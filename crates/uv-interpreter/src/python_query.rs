//! Find a user requested python version/interpreter.

use std::env;
use std::path::PathBuf;

use once_cell::sync::Lazy;
use regex::Regex;
use tracing::instrument;

use platform_host::Platform;
use uv_cache::Cache;

use crate::python_query::windows::PythonVersionSelector;
use crate::{Error, Interpreter};

/// ```text
/// -V:3.12          C:\Users\Ferris\AppData\Local\Programs\Python\Python312\python.exe
/// -V:3.8           C:\Users\Ferris\AppData\Local\Programs\Python\Python38\python.exe
/// ```
static PY_LIST_PATHS: Lazy<Regex> = Lazy::new(|| {
    // Without the `R` flag, paths have trailing \r
    Regex::new(r"(?mR)^ -(?:V:)?(\d).(\d+)-?(?:arm)?(?:\d*)\s*\*?\s*(.*)$").unwrap()
});

/// Find a python version/interpreter of a specific version.
///
/// Supported formats:
/// * `-p 3.10` searches for an installed Python 3.10 (`py --list-paths` on Windows, `python3.10` on
///   Linux/Mac). Specifying a patch version is not supported.
/// * `-p python3.10` or `-p python.exe` looks for a binary in `PATH`.
/// * `-p /home/ferris/.local/bin/python3.10` uses this exact Python.
///
/// When the user passes a patch version (e.g. 3.12.1), we currently search for a matching minor
/// version (e.g. `python3.12` on unix) and error when the version mismatches, as a binary with the
/// patch version (e.g. `python3.12.1`) is often not in `PATH` and we make the simplifying
/// assumption that the user has only this one patch version installed.
#[instrument]
pub fn find_requested_python(
    request: &str,
    platform: &Platform,
    cache: &Cache,
) -> Result<Option<Interpreter>, Error> {
    let versions = request
        .splitn(3, '.')
        .map(str::parse::<u8>)
        .collect::<Result<Vec<_>, _>>();
    if let Ok(versions) = versions {
        // `-p 3.10` or `-p 3.10.1`
        if cfg!(unix) {
            if let [_major, _minor, requested_patch] = versions.as_slice() {
                let formatted = PathBuf::from(format!("python{}.{}", versions[0], versions[1]));
                let Some(executable) = Interpreter::find_executable(&formatted)? else {
                    return Ok(None);
                };
                let interpreter = Interpreter::query(&executable, platform, cache)?;
                if interpreter.python_patch() != *requested_patch {
                    return Err(Error::PatchVersionMismatch(
                        executable,
                        request.to_string(),
                        interpreter.python_version().clone(),
                    ));
                }
                Ok(Some(interpreter))
            } else {
                let formatted = PathBuf::from(format!("python{request}"));
                let Some(executable) = Interpreter::find_executable(&formatted)? else {
                    return Ok(None);
                };
                Ok(Some(Interpreter::query(&executable, platform, cache)?))
            }
        } else if cfg!(windows) {
            match versions.as_slice() {
                [requested_major] => windows::find_python(
                    PythonVersionSelector::Major(*requested_major),
                    platform,
                    cache,
                ),
                [major, minor] => windows::find_python(
                    PythonVersionSelector::MajorMinor(*major, *minor),
                    platform,
                    cache,
                ),
                [major, minor, requested_patch] => {
                    if let Some(interpreter) = windows::find_python(
                        PythonVersionSelector::MajorMinorPatch(*major, *minor, *requested_patch),
                        platform,
                        cache,
                    )? {
                        if interpreter.python_patch() != *requested_patch {
                            return Err(Error::PatchVersionMismatch(
                                interpreter.sys_executable().to_path_buf(),
                                request.to_string(),
                                interpreter.python_version().clone(),
                            ));
                        }

                        Ok(Some(interpreter))
                    } else {
                        Ok(None)
                    }
                }
                // SAFETY: Guaranteed by the Ok(versions) guard
                _ => unreachable!(),
            }
        } else {
            unimplemented!("Only Windows and Unix are supported")
        }
    } else if !request.contains(std::path::MAIN_SEPARATOR) {
        // `-p python3.10`; Generally not used on windows because all Python are `python.exe`.
        let Some(executable) = Interpreter::find_executable(request)? else {
            return Ok(None);
        };
        Ok(Some(Interpreter::query(&executable, platform, cache)?))
    } else {
        // `-p /home/ferris/.local/bin/python3.10`
        let executable = fs_err::canonicalize(request)?;
        Ok(Some(Interpreter::query(&executable, platform, cache)?))
    }
}

/// Pick a sensible default for the python a user wants when they didn't specify a version.
///
/// We prefer the test overwrite `UV_TEST_PYTHON_PATH` if it is set, otherwise `python3`/`python` or
/// `python.exe` respectively.
#[instrument]
pub fn find_default_python(platform: &Platform, cache: &Cache) -> Result<Interpreter, Error> {
    let python = if cfg!(unix) {
        if let Some(test_path) = env::var_os("UV_TEST_PYTHON_PATH") {
            which::which_in_global("python3", Some(&test_path))
                .and_then(|mut iter| iter.next().ok_or(which::Error::CannotFindBinaryPath))
        } else {
            which::which("python3").or_else(|_| which::which("python"))
        }
        .map_err(|_| Error::NoPythonInstalledUnix)?
    } else if cfg!(windows) {
        return windows::find_python(PythonVersionSelector::Default, platform, cache)?
            .ok_or(Error::NoPythonInstalledWindows);
    } else {
        unimplemented!("Only Windows and Unix are supported")
    };
    let base_python = fs_err::canonicalize(python)?;
    let interpreter = Interpreter::query(&base_python, platform, cache)?;
    return Ok(interpreter);
}

mod windows {
    use std::env;
    use std::iter::FusedIterator;
    use std::path::PathBuf;
    use std::process::{Command, ExitStatus};

    use tracing::info_span;

    use platform_host::Platform;
    use uv_cache::Cache;

    use crate::python_query::PY_LIST_PATHS;
    use crate::{Error, Interpreter};

    pub(super) fn find_python(
        selector: PythonVersionSelector,
        platform: &Platform,
        cache: &Cache,
    ) -> Result<Option<Interpreter>, Error> {
        match find_python_installation(selector, platform, cache) {
            Ok(Some(installation)) => Ok(Some(installation.into_interpreter(platform, cache)?)),
            Ok(None) => Ok(None),
            Err(err) => Err(err),
        }
    }

    fn find_python_installation(
        selector: PythonVersionSelector,
        platform: &Platform,
        cache: &Cache,
    ) -> Result<Option<PythonInstallation>, Error> {
        // If `UV_TEST_PYTHON_PATH` is set, only search for python installations in the given PATHs.
        if let Some(python_overwrite) = env::var_os("UV_TEST_PYTHON_PATH") {
            for path in which::which_in_global("python.exe", Some(&python_overwrite))
                .map_err(|_| Error::NoPythonInstalledWindows)?
            {
                let installation =
                    PythonInstallation::Interpreter(Interpreter::query(&path, platform, cache)?);

                if selector.is_selected(&installation) {
                    return Ok(Some(installation));
                }
            }

            return Ok(None);
        }

        // Use `py` to find the python installation on the system.
        match py_list_paths(selector) {
            Ok(Some(installation)) => return Ok(Some(installation)),
            Ok(None) => {}
            Err(PyListError::NotFound(error)) => {
                tracing::warn!("`py` is not installed or can't be executed: {error}. Falling back to searching Python on the path");
            }
            Err(err) => return Err(err.into()),
        }

        for path in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
            for name in selector.possible_names() {
                if let Ok(paths) = which::which_in_global(&*name, Some(&path)) {
                    for path in paths {
                        // TODO filter out the windows python stub.
                        let installation = PythonInstallation::Interpreter(Interpreter::query(
                            &path, platform, cache,
                        )?);

                        if selector.is_selected(&installation) {
                            return Ok(Some(installation));
                        }
                    }
                }
            }
        }

        Ok(None)
    }

    /// Run `py --list-paths` to find the installed pythons.
    ///
    /// The command takes 8ms on my machine.
    /// TODO(konstin): Implement <https://peps.python.org/pep-0514/> to read python installations from the registry instead.
    fn py_list_paths(
        selector: PythonVersionSelector,
    ) -> Result<Option<PythonInstallation>, PyListError> {
        let output = info_span!("py_list_paths")
            .in_scope(|| Command::new("py").arg("--list-paths").output())
            .map_err(PyListError::NotFound)?;

        // There shouldn't be any output on stderr.
        if !output.status.success() || !output.stderr.is_empty() {
            return Err(PyListError::CommandFailed {
                status: output.status,
                stdout: output.stdout,
                stderr: output.stderr,
            });
        }

        // Find the first python of the version we want in the list
        let stdout = String::from_utf8(output.stdout).map_err(|err| PyListError::NotUtf8 {
            error: err,
            stderr: output.stderr,
        })?;
        let installation = PY_LIST_PATHS.captures_iter(&stdout).find_map(|captures| {
            let (_, [major, minor, path]) = captures.extract();

            let installation = PythonInstallation::PyListPath {
                major: major.parse::<u8>().ok()?,
                minor: minor.parse::<u8>().ok()?,
                executable_path: PathBuf::from(path),
            };

            selector.is_selected(&installation).then_some(installation)
        });

        Ok(installation)
    }

    #[derive(Debug)]
    enum PyListError {
        NotFound(std::io::Error),
        CommandFailed {
            status: ExitStatus,
            stdout: Vec<u8>,
            stderr: Vec<u8>,
        },
        NotUtf8 {
            error: std::string::FromUtf8Error,
            stderr: Vec<u8>,
        },
    }

    impl From<PyListError> for Error {
        fn from(value: PyListError) -> Self {
            match value {
                PyListError::NotFound(error) => Error::PyList(error),
                PyListError::CommandFailed {
                    status,
                    stdout,
                    stderr,
                } => Error::PythonSubcommandOutput {
                    message: format!("Running `py --list-paths` failed with status {status}"),
                    stdout: String::from_utf8_lossy(&stdout).trim().to_string(),
                    stderr: String::from_utf8_lossy(&stderr).trim().to_string(),
                },
                PyListError::NotUtf8 { error, stderr } => Error::PythonSubcommandOutput {
                    message: format!(
                        "The stdout of `py --list-paths` isn't UTF-8 encoded: {error}"
                    ),
                    stdout: String::from_utf8_lossy(error.as_bytes()).trim().to_string(),
                    stderr: String::from_utf8_lossy(&stderr).trim().to_string(),
                },
            }
        }
    }

    #[derive(Debug, Clone)]
    pub(super) enum PythonInstallation {
        PyListPath {
            major: u8,
            minor: u8,
            executable_path: PathBuf,
        },
        Interpreter(Interpreter),
    }

    impl PythonInstallation {
        pub(super) fn major(&self) -> u8 {
            match self {
                PythonInstallation::PyListPath { major, .. } => *major,
                PythonInstallation::Interpreter(interpreter) => interpreter.python_major(),
            }
        }

        pub(super) fn minor(&self) -> u8 {
            match self {
                PythonInstallation::PyListPath { minor, .. } => *minor,
                PythonInstallation::Interpreter(interpreter) => interpreter.python_minor(),
            }
        }

        pub(super) fn patch(&self) -> Option<u8> {
            match self {
                PythonInstallation::PyListPath { .. } => None,
                PythonInstallation::Interpreter(interpreter) => Some(interpreter.python_patch()),
            }
        }

        #[inline]
        pub(super) fn matches(&self, major: u8, minor: Option<u8>) -> bool {
            self.major() == major && minor.map_or(true, |minor| self.minor() == minor)
        }

        pub(super) fn into_interpreter(
            self,
            platform: &Platform,
            cache: &Cache,
        ) -> Result<Interpreter, Error> {
            match self {
                PythonInstallation::PyListPath {
                    executable_path, ..
                } => Interpreter::query(&executable_path, platform, cache),
                PythonInstallation::Interpreter(interpreter) => Ok(interpreter),
            }
        }
    }

    #[derive(Copy, Clone, Debug)]
    pub(super) enum PythonVersionSelector {
        Default,
        Major(u8),
        MajorMinor(u8, u8),
        MajorMinorPatch(u8, u8, u8),
    }

    impl PythonVersionSelector {
        fn is_selected(self, installation: &PythonInstallation) -> bool {
            match self {
                PythonVersionSelector::Default => true,
                PythonVersionSelector::Major(major) => installation.matches(major, None),
                PythonVersionSelector::MajorMinor(major, minor) => {
                    installation.matches(major, Some(minor))
                }
                PythonVersionSelector::MajorMinorPatch(major, minor, requested_patch) => {
                    installation.matches(major, Some(minor))
                        // Exclude the versions that we already know aren't matching but continue searching
                        // in case we find a matching version later.
                        && !installation
                        .patch()
                        .is_some_and(|patch| patch != requested_patch)
                }
            }
        }

        fn possible_names(self) -> PossibleNamesIter {
            match self {
                PythonVersionSelector::Default => PossibleNamesIter::Default,
                PythonVersionSelector::Major(major) => PossibleNamesIter::Major(major),
                PythonVersionSelector::MajorMinor(major, minor) => {
                    PossibleNamesIter::MajorMinor(major, minor)
                }
                PythonVersionSelector::MajorMinorPatch(major, minor, patch) => {
                    PossibleNamesIter::MajorMinorPatch(major, minor, patch)
                }
            }
        }
    }

    #[derive(Clone, Debug)]
    enum PossibleNamesIter {
        MajorMinorPatch(u8, u8, u8),
        MajorMinor(u8, u8),
        Major(u8),
        Default,
        Done,
    }

    impl Iterator for PossibleNamesIter {
        type Item = std::borrow::Cow<'static, str>;

        fn next(&mut self) -> Option<Self::Item> {
            Some(match *self {
                PossibleNamesIter::MajorMinorPatch(major, minor, patch) => {
                    *self = Self::MajorMinor(major, minor);
                    std::borrow::Cow::Owned(format!("python{major}.{minor}.{patch}"))
                }
                PossibleNamesIter::MajorMinor(major, minor) => {
                    *self = Self::Major(major);
                    std::borrow::Cow::Owned(format!("python{major}.{minor}"))
                }
                PossibleNamesIter::Major(major) => {
                    *self = Self::Default;
                    std::borrow::Cow::Owned(format!("python{major}"))
                }
                PossibleNamesIter::Default => {
                    *self = Self::Done;
                    std::borrow::Cow::Borrowed("python")
                }
                PossibleNamesIter::Done => return None,
            })
        }
    }

    impl FusedIterator for PossibleNamesIter {}

    #[cfg(test)]
    #[cfg(windows)]
    mod tests {
        use std::fmt::Debug;

        use insta::assert_display_snapshot;
        use itertools::Itertools;

        use platform_host::Platform;
        use uv_cache::Cache;

        use crate::{find_requested_python, Error};

        fn format_err<T: Debug>(err: Result<T, Error>) -> String {
            anyhow::Error::new(err.unwrap_err())
                .chain()
                .join("\n  Caused by: ")
        }

        #[test]
        fn no_such_python_path() {
            let result = find_requested_python(
                r"C:\does\not\exists\python3.12",
                &Platform::current().unwrap(),
                &Cache::temp().unwrap(),
            );
            insta::with_settings!({
                filters => vec![
                    // The exact message is host language dependent
                    (r"Caused by: .* \(os error 3\)", "Caused by: The system cannot find the path specified. (os error 3)")
                ]
            }, {
                assert_display_snapshot!(
                    format_err(result), @r###"
        failed to canonicalize path `C:\does\not\exists\python3.12`
          Caused by: The system cannot find the path specified. (os error 3)
        "###);
            });
        }
    }
}

#[cfg(unix)]
#[cfg(test)]
mod tests {
    use insta::assert_display_snapshot;
    #[cfg(unix)]
    use insta::assert_snapshot;
    use itertools::Itertools;
    use platform_host::Platform;
    use uv_cache::Cache;

    use crate::python_query::find_requested_python;
    use crate::Error;

    fn format_err<T: Debug>(err: Result<T, Error>) -> String {
        anyhow::Error::new(err.unwrap_err())
            .chain()
            .join("\n  Caused by: ")
    }

    #[test]
    fn no_such_python_version() {
        let request = "3.1000";
        let result = find_requested_python(
            request,
            &Platform::current().unwrap(),
            &Cache::temp().unwrap(),
        )
        .unwrap()
        .ok_or(Error::NoSuchPython(request.to_string()));
        assert_snapshot!(
            format_err(result),
            @"No Python 3.1000 In `PATH`. Is Python 3.1000 installed?"
        );
    }

    #[test]
    fn no_such_python_binary() {
        let request = "python3.1000";
        let result = find_requested_python(
            request,
            &Platform::current().unwrap(),
            &Cache::temp().unwrap(),
        )
        .unwrap()
        .ok_or(Error::NoSuchPython(request.to_string()));
        assert_display_snapshot!(
            format_err(result),
            @"No Python python3.1000 In `PATH`. Is Python python3.1000 installed?"
        );
    }

    #[test]
    fn no_such_python_path() {
        let result = find_requested_python(
            "/does/not/exists/python3.12",
            &Platform::current().unwrap(),
            &Cache::temp().unwrap(),
        );
        assert_display_snapshot!(
            format_err(result), @r###"
        failed to canonicalize path `/does/not/exists/python3.12`
          Caused by: No such file or directory (os error 2)
        "###);
    }
}
