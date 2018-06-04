@echo off

"%CD%\contrib\cygwin\isabelle\cygwin" --site {MIRROR} --no-verify --only-site --local-package-dir "%TEMP%" --root "%CD%\contrib\cygwin"
