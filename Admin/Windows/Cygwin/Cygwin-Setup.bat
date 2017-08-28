@echo off

"%CD%\contrib\cygwin\isabelle\cygwin" --site http://isabelle.in.tum.de/cygwin_2017 --no-verify --only-site --local-package-dir "%TEMP%" --root "%CD%\contrib\cygwin"
