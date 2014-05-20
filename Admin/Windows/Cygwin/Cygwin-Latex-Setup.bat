@echo off

"%CD%\contrib\cygwin\isabelle\cygwin" --site http://isabelle.in.tum.de/cygwin_2014 --no-verify --only-site --local-package-dir "%TEMP%" --root "%CD%\contrib\cygwin" --packages texlive-collection-latexextra,texlive-collection-fontutils,texlive-collection-mathextra,libsasl2 --quiet-mode

