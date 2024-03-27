@echo off

set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%CD%\bin;%PATH%
set LANG=en_US.UTF-8
set CHERE_INVOKING=true

echo This is the GNU Bash interpreter of Cygwin.
echo Use command "isabelle" to invoke Isabelle tools.
"%CD%\contrib\cygwin\bin\bash" --login -i
