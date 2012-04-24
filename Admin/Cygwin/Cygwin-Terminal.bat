@echo off

set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%CD%\bin;%PATH%
set CHERE_INVOKING=true

echo This is the GNU Bash interpreter of Cygwin.
echo Use command "isabelle" to invoke Isabelle tools.
"%CD%\contrib\cygwin-1.7.9\bin\bash" --login -i
