@echo off

set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%CD%\bin;%PATH%
set LANG=en_US.UTF-8
set CHERE_INVOKING=true

echo This is the GNU Bash interpreter of Cygwin.
echo Use command "isabelle" to invoke Isabelle tools.
"%CD%\contrib\{JDK_COMPONENT}\x86_64-windows\bin\java" -jar "%CD%\contrib\{SETUP_COMPONENT}\lib\isabelle_setup.jar" cygwin_init "%CD%" "%CD%\contrib\cygwin"
"%CD%\contrib\cygwin\bin\bash" --login -i
