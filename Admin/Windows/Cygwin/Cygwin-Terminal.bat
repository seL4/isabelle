@echo off

set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%CD%\bin;%PATH%
set LANG=en_US.UTF-8
set CHERE_INVOKING=true

if exist "%CD%\contrib\cygwin\isabelle\uninitialized" (
  echo Initializing Cygwin ...
  "%CD%\contrib\{JDK_COMPONENT}\x86_64-windows\bin\java" -jar "%CD%\contrib\{SETUP_COMPONENT}\lib\isabelle_setup.jar" cygwin_init "%CD%" "%CD%\contrib\cygwin"
)
echo This is the GNU Bash interpreter of Cygwin.
echo Use command "isabelle" to invoke Isabelle tools.
"%CD%\contrib\cygwin\bin\bash" --login -i
