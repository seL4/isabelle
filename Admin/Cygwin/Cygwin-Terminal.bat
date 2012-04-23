@echo off

set HOME=%HOMEDRIVE%%HOMEPATH%
set PATH=%CD%\bin;%PATH%
"%CD%\contrib\cygwin-1.7.9\bin\bash" --login -i
