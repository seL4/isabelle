@echo off

cd "%~dp0"
cd "..\..\.."

set CYGWIN=nodosfilewarning

echo Initializing Cygwin ...
"contrib\cygwin\bin\dash" /isabelle/rebaseall
"contrib\cygwin\bin\bash" /isabelle/postinstall

