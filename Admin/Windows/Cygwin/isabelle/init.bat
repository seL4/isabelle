@echo off

cd "%~dp0"
cd "..\.."

set CYGWIN=nodosfilewarning

echo Initializing Cygwin ...
"cygwin\bin\dash" /isabelle/rebaseall contrib/polyml-5.5.0
"cygwin\bin\bash" /isabelle/postinstall

