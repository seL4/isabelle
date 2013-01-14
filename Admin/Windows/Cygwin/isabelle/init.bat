@echo off

cd "%~dp0"
cd ".."

set CYGWIN=nodosfilewarning

echo Initializing Cygwin ...
"bin\dash" /isabelle/rebaseall
"bin\bash" /isabelle/postinstall

