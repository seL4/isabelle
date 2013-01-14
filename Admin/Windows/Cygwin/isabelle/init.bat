@echo off

cd "%~dp0"
cd ".."

set CYGWIN=nodosfilewarning

echo Initializing Cygwin ...
"bin\dash" /isabelle/rebaseall polyml-5.5.0
"bin\bash" /isabelle/postinstall

