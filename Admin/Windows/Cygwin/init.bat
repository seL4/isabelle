@echo off

cd "%~dp0"
cd "..\.."

set CYGWIN=nodosfilewarning

echo Initializing Cygwin ...
"cygwin\bin\ash" /bin/rebaseall -p
"cygwin\bin\bash" -c "PATH=/bin; bash -c 'source /etc/postinstall/base-files-mketc.sh.done'; mkpasswd -l >/etc/passwd; mkgroup -l >/etc/group"
