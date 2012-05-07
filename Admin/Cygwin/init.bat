@echo off

cd "%~dp0"
cd "..\.."

"contrib\cygwin-1.7.9\bin\ash" /bin/rebaseall
"contrib\cygwin-1.7.9\bin\bash" -c "PATH=/bin; chmod -wx $(find heaps -type f); mkpasswd -l >/etc/passwd; mkgroup -l >/etc/group"
