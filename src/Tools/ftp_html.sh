#!/bin/csh
# Executed from the main Isabelle directory, this script transfers all
# files needed for the HTML version of Isabelle's theories to the FTP
# server. It deletes old files and makes directories by executing the
# commands stored in ftp_mkdirs.txt.
#
# Provide password as first argument or enter it manually at the prompt.

echo >ftp_commands.tmp
foreach f (*/*.thy */*/*.thy */*/*/*.thy)
  if ( -f $f:r.html ) then
    echo put $f:r.html >>ftp_commands.tmp
    echo put $f:r_sub.html >>ftp_commands.tmp
    echo put $f:r_sup.html >>ftp_commands.tmp
    if ( -f $f:r.ML ) then
      echo put $f:r.ML >>ftp_commands.tmp
    endif
  endif
end

( \
 echo user nipkow $1; \
 echo cd isabelle; \
 echo bin; \
 echo "mput logics.html Tools/*_arrow.gif */00-chart.html;" \
 echo "mdel */*.ML */*.html */*/*.ML */*/*.html */*/*/*.ML */*/*/*.html"; \
 cat Tools/ftp_mkdirs.txt \
 cat ftp_commands.tmp \
) | ftp -inv ftp.informatik.tu-muenchen.de

rm ftp_commands.tmp
