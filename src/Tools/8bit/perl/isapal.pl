#!/usr/local/dist/bin/perl
'di';
'ig00';
#
# $Header$
#
# $Log$
# Revision 1.2  1997/03/17 11:25:52  wenzelm
# fixed perl path;
#
# Revision 1.1.1.1  1996/06/25  15:44:59  oheimb
# Graphical 8bit Font Packet, see isabelle/Tools/8bit/doc/manual.dvi
# Author: Franz Regensburger; improvements by David von Oheimb
#
# Revision 1.1.1.1  1996/06/25  13:58:23  oheimb
# Graphical 8bit Font Package imported, second attempt
#
#
# isapal.pl
# Franz Regensburger <regensbu@informatik.tu-muenchen.de>
# 21.3.95
#
# last changed: 
#
# print the file palette.isa
#
# needs an 8bit terminal for output

$pack=$ENV{'ISABELLE8BIT'};
$filename = "$pack/doc/palette.isa";

open(INFILE,$filename) || die "can't open $filename: $!\n";

while (<INFILE>){ print;}

close(INFILE);
exit(0);

###############################################################

    # These next few lines are legal in both Perl and nroff.

.00;                       # finish .ig
 
'di           \" finish diversion--previous line must be blank
.nr nl 0-1    \" fake up transition to first page again
.nr % 0         \" start at page 1
'; __END__ ##### From here on it's a standard manual page #####
