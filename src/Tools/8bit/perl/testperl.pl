# this is a test file for perl
'di';
'ig00';
#
# $Header$
#
# $Log$
# Revision 1.1  1996/06/25 15:44:59  oheimb
# Initial revision
#
# Revision 1.1.1.1  1996/06/25  13:58:23  oheimb
# Graphical 8bit Font Package imported, second attempt
#
#
# correct output (without leading #)
#
#This is a Test of backslash expansion:  \today and \\ and \'
#000000
#
#This is a Test of backslash expansion:  \today and \ and '
#000000
#
#

print <<'End';
This is a Test of backslash expansion:  \today and \\ and \'
End
print "000000\n";


print '
This is a Test of backslash expansion:  \today and \\ and \'
';
print "000000\n";
###############################################################

    # These next few lines are legal in both Perl and nroff.

.00;                       # finish .ig
 
'di           \" finish diversion--previous line must be blank
.nr nl 0-1    \" fake up transition to first page again
.nr % 0         \" start at page 1
'; __END__ ##### From here on it's a standard manual page #####

.TH TESTPERL 1 "March 30, 1995"
.AT 3
.SH NAME
testperl \- whatever
.SH SYNOPSIS
.B testperl [options] [files]
.SH DESCRIPTION
.I Testperl
does whatever.
.SH ENVIRONMENT
No environment variables are used.
.SH FILES
None.
.SH AUTHOR
Franz Regensburger
.SH "SEE ALSO"

.SH DIAGNOSTICS

.SH BUGS

