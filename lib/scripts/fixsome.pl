#
# $Id$
# Author: Markus Wenzel, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# fixsome.pl - fix theorem names related to SOME (Eps) in HOL
#

sub fixsome {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    s/select_equality/some_equality/g;
    s/select_eq_Ex/some_eq_ex/g;
    s/selectI2EX/someI2_ex/g;
    s/selectI2/someI2/g;
    s/selectI/someI/g;
    s/select1_equality/some1_equality/g;
    s/Eps_sym_eq/some_sym_eq_trivial/g;
    s/Eps_eq/some_eq_trivial/g;

    $result = $_;

    if ($text ne $result) {
	print STDERR "fixing $file\n";
        if (! -f "$file~~") {
	    rename $file, "$file~~" || die $!;
        }
	open (FILE, "> $file") || die $!;
	print FILE $result;
	close FILE || die $!;
    }
}


## main

foreach $file (@ARGV) {
  eval { &fixsome($file); };
  if ($@) { print STDERR "*** fixsome $file: ", $@, "\n"; }
}
