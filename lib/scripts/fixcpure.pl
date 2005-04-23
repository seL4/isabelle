#
# $Id$
# Author: Makarius
#
# fixcpure.pl - adapt theories and ML files to new CPure/Pure arrangement
#

sub fixcpure {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    s/\bCPure\.thy\b/-THE-CPURE-THEORY-/sg;
    s/\bCPure\.([A-Za-z_\-])/Pure.$1/sg;
    s/-THE-CPURE-THEORY-/CPure.thy/sg;

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
  eval { &fixcpure($file); };
  if ($@) { print STDERR "*** fixcpure $file: ", $@, "\n"; }
}
