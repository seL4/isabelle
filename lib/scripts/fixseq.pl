#
# $Id$
# Author: Markus Wenzel, TU Muenchen
#
# fixseq.pl - fix references to obsolete Pure/Sequence structure
#

sub fixseq {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;


    s/Sequence\.tl/Seq.tl/sg;
    s/Sequence\.single/Seq.single/sg;
    s/Sequence\.seqof/Seq.make/sg;
    s/Sequence\.seq/Seq.seq/sg;
    s/Sequence\.s_of_list/Seq.of_list/sg;
    s/Sequence\.pull/Seq.pull/sg;
    s/Sequence\.prints/Seq.print/sg;
    s/Sequence\.null/Seq.empty/sg;
    s/Sequence\.maps/Seq.map/sg;
    s/Sequence\.mapp/Seq.mapp/sg;
    s/Sequence\.list_of_s/Seq.list_of/sg;
    s/Sequence\.its_right/Seq.it_right/sg;
    s/Sequence\.interleave/Seq.interleave/sg;
    s/Sequence\.hd/Seq.hd/sg;
    s/Sequence\.flats/Seq.flat/sg;
    s/Sequence\.filters/Seq.filter/sg;
    s/Sequence\.cons/Seq.cons/sg;
    s/Sequence\.chop/Seq.chop/sg;
    s/Sequence\.append/Seq.append/sg;


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
  eval { &fixseq($file); };
  if ($@) { print STDERR "*** fixseq $file: ", $@, "\n"; }
}
