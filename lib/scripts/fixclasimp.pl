#
# $Id$
#
# fixclasimp.pl - fix references to implicit claset and simpset
#

sub fixclasimp {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    s/set_current_thy\s"([^"]*)"/context $1.thy/sg;

    s/!\s*simpset/simpset()/sg;
    s/simpset\s*:=/simpset_ref() :=/sg;
    s/simpset_of\s*"([^"]*)"/simpset_of $1.thy/sg;

    s/!\s*claset/claset()/sg;
    s/claset\s*:=/claset_ref() :=/sg;
    s/claset_of\s*"([^"]*)"/claset_of $1.thy/sg;


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
  eval { &fixclasimp($file); };
  if ($@) { print STDERR "*** fixclasimp $file: ", $@, "\n"; }
}
