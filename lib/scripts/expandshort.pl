#
# $Id$
#
# expandshort.pl - expand shorthand goal commands
#

sub expandshort {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    s/\bsafe_tac *\(claset *\( *\) *\)/Safe_tac/sg;
    s/ *\(Safe_tac\) *([0-9]+)/ Safe_tac \1/sg;
    s/ *\(Safe_tac\)/ Safe_tac/sg;
    s/\bby\(/by (/sg;
    s/\bba\b *(\d+);/by (assume_tac \1);/sg;
    s/\bbr\b *([^;]*) (\d+);/by (rtac \1 \2);/sg;
    s/\bbrs\b *([^;]*) (\d+);/by (resolve_tac \1 \2);/sg;
    s/\bbd\b *([^;]*) (\d+);/by (dtac \1 \2);/sg;
    s/\bbds\b *([^;]*) (\d+);/by (dresolve_tac \1 \2);/sg;
    s/\bbe\b *([^;]*) (\d+);/by (etac \1 \2);/sg;
    s/\bbes\b *([^;]*) (\d+);/by (eresolve_tac \1 \2);/sg;
    s/\bbw\b *([^;]*);/by (rewtac \1);/sg;
    s/\bbws\b *([^;]*);/by (rewrite_goals_tac \1);/sg;
    s/\bauto *\(\)/by (Auto_tac())/sg;
    s/dresolve_tac *\[(\w+)\] */dtac \1 /sg;
    s/eresolve_tac *\[(\w+)\] */etac \1 /sg;
    s/resolve_tac *\[(\w+)\] */rtac \1 /sg;
    s/rewrite_goals_tac *\[(\w+)\]( *)/rewtac \1\2/sg;
    s/rtac *\((\w+)\s+RS\s+ssubst\)\s+/stac \1 /sg;

    $result = $_;

    if ($text ne $result) {
	print STDERR "expanding $file\n";
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
  eval { &expandshort($file); };
  if ($@) { print STDERR "*** expandshort $file: ", $@, "\n"; }
}
