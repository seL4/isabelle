#
# $Id$
# Author: Markus Wenzel, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# unsymbolize.pl - remove unreadable symbol names from sources
#

sub unsymbolize {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    # Pure
    s/\\?\\<And>/!!/g;
    s/\\?\\<Colon>/::/g;
    s/\\?\\<Longrightarrow>/==>/g;
    s/\\?\\<Midarrow>\\?\\<Rightarrow>/==>/g;
    s/\\?\\<Rightarrow>/=>/g;
    s/\\?\\<equiv>/==/g;
    s/\\?\\<dots>/.../g;
    s/\\?\\<lbrakk> ?/[| /g;
    s/\\?\\ ?<rbrakk>/ |]/g;
    s/\\?\\<lparr> ?/(| /g;
    s/\\?\\ ?<rparr>/ |)/g;
    # HOL
    s/\\?\\<longleftrightarrow>/<->/g;
    s/\\?\\<longrightarrow>/-->/g;
    s/\\?\\<midarrow>\\?\\<rightarrow>/-->/g;
    s/\\?\\<rightarrow>/->/g;
    s/\\?\\<not>/~/g;
    s/\\?\\<epsilon> ?/SOME /g;
    # outer syntax
    s/\\?\\<rightleftharpoons>/==/g;
    s/\\?\\<rightharpoonup>/=>/g;
    s/\\?\\<leftharpoondown>/<=/g;

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
  eval { &unsymbolize($file); };
  if ($@) { print STDERR "*** unsymbolize $file: ", $@, "\n"; }
}
