#
# $Id$
# Author: Markus Wenzel, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# fixgoal.pl - replace goal(w) commands by implicit versions Goal(w)
#

sub fixgoal {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    ($path, $thy, $ext) = ($file =~ m,^(.*/)?(\w+)(\.\w+)?$,);

    $_ = $text;

    s/^[ \t]*goalw\b\s*\bthy\b/Goalw/mg;
    s/^[ \t]*goalw\b\s*\b$thy\.thy\b/Goalw/mg;
    s/^[ \t]*goal\b\s*\bthy\b/Goal/mg;
    s/^[ \t]*goal\b\s*\b$thy\.thy\b/Goal/mg;


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
  eval { &fixgoal($file); };
  if ($@) { print STDERR "*** fixgoal $file: ", $@, "\n"; }
}
