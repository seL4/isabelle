#
# $Id$
#
# fixnumerals.pl - fix occurences of numerals in HOL/ZF terms
#
# tries to be smart; may produce garbage if nested comments and
# solitary quotes (") are intermixed badly;
#

sub fixdots {
    my ($constr, $file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;


    $result = "";
    $rest = $text;

    while (1) {
	$_ = $rest;
	($pre, $str, $rest) =
	    m/^((?: \(\*.*?\*\) | [^"] )*)      # pre: text or (non-nested!) comments
            "((?: [^"\\] | \\\S | \\\s+\\ )*)"  # quoted string
            (.*)$/sx;                           # rest of file
	if ($str) {
	    $_ = $str;
	    if (!m/^[a-zA-Z0-9_\/\.]*$/s && !m/\.ML/s && !m/\.thy/s) {   # exclude filenames!
		if ($constr eq "true") {
		    s/#([0-9]+)/($1::int)/sg;
		    s/#-([0-9]+)/(~$1::int)/sg;
		} else {
		    s/#([0-9]+)/$1/sg;
		    s/#-([0-9]+)/~$1/sg;
		}
	    }
            $result = $result . $pre . '"' . $_ . '"';
        } else {
 	    $result = $result . $_;
    	    last;
	}
    }

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

$constr = shift;

foreach $file (@ARGV) {
  eval { &fixdots($constr, $file); };
  if ($@) { print STDERR "*** fixdots $file: ", $@, "\n"; }
}
