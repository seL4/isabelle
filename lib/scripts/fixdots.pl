#
# $Id$
#
# fixdots.pl - ensure that dots in formulas are followed by non-idents
#

foreach $file (@ARGV) {

    if (open (FILE, $file)) {
	undef $/;
	$text = <FILE>;
	close FILE;

	$result = "";
	$rest = $text;

	while (1) {
	    $_ = $rest;
	    ($pre, $str, $rest) = m/^([^"]*)"((?:[^"\\]|\\.)*)"(.*)$/s;
	    if ($str) {
		$_ = $str;
		if (!m/^[a-zA-Z0-9_\/\.]*$/s && !m/\.ML$/s && !m/\.thy/) {     # Exclude filenames!
		    s/([a-zA-Z][a-zA-Z0-9_']*)\.([a-zA-Z])/$1\. $2/g;
	        }
                $result = $result . $pre . '"' . $_ . '"';
            } else {
 	        $result = $result . $_;
    	        last;
	    }
        }

        if ($text ne $result) {
	    print STDERR "fixing $file\n";
	    open (FILE, "> $file") || die $!;
	    print FILE $result;
	    close FILE || die $!;
        }

    } else {
        print STDERR "Can't open file $file: $!\n";
    }
}
