#
# $Id$
# Author: Sebastian Skalberg, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# fixgreek.pl - fix problems with greek and other foreign letters now
#               being classified as letters instead of symbols.
#

sub fixgreek {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    s/(\\<(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z)>)([a-zA-Z0-9])/$1 $3/sg;

    s/([a-zA-Z][a-zA-Z0-9]*)(\\<(a|b|c|d|e|f|g|h|i|j|k|l|m|n|o|p|q|r|s|t|u|v|w|x|y|z|A|B|C|D|E|F|G|H|I|J|K|L|M|N|O|P|Q|R|S|T|U|V|W|X|Y|Z)>)/$1 $2/sg;

    s/(\\<(aa|bb|cc|dd|ee|ff|gg|hh|ii|jj|kk|ll|mm|nn|oo|pp|qq|rr|ss|tt|uu|vv|ww|xx|yy|zz|AA|BB|CC|DD|EE|FF|GG|HH|II|JJ|KK|LL|MM|NN|OO|PP|QQ|RR|SS|TT|UU|VV|WW|XX|YY|ZZ)>)([a-zA-Z0-9])/$1 $3/sg;

    s/([a-zA-Z][a-zA-Z0-9]*)(\\<(aa|bb|cc|dd|ee|ff|gg|hh|ii|jj|kk|ll|mm|nn|oo|pp|qq|rr|ss|tt|uu|vv|ww|xx|yy|zz|AA|BB|CC|DD|EE|FF|GG|HH|II|JJ|KK|LL|MM|NN|OO|PP|QQ|RR|SS|TT|UU|VV|WW|XX|YY|ZZ)>)/$1 $2/sg;

    s/(\\<(alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Upsilon|Phi|Psi|Omega)>)([a-zA-Z0-9])/$1 $3/sg;

    s/([a-zA-Z][a-zA-Z0-9]*)(\\<(alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Upsilon|Phi|Psi|Omega)>)/$1 $2/sg;

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
  eval { &fixgreek($file); };
  if ($@) { print STDERR "*** fixgreek $file: ", $@, "\n"; }
}
