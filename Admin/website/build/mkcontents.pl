#!/usr/bin/perl

# mkcontents.pl
#
#   $Id$
#
#   simple script to create a html version of the Contents file in the
#   Isabelle documentation directory.
#
#   Nov/14/1999 Version 1.0  -  Gerwin Klein <kleing@in.tum.de>
#
#   command line:
#   mkcontent.pl [-p <url-path-prefix>] <Content-file> <output-file>
#


use Getopt::Long ;

$opt_p="";
$result = GetOptions ("p=s");

$path=$opt_p;

$infile  = $ARGV[0];
$outfile = $ARGV[1];

$listHeader = "<ul>\n";
$lineHeader = "  <li>";
$lineEnd    = "</li>\n";
$listFooter = "</ul>\n";

$topicStart = "<h3>";
$topicEnd   = "</h3>\n";

open(IN, "<$infile") || die "cannot read input file <$infile>";
open(OUT, ">$outfile") || die "cannot write output file <$outfile>";

$first = 1;

print OUT '<?xml version="1.0" encoding="iso-8859-1" ?>' . "\n";
print OUT '<dummy:wrapper xmlns:dummy="http://nowhere.no">' . "\n";

while (<IN>) {
  if (/^([^ \t].*)\n/) {
    if ($first == 1) {
      $first = 0;
    }
    else {
      print OUT $listFooter;
    }
    print OUT $topicStart;
    print OUT $1;
    print OUT $topicEnd;
    print OUT $listHeader;
  }
  elsif (/^[ \t]+([^ \t]+)[ \t]+(.+)\n/) {
    print OUT $lineHeader;
    print OUT "<a target='_blank' href='$path$1.pdf'>$2</a>";
    print OUT $lineEnd;
  }
}

print OUT $listFooter;

print OUT '</dummy:wrapper>' . "\n";

close(OUT);
close(IN);

exit(0);
