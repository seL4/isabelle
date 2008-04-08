#
# $Id$
# Author: Makarius
#
# yxml.pl - simple XML to YXML converter
#

use strict;
use XML::Parser;

binmode(STDOUT, ":utf8");

sub handle_start {
  print chr(5), chr(6), $_[1];
  for (my $i = 2; $i <= $#_; $i++) {
    print ($i % 2 == 0 ? chr(6) : "=");
    print $_[$i];
  }
  print chr(5);
}

sub handle_end {
  print chr(5), chr(6), chr(5);
}

sub handle_char {
  print $_[1];
}

my $parser = new XML::Parser(Handlers =>
  {Start => \&handle_start,
    End => \&handle_end,
    Char => \&handle_char});

$parser->parse(*STDIN);

