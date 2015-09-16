#
# Author: Markus Wenzel, TU Muenchen
#
# feeder.pl - feed isabelle session
#

# args

($head, $emitpid, $quit, $tail) = @ARGV;


# setup signal handlers

$SIG{'INT'} = "IGNORE";


# main

#buffer lines
$| = 1;

sub emit {
  my ($text) = @_;
  if ($text) {
    utf8::upgrade($text);
    $text =~ s/([\x80-\xff])/\\${\(ord($1))}/g;
    print $text, "\n";
  }
}

$emitpid && (print $$, "\n");

emit("$head");

if (!$quit) {
  while (<STDIN>) {
    print;
  }
}

emit("$tail");


# wait forever

close STDOUT;
sleep;
