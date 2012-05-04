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


$emitpid && (print $$, "\n");

if ($head) {
  utf8::upgrade($head);
  $head =~ s/([\x80-\xff])/\\${\(ord($1))}/g;
  print $head, "\n";
}

if (!$quit) {
  while (<STDIN>) {
    print;
  }
}

$tail && (print "$tail", "\n");


# wait forever

close STDOUT;
sleep;
