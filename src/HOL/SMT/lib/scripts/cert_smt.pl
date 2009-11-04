#
# Author: Sascha Boehme, TU Muenchen
#
# Fake SMT solver: check that input matches previously computed input and
# and return previously computed output.
#

use strict;
use File::Compare;


# arguments

my $cert_path = $ARGV[0];
my $new_problem = $ARGV[1];


# check content of new problem file against old problem file

my $old_problem = $cert_path;
my $old_proof = $cert_path . ".proof";

if (-e $old_problem and compare($old_problem, $new_problem) == 0) {
  if (-e $old_proof) {
    open FILE, "<$old_proof";
    foreach (<FILE>) {
      print $_;
    }
    close FILE;
  }
  else { print "ERROR: unable to open proof file\n"; }
}
else { print "ERROR: bad problem\n"; }
