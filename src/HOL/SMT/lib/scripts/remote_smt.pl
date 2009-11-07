#
# Author: Sascha Boehme, TU Muenchen
#
# Invoke remote SMT solvers.
#

use strict;
use LWP;


# arguments

my $url = $ARGV[0];
my $solver = $ARGV[1];
my @options = @ARGV[2 .. ($#ARGV - 1)];
my $problem_file = $ARGV[-1];


# call solver

my $agent = LWP::UserAgent->new;
$agent->agent("SMT-Request");
$agent->timeout(180);
my $response = $agent->post($url, [
  "Solver" => $solver,
  "Options" => join(" ", @options),
  "Problem" => [$problem_file] ],
  "Content_Type" => "form-data");
if (not $response->is_success) {
  print "HTTP-Error: " . $response->message . "\n";
  exit 1;
}
else {
  print $response->content;
  exit 0;
}
