#!/usr/bin/env perl -w
#
# Script to invoke remote SMT solvers.
# Author: Sascha Boehme, TU Muenchen
#

use strict;
use LWP;


# environment

my $remote_smt_url = $ENV{"REMOTE_SMT_URL"};


# arguments

my $solver = $ARGV[0];
my @options = @ARGV[1 .. ($#ARGV - 2)];
my $problem_file = $ARGV[-2];
my $output_file = $ARGV[-1];


# call solver

my $agent = LWP::UserAgent->new;
$agent->agent("SMT-Request");
$agent->timeout(180);
my $response = $agent->post($remote_smt_url, [
  "Solver" => $solver,
  "Options" => join(" ", @options),
  "Problem" => [$problem_file] ],
  "Content_Type" => "form-data");
if (not $response->is_success) {
  print "HTTP-Error: " . $response->message . "\n";
  exit 1;
}
else {
  open(FILE, ">$output_file");
  print FILE $response->content;
  close(FILE);
}

