#
# Author: Sascha Boehme, TU Muenchen
#
# Cache for prover results, based on discriminating problems using MD5.

use strict;
use warnings;
use Digest::MD5;
use LWP;


# arguments

my $certs_file = shift @ARGV;
my $location = shift @ARGV;
my $result_file = pop @ARGV;
my $problem_file = $ARGV[-1];

my $use_certs = not ($certs_file eq "-");


# create MD5 problem digest

my $problem_digest = "";
if ($use_certs) {
  my $md5 = Digest::MD5->new;
  open FILE, "<$problem_file" or
    die "ERROR: Failed to open '$problem_file' ($!)";
  $md5->addfile(*FILE);
  close FILE;
  $problem_digest = $md5->b64digest;
}


# lookup problem digest among existing certificates and
# return a cached result (if there is a certificate for the problem)

if ($use_certs and -e $certs_file) {
  my $cached = 0;
  open CERTS, "<$certs_file" or die "ERROR: Failed to open '$certs_file' ($!)";
  while (<CERTS>) {
    if (m/(\S+) (\d+)/) {
      if ($1 eq $problem_digest) {
        my $start = tell CERTS;
        open FILE, ">$result_file" or
          die "ERROR: Failed to open '$result_file ($!)";
        while ((tell CERTS) - $start < $2) {
          my $line = <CERTS>;
          print FILE $line;
        }
        close FILE;
        $cached = 1;
        last;
      }
      else { seek CERTS, $2, 1; }
    }
    else { die "ERROR: Invalid file format in '$certs_file'"; }
  }
  close CERTS;
  if ($cached) { exit 0; }
}


# invoke (remote or local) prover

if ($location eq "remote") {
  # arguments
  my $solver = $ARGV[0];
  my @options = @ARGV[1 .. ($#ARGV - 1)];

  # call solver
  my $agent = LWP::UserAgent->new;
  $agent->agent("SMT-Request");
  $agent->timeout(180);
  my $response = $agent->post($ENV{"REMOTE_SMT_URL"}, [
    "Solver" => $solver,
    "Options" => join(" ", @options),
    "Problem" => [$problem_file] ],
    "Content_Type" => "form-data");
  if (not $response->is_success) { die "HTTP-Error: " . $response->message; }
  else {
    open FILE, ">$result_file" or
      die "ERROR: Failed to create '$result_file' ($!)";
    print FILE $response->content;
    close FILE;
  }
}
elsif ($location eq "local") {
  system "@ARGV >$result_file 2>&1";
}
else { die "ERROR: No SMT solver invoked"; }


# cache result

if ($use_certs) {
  open CERTS, ">>$certs_file" or
    die "ERROR: Failed to open '$certs_file' ($!)";
  print CERTS
    ("$problem_digest " . ((-s $result_file) + (length "\n")) . "\n");

  open FILE, "<$result_file" or
    die "ERROR: Failed to open '$result_file' ($!)";
  foreach (<FILE>) { print CERTS $_; }
  close FILE; 

  print CERTS "\n";
  close CERTS;
}

