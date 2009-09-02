#
# Author: Sascha Boehme
#
# Reports for Mirabelle
#

my $log_file = $ARGV[0];

open(FILE, "<$log_file") || die "Cannot open file '$log_file'";
my @lines = <FILE>;
close(FILE);

my $unhandled = 0;

my $sh_calls = 0;
my $sh_succeeded = 0;
my $sh_time = 0;

my $metis_calls = 0;
my $metis_succeeded = 0;
my $metis_time = 0;

foreach (@lines) {
  if (m/^unhandled exception/) {
    $unhandled++;
  }
  if (m/^sledgehammer:/) {
    $sh_calls++;
  }
  if (m/^sledgehammer: succeeded \(([0-9]+)\)/) {
    $sh_succeeded++;
    $sh_time += $1;
  }
  if (m/^metis \(sledgehammer\):/) {
    $metis_calls++;
  }
  if (m/^metis \(sledgehammer\): succeeded \(([0-9]+)\)/) {
    $metis_succeeded++;
    $metis_time += $1;
  }
}

open(FILE, ">>$log_file") || die "Cannot open file '$log_file'";

print FILE "\n\n\n";

if ($unhandled > 0) {
  print FILE "Number of unhandled exceptions: $unhandled\n\n";
}

if ($sh_calls > 0) {
  my $percent = $sh_succeeded / $sh_calls * 100;
  my $time = $sh_time / 1000;
  print FILE "Total number of sledgehammer calls: $sh_calls\n";
  print FILE "Number of successful sledgehammer calls: $sh_succeeded\n";
  printf FILE "Percentage of successful sledgehammer calls: %.0f%%\n", $percent;
  print FILE "Total time for successful sledgehammer calls: $time seconds\n\n";
}

if ($metis_calls > 0) {
  my $percent = $metis_succeeded / $metis_calls * 100;
  my $time = $metis_time / 1000;
  print FILE "Total number of metis calls: $metis_calls\n";
  print FILE "Number of successful metis calls: $metis_succeeded\n";
  printf FILE "Percentage of successful metis calls: %.0f%%\n", $percent;
  print FILE "Total time for successful metis calls: $time seconds\n";
}

close(FILE);
