#
# Author: Makarius
#
# tools.pl - list Isabelle tools with description
#

use strict;
use warnings;

my @tools = ();

for my $dir (split(":", $ENV{"ISABELLE_TOOLS"})) {
  if (-d $dir) {
    if (opendir DIR, $dir) {
      for my $name (readdir DIR) {
        my $file = "$dir/$name";
        if (-f $file and -x $file and !($file =~ /~$/ or $file =~ /\.orig$/)) {
          if (open FILE, $file) {
            my $description;
            while (<FILE>) {
              if (!defined($description) and m/DESCRIPTION: *(.*)$/) {
                $description = $1;
              }
            }
            close FILE;
            if (defined($description)) {
              push(@tools, "  $name - $description\n");
            }
          }
        }
      }
      closedir DIR;
    }
  }
}

for (sort @tools) { print };
