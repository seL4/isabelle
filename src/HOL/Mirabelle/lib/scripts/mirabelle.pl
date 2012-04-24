#
# Author: Jasmin Blanchette and Sascha Boehme
#
# Testing tool for automated proof tools.
#

use File::Basename;

# environment

my $isabelle_home = $ENV{'ISABELLE_HOME'};
my $mirabelle_home = $ENV{'MIRABELLE_HOME'};
my $mirabelle_logic = $ENV{'MIRABELLE_LOGIC'};
my $mirabelle_theory = $ENV{'MIRABELLE_THEORY'};
my $output_path = $ENV{'MIRABELLE_OUTPUT_PATH'};
my $timeout = $ENV{'MIRABELLE_TIMEOUT'};
my $be_quiet = $ENV{'MIRABELLE_QUIET'};
my $actions = $ENV{'MIRABELLE_ACTIONS'};

my $mirabelle_thy = $mirabelle_home . "/Mirabelle";


# arguments

my $thy_file = $ARGV[0];
my $start_line = "0";
my $end_line = "~1";
if ($thy_file =~ /^(.*)\[([0-9]+)\:(~?[0-9]+)\]$/) {
  $thy_file = $1;
  $start_line = $2;
  $end_line = $3;
}
my ($thy_name, $path, $ext) = fileparse($thy_file, ".thy");
my $rand_suffix = join('', map { ('a'..'z')[rand(26)] } 1 .. 10);
my $new_thy_name = $thy_name . "_Mirabelle_" . $rand_suffix;
my $new_thy_file = $path . "/" . $new_thy_name . $ext;


# setup

my $setup_thy_name = $thy_name . "_Setup";
my $setup_file = $output_path . "/" . $setup_thy_name . ".thy";
my $log_file = $output_path . "/" . $thy_name . ".log";

my @action_files;
my @action_names;
foreach (split(/:/, $actions)) {
  if (m/([^[]*)/) {
    push @action_files, "\"$mirabelle_home/Tools/mirabelle_$1.ML\"";
    push @action_names, $1;
  }
}
my $tools = "";
if ($#action_files >= 0) {
  # uniquify
  my $s = join ("\n", @action_files);
  my @action_files = split(/\n/, $s . "\n" . $s);
  %action_files = sort(@action_files);
  $tools = "uses " . join(" ", sort(keys(%action_files)));
}

open(SETUP_FILE, ">$setup_file") || die "Could not create file '$setup_file'";

print SETUP_FILE <<END;
theory "$setup_thy_name"
imports "$mirabelle_thy" "$mirabelle_theory"
$tools
begin

setup {*
  Config.put_global Mirabelle.logfile "$log_file" #>
  Config.put_global Mirabelle.timeout $timeout #>
  Config.put_global Mirabelle.start_line $start_line #>
  Config.put_global Mirabelle.end_line $end_line
*}

END

@action_list = split(/:/, $actions);

foreach (reverse(@action_list)) {
  if (m/([^[]*)(?:\[(.*)\])?/) {
    my ($name, $settings_str) = ($1, $2 || "");
    $name =~ s/^([a-z])/\U$1/;
    print SETUP_FILE "setup {* Mirabelle_$name.invoke [";
    my $sep = "";
    foreach (split(/,/, $settings_str)) {
      if (m/\s*([^=]*)\s*=\s*(.*)\s*/) {
        print SETUP_FILE "$sep(\"$1\", \"$2\")";
        $sep = ", ";
      }
      elsif (m/\s*(.*)\s*/) {
        print SETUP_FILE "$sep(\"$1\", \"\")";
        $sep = ", ";
      }
    }
    print SETUP_FILE "] *}\n";
  }
}

print SETUP_FILE "\nend";
close SETUP_FILE;


# modify target theory file

open(OLD_FILE, "<$thy_file") || die "Cannot open file '$thy_file'";
my @lines = <OLD_FILE>;
close(OLD_FILE);

my $setup_import =
  substr("\"$output_path\/$setup_thy_name\"" . (" " x 1000), 0, 1000);

my $thy_text = join("", @lines);
my $old_len = length($thy_text);
$thy_text =~ s/(theory\s+)\"?$thy_name\"?/$1"$new_thy_name"/g;
$thy_text =~ s/(imports)(\s+)/$1 $setup_import$2/g;
die "No 'imports' found" if length($thy_text) == $old_len;

open(NEW_FILE, ">$new_thy_file") || die "Cannot create file '$new_thy_file'";
print NEW_FILE $thy_text;
close(NEW_FILE);


# run isabelle

open(LOG_FILE, ">$log_file");
print LOG_FILE "Run of $new_thy_file with:\n";
foreach $action  (@action_list) {
  print LOG_FILE "  $action\n";
}
close(LOG_FILE);

my $quiet = "";
my $output_log = 1;
if (defined $be_quiet and $be_quiet ne "") {
  $quiet = " > /dev/null 2>&1";
  $output_log = 0;
}

if ($output_log) { print "Mirabelle: $thy_file\n"; }

my $result = system "\"$ENV{'ISABELLE_PROCESS'}\" " .
  "-e 'Unsynchronized.setmp quick_and_dirty true use_thy \"$path/$new_thy_name\" handle _ => exit 1;\n' -q $mirabelle_logic" . $quiet;

if ($output_log) { print "Finished:  $thy_file\n"; }


# cleanup

unlink $setup_file;
unlink $new_thy_file;

exit ($result ? 1 : 0);
