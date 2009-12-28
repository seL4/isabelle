#
# Author: Makarius
#
# system.pl - invoke shell command line (with robust signal handling)
#

# args

($group, $script_name, $pid_name, $output_name) = @ARGV;


# process id

if ($group eq "group") {
  use POSIX "setsid";
  POSIX::setsid || die $!;
}

open (PID_FILE, ">", $pid_name) || die $!;
print PID_FILE "$$";
close PID_FILE;


# exec script

$SIG{'INT'} = "DEFAULT";   #paranoia setting, required for Cygwin
exec qq/exec bash '$script_name' > '$output_name'/;

