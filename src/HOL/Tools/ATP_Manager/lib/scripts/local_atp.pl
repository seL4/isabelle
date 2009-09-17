use POSIX qw(setsid);

$SIG{'INT'} = "DEFAULT";

defined (my $pid = fork) or die "$!";
if (not $pid) {
  POSIX::setsid or die $!;
  exec @ARGV;
}
else {
  wait;
  my ($user, $system, $cuser, $csystem) = times;
  my $time = ($user + $cuser) * 1000;
  print "$time\n";
}
