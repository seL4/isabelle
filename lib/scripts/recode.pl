#
# Author: Makarius
#
# recode.pl - recode utf8 for ML
#

for (@ARGV) {
  utf8::upgrade($_);
  s/([\x80-\xff])/\\${\(ord($1))}/g;
  print $_;
}
