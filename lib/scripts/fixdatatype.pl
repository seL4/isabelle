#
# $Id$
#
# fixdatatype.pl - adapt theories and proof scripts to new datatype package
#

sub fixdatatype {
    my ($file) = @_;

    open (FILE, $file) || die $!;
    undef $/; $text = <FILE>; $/ = "\n";         # slurp whole file
    close FILE || die $!;

    $_ = $text;

    ## convert split_type_case[_asm] to type.split[_asm]
    s/([^"])\bsplit_([\w]+)_case\b/$1$2.split/sg;
    s/([^"])\bsplit_([\w]+)_case_asm\b/$1$2.split_asm/sg;

    ## delete function name and type after "primrec"
    s/\bprimrec\b\s+([\w]+|"[^"]+")\s+([\w\.]+)/primrec/sg;

    ## replace specific induct_tac by generic induct_tac
    s/[\w\.]+\.induct_tac/induct_tac/sg;

    ## replace res_inst_tac ... natE by case_tac
    s/\bres_inst_tac\b\s*\[\s*\(\s*"[^"]+"\s*,\s*("[^"]+")\s*\)\s*\]\s*natE\b/case_tac $1/sg;

    $result = $_;

    if ($text ne $result) {
        print STDERR "fixing $file\n";
        if (! -f "$file~~") {
            rename $file, "$file~~" || die $!;
        }
        open (FILE, "> $file") || die $!;
        print FILE $result;
        close FILE || die $!;
    }
}


## main

foreach $file (@ARGV) {
  eval { &fixdatatype($file); };
  if ($@) { print STDERR "*** fixdatatype $file: ", $@, "\n"; }
}
