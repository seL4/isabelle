#
# $Id$
#
# dimacs2hol.pl - convert files in DIMACS CNF format [1] into Isabelle/HOL
#                 theories
#
# Author: Tjark Weber
# Copyright 2004
#
# For each CNF file, a theory file (with '.thy' appended to the original
# filename) is generated.  The CNF files are not modified.
#
# This script is not too strict about the format of the input file.  However,
# in rare cases it may produce a theory that will not be accepted by
# Isabelle/HOL (e.g. when a CNF file contains '\end{verbatim}' or '*}' in a
# comment).
#
# Each CNF file must contain at least one clause, and may not contain empty
# clauses (i.e. '0' immediately followed by another '0').
#
# The CNF formula is negated, so that an unsatisfiable formula becomes
# provable.
#
# [1] ftp://dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.dvi
#


sub dimacs2hol {
    my ($file) = @_;

    print STDERR "Converting $file ...";

    open (FILE, $file) || die $!;
    undef $/; $_ = <FILE>; $/ = "\n";  # slurp whole file
    close FILE || die $!;

    s/(^c.*\n\s*)*^p[ \t]+cnf[ \t]+\d+[ \t]+\d+[ \t]*\n//m || die "CNF header not found";  # find and remove header
    my ($header) = $&;

    s/^c.*\n//gm;                            # remove further comments
    s/\A\s*//;                               # remove leading whitespace
    s/(\s+0)?\s*\z//;                        # remove trailing whitespace, and possibly a last '0'
    s/-/~/g;                                 # replace '-' by '~' (negation in HOL)
    s/[1-9]\d*/v$&/g;                        # add 'v' before variables
    s/(\s+)0(\s+)/\)$1&$2\(/g;               # replace ' 0 ' by ') & ('
    s/(\d)(\s+[~v])/$1 |$2/g;                # insert ' |' between literals

    my ($filename) = $file;
    $filename =~ s/.*\///g;                  # filter out directories, only leave what's after the last '/'

    open (FILE, "> $file.thy") || die $!;

    print FILE "(* Theory generated from \"$filename\" by dimacs2hol *)\n";
    print FILE "\n";
    print FILE "theory \"$filename\"\n";
    print FILE "imports Main\n";
    print FILE "begin\n";
    print FILE "\n";
    print FILE "text {*\n";
    print FILE "\\begin{verbatim}\n";
    print FILE $header;
    print FILE "\\end{verbatim}\n";
    print FILE "*}\n";
    print FILE "\n";
    print FILE "theorem \"~((";  # negate the whole CNF formula
    print FILE;
    print FILE "))\"\n";
    print FILE "oops\n";
    print FILE "\n";
    print FILE "end\n";

    close FILE || die $!;

    print STDERR " done.\n";
}


## main

foreach $file (@ARGV) {
  eval { &dimacs2hol($file); };
  if ($@) { print STDERR "\n*** dimacs2hol $file: ", $@, "\n"; unlink "$file.thy"; }
}
