#
# Author: Makarius
#
# keywords.pl - generate outer syntax keyword files from session logs
#

## arguments

my ($keywords_name, $sessions) = @ARGV;


## keywords

my %keywords;

sub set_keyword {
  my ($name, $kind) = @_;
  if (defined $keywords{$name} and $keywords{$name} ne $kind and $keywords{$name} ne "minor") {
    if ($kind ne "minor") {
      print STDERR "### Inconsistent declaration of keyword \"${name}\": $keywords{$name} vs ${kind}\n";
      $keywords{$name} = $kind;
    }
  } else {
    $keywords{$name} = $kind;
  }
}

sub collect_keywords {
  while(<STDIN>) {
    if (m/^Outer syntax keyword:\s*"(.*)"/) {
      my $name = $1;
      &set_keyword($name, "minor");
    }
    elsif (m/^Outer syntax command:\s*"(.*)"\s*\((.*)\)/) {
      my $name = $1;
      my $kind = $2;
      &set_keyword($name, $kind);
    }
  }
}


## Emacs output

sub emacs_output {
  my @kinds = (
    "major",
    "minor",
    "control",
    "diag",
    "theory-begin",
    "theory-switch",
    "theory-end",
    "theory-heading",
    "theory-decl",
    "theory-script",
    "theory-goal",
    "qed",
    "qed-block",
    "qed-global",
    "proof-heading",
    "proof-goal",
    "proof-block",
    "proof-open",
    "proof-close",
    "proof-chain",
    "proof-decl",
    "proof-asm",
    "proof-asm-goal",
    "proof-script"
  );
  my $file = $keywords_name eq "" ? "isar-keywords.el" : "isar-keywords-${keywords_name}.el";
  open (OUTPUT, "> ${file}") || die "$!";
  select OUTPUT;

  print ";;\n";
  print ";; Keyword classification tables for Isabelle/Isar.\n";
  print ";; Generated from ${sessions}.\n";
  print ";; *** DO NOT EDIT *** DO NOT EDIT *** DO NOT EDIT ***\n";
  print ";;\n";

  for my $kind (@kinds) {
    my @names;
    for my $name (keys(%keywords)) {
      if ($kind eq "major" ? $keywords{$name} ne "minor" : $keywords{$name} eq $kind) {
        if ($kind ne "minor" or $name =~ m/^[A-Za-z0-9_]+$/) {
          push @names, $name;
        }
      }
    }
    @names = sort(@names);

    print "\n(defconst isar-keywords-${kind}";
    print "\n  '(";
    my $first = 1;
    for my $name (@names) {
      $name =~ s/([\.\*\+\?\[\]\^\$])/\\\\$1/g;
      if ($first) {
        print "\"${name}\"";
        $first = 0;
      }
      else {
        print "\n    \"${name}\"";
      }
    }
    print "))\n";
  }
  print "\n(provide 'isar-keywords)\n";

  close OUTPUT;
  select;
  print STDERR "${file}\n";
}


## main

&collect_keywords();
&emacs_output();

