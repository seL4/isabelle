#
# Author: Makarius
#
# keywords.pl - generate outer syntax keyword files from session logs
#

## arguments

my ($keywords_name, $target_tool, $sessions) = @ARGV;


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
  print STDERR "${target_tool}: ${file}\n";
}


## jEdit output

sub jedit_output {
  my %keyword_types = (
    "minor"           => "KEYWORD4",
    "control"         => "INVALID",
    "diag"            => "LABEL",
    "theory-begin"    => "KEYWORD3",
    "theory-switch"   => "KEYWORD3",
    "theory-end"      => "KEYWORD3",
    "theory-heading"  => "OPERATOR",
    "theory-decl"     => "OPERATOR",
    "theory-script"   => "KEYWORD1",
    "theory-goal"     => "OPERATOR",
    "qed"             => "OPERATOR",
    "qed-block"       => "OPERATOR",
    "qed-global"      => "OPERATOR",
    "proof-heading"   => "OPERATOR",
    "proof-goal"      => "OPERATOR",
    "proof-block"     => "OPERATOR",
    "proof-open"      => "OPERATOR",
    "proof-close"     => "OPERATOR",
    "proof-chain"     => "OPERATOR",
    "proof-decl"      => "OPERATOR",
    "proof-asm"       => "KEYWORD2",
    "proof-asm-goal"  => "KEYWORD2",
    "proof-script"    => "KEYWORD1"
  );
  my $file = "isabelle.xml";
  open (OUTPUT, "> ${file}") || die "$!";
  select OUTPUT;

  print <<'EOF';
<?xml version="1.0"?>
<!DOCTYPE MODE SYSTEM "xmode.dtd">
EOF
  print "<!-- Generated from ${sessions}. -->\n";
  print "<!-- *** DO NOT EDIT *** DO NOT EDIT *** DO NOT EDIT *** -->\n";
  print <<'EOF';
<MODE>
  <PROPS>
    <PROPERTY NAME="commentStart" VALUE="(*"/>
    <PROPERTY NAME="commentEnd" VALUE="*)"/>
    <PROPERTY NAME="noWordSep" VALUE="_'.?"/>
    <PROPERTY NAME="indentOpenBrackets" VALUE="{"/>
    <PROPERTY NAME="indentCloseBrackets" VALUE="}"/>
    <PROPERTY NAME="unalignedOpenBrackets" VALUE="(" />
    <PROPERTY NAME="unalignedCloseBrackets" VALUE=")" />
    <PROPERTY NAME="tabSize" VALUE="2" />
    <PROPERTY NAME="indentSize" VALUE="2" />
  </PROPS>
  <RULES IGNORE_CASE="FALSE" HIGHLIGHT_DIGITS="FALSE" ESCAPE="\">
    <SPAN TYPE="COMMENT1" NO_ESCAPE="TRUE">
      <BEGIN>(*</BEGIN>
      <END>*)</END>
    </SPAN>
    <SPAN TYPE="COMMENT3" NO_ESCAPE="TRUE">
      <BEGIN>{*</BEGIN>
      <END>*}</END>
    </SPAN>
    <SPAN TYPE="LITERAL1">
      <BEGIN>`</BEGIN>
      <END>`</END>
    </SPAN>
    <SPAN TYPE="LITERAL3">
      <BEGIN>"</BEGIN>
      <END>"</END>
    </SPAN>
    <KEYWORDS>
EOF

  for my $name (sort(keys(%keywords))) {
    my $kind = $keywords{$name};
    my $type = $keyword_types{$kind};
    if ($kind ne "minor" or $name =~ m/^[A-Za-z0-9_]+$/) {
      $name =~ s/&/&amp;/g;
      $name =~ s/</&lt;/g;
      $name =~ s/>/&lt;/g;
      print "      <${type}>${name}</${type}>\n";
    }
  }

  print <<'EOF';
    </KEYWORDS>
  </RULES>
</MODE>
EOF

  close OUTPUT;
  select;
  print STDERR "${target_tool}: ${file}\n";
}


## main

&collect_keywords();
eval "${target_tool}_output()";

