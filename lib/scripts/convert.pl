#
# $Id$
# Author: David von Oheimb, TU Muenchen
# License: GPL (GNU GENERAL PUBLIC LICENSE)
#
# convert.pl - convert legacy tactic scripts to Isabelle/Isar tactic
#   emulation using heuristics - leaves unrecognized patterns unchanged
#   produces from each input file (on the command line) a new file with
#   ".thy" appended


sub thmlist {
  my $s = shift;
  $s =~ s/^\[(.*)\]$/$1/sg;
  $s =~ s/, +/ /g;
  $s =~ s/,/ /g;
  $s;
}

sub process_tac {
  my $t = shift;
  my $simpmodmod = ($t =~ m/auto_tac|force_tac|clarsimp_tac/) ? "simp " : "";

  $_ = $t;
  s/Blast_tac *1/blast/g;
  s/Fast_tac *1/fast/g;
  s/Slow_tac *1/slow/g;
  s/Best_tac *1/best/g;
  s/Safe_tac/safe/g;
  s/Clarify_tac *1/clarify/g;

  s/blast_tac *\( *claset *\( *\) *(.*?)\) *1/blast $1/g;
  s/fast_tac *\( *claset *\( *\) *(.*?)\) *1/fast $1/g;
  s/slow_tac *\( *claset *\( *\) *(.*?)\) *1/slow $1/g;
  s/best_tac *\( *claset *\( *\) *(.*?)\) *1/best $1/g;
  s/safe_tac *\( *claset *\( *\) *(.*?)\) */safe $1/g;
  s/clarify_tac *\( *claset *\( *\) *(.*?)\) *1/clarify $1/g;

  s/Auto_tac/auto/g;
  s/Force_tac *1/force/g;
  s/Clarsimp_tac *1/clarsimp/g;

  s/auto_tac *\( *claset *\( *\) *(.*?), *simpset *\( *\) *(.*?)\) */auto$1$2/g;
  s/force_tac *\( *claset *\( *\) *(.*?), *simpset *\( *\) *(.*?)\) *1/force$1$2/g;
  s/clarsimp_tac *\( *claset *\( *\) *(.*?), *simpset *\( *\) *(.*?)\) *1/clarsimp$1$2/g;

  s/Simp_tac *1/simp (no_asm)/g;
  s/Asm_simp_tac *1/simp (no_asm_simp)/g;
  s/Full_simp_tac_tac *1/simp (no_asm_use)/g;
  s/Asm_full_simp_tac_tac *1/simp/g;
  s/ALLGOALS *Asm_full_simp_tac/simp_all/g;
  s/ALLGOALS *Simp_tac/simp_all (no_asm)/g;

  s/atac *1/assumption/g;
  s/hypsubst_tac *1/hypsubst/g;
  s/arith_tac *1/arith/g;
  s/strip_tac *1/intro strip/g;
  s/split_all_tac *1/simp (no_asm_simp) only: split_tupled_all/g;

  s/rotate_tac *(\d+) *1/rotate_tac $1/g;
  s/rotate_tac *(\d+) *(\d+)/rotate_tac [$2] $1/g;
  s/case_tac *(\".*\") *1/case_tac $1/g;
  s/case_tac *(\".*\") *(\d+)/case_tac [$2] $1/g;
  s/induct_tac *(\".*\") *1/induct_tac $1/g;
  s/induct_tac *(\".*\") *(\d+)/induct_tac [$2] $1/g;

  s/stac (\w+) +1/subst $1/g;
  s/rtac (\w+) +1/rule $1/g;
  s/rtac (\w+) +(\d+)/rule_tac [$2] $1/g;
  s/dtac (\w+) +1/drule $1/g;
  s/dtac (\w+) +(\d+)/drule_tac [$2] $1/g;
  s/etac (\w+) +1/erule $1/g;
  s/etac (\w+) +(\d+)/erule_tac [$2] $1/g;
  s/ftac (\w+) +1/frule $1/g;
  s/rfac (\w+) +(\d+)/frule_tac [$2] $1/g;


  s/THEN/,/g;
  s/ORELSE/|/g;
  s/fold_goals_tac *(\[[\w\s,]*\]|[\w]+)/"fold ".thmlist($1)/eg;
  s/rewrite_goals_tac *(\[[\w\s,]*\]|[\w]+)/"unfold ".thmlist($1)/eg;
  s/cut_facts_tac *(\[[\w\s,]*\]|[\w]+)/"insert ".thmlist($1)/eg;
  s/EVERY *(\[[\w\s,]*\]|[\w]+)/thmlist($1)/eg;
  s/addIs *(\[[\w\s,]*\]|[\w]+)/" intro: ".thmlist($1)/eg;
  s/addSIs *(\[[\w\s,]*\]|[\w]+)/" intro!: ".thmlist($1)/eg;
  s/addEs *(\[[\w\s,]*\]|[\w]+)/" elim: ".thmlist($1)/eg;
  s/addSEs *(\[[\w\s,]*\]|[\w]+)/" elim!: ".thmlist($1)/eg;
  s/addDs *(\[[\w\s,]*\]|[\w]+)/" dest: ".thmlist($1)/eg;
  s/addSDs *(\[[\w\s,]*\]|[\w]+)/" dest!: ".thmlist($1)/eg;
  s/delrules *(\[[\w\s,]*\]|[\w]+)/" del: ".thmlist($1)/eg;
  s/addsimps *(\[[\w\s,]*\]|[\w]+)/" $simpmodmod"."add: ".thmlist($1)/eg;
  s/delsimps *(\[[\w\s,]*\]|[\w]+)/" $simpmodmod"."del: ".thmlist($1)/eg;
  s/addcongs *(\[[\w\s,]*\]|[\w]+)/" cong add: ".thmlist($1)/eg;
  s/delcongs *(\[[\w\s,]*\]|[\w]+)/" cong del: ".thmlist($1)/eg;
  s/addsplits *(\[[\w\s,]*\]|[\w]+)/" split add: ".thmlist($1)/eg;
  s/delsplits *(\[[\w\s,]*\]|[\w]+)/" split del: ".thmlist($1)/eg;

  s/^\s*(.*)\s*$/$1/s;     # remove enclosing whitespace
  s/^\(\s*([\w]+)\s*\)$/$1/; # remove enclosing parentheses around atoms
  s/^([a-zA-Z])/ $1/; # add space if required
  $_;
}

sub thmname { "@@" . ++$thmcount . "@@"; }

sub backpatch_thmnames {
  if($oldargv ne "") {
    select(STDOUT);
    close(ARGVOUT);
    open(TMPW, '>'.$finalfile);
    open TMPR,$tmpfile or die "Can't find tmp file $tmp: $!\n";
    while(<TMPR>) {
      s/@@(\d+)@@/$thmnames[$1]/eg;
      print TMPW $_;
    }
    system("rm " . $oldargv . '.thy~~');
  }
}

sub done {
  my $name = shift;
  my $attr = shift;
  $thmnames[$thmcount] = $name.$attr;
  "done";
}

$next = "nonempty";
while (<>) { # main loop
  if ($ARGV ne $oldargv) {
    $x=$_; backpatch_thmnames; $_=$x;
    $thmcount=0;
    $finalfile = "$ARGV" . '.thy';
    $tmpfile = $finalfile . '~~';
    open(ARGVOUT, '>'.$tmpfile);
    select(ARGVOUT);
    $oldargv = $ARGV;
  }

 nl:
  if(!(s/;\s*?(\n?)$/$1/s)) {# no end_of_ML_command marker
    $next = <>; $_ = $_ . $next;
    if($next) { goto nl; }
  }
  s/\\(\s*\n\s*)\\/ $1 /g; # remove backslashes escaping newlines
 nlc:
  m/^(\s*)(.*?)(\s*)$/s;
  $head=$1; $line=$2; $tail=$3;
  print $head; $_=$2.$tail;
  if ($line =~ m/^\(\*/) { # start comment
    while (($i = index $_,"*)") == -1) { # no end comment
      print $_;
      $_ = <>;
    }
    print substr $_,0,$i+2;
    $_ = substr $_,$i+2;
    goto nlc;
  }
  $_=$line;
  s/^Goalw *(\[[\w\s,]*\]|[\w]+) *(.+)/
    "lemma ".thmname().": $2$head"."apply (unfold ".thmlist($1).")"/se;
  s/^Goal *(.+)/"lemma ".thmname().": $1"/se;
  s/^qed_spec_mp *\"(.*?)\"/done($1," [rule_format (no_asm)]")/se;
  s/^qed *\"(.*?)\"/done($1,"")/se;
  s/^bind_thm *\( *\"(.*?)\" *, *(.*?result *\( *\).*?) *\) *$/done($1,"[?? $2 ??] ")/se;
  s/^by(\s*)(.*)$/"apply$1".process_tac($2)/se;
  print "$_$tail";
  if(!$next) { last; } # prevents reading finally from stdin (thru <>)!
}
backpatch_thmnames;
select(STDOUT);
