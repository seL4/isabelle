
(*Better then ex1E for classical reasoner: needs no quantifier duplication!*)
val major::prems = goal (the_context ())
    "[| ?! x. P(x);                                              \
\       !!x. [| P(x);  ALL y y'. P(y) & P(y') --> y=y' |] ==> R  \
\    |] ==> R";
by (rtac (major RS ex1E) 1);
by (REPEAT (ares_tac (allI::prems) 1));
by (etac (dup_elim allE) 1);
by (Fast_tac 1);
qed "alt_ex1E";

AddSEs [alt_ex1E];

(*** Applying BlastFun to create Blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Classical.claset
  val notE	= notE
  val ccontr	= ccontr
  val contr_tac = Classical.contr_tac
  val dup_intr	= Classical.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val claset	= Classical.claset
  val rep_cs    = Classical.rep_cs
  val atomize	= thms "atomize'"
  val cla_modifiers = Classical.cla_modifiers;
  val cla_meth' = Classical.cla_meth'
  end;

structure Blast = BlastFun(Blast_Data);
Blast.overloaded ("op =", domain_type);	(*overloading of equality as iff*)

val Blast_tac = Blast.Blast_tac
and blast_tac = Blast.blast_tac;
