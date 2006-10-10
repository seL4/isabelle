Classical.AddSEs [thm "alt_ex1E"];

structure Blast_Data = 
struct
  type claset = Classical.claset
  val equality_name = "op ="
  val not_name = "Not"
  val notE = HOL.notE
  val ccontr = HOL.ccontr
  val contr_tac = Classical.contr_tac
  val dup_intr = Classical.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val claset	= Classical.claset
  val rep_cs = Classical.rep_cs
  val cla_modifiers = Classical.cla_modifiers
  val cla_meth' = Classical.cla_meth'
end;

structure Blast = BlastFun(Blast_Data);

structure HOL =
struct

open HOL;

val Blast_tac = Blast.Blast_tac;
val blast_tac = Blast.blast_tac;

end;