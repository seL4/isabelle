
(*** Applying BlastFun to create blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Cla.claset
  val equality_name = @{const_name "op ="}
  val not_name = @{const_name Not}
  val notE	= @{thm notE}
  val ccontr	= @{thm ccontr}
  val contr_tac = Cla.contr_tac
  val dup_intr	= Cla.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val rep_cs = Cla.rep_cs
  val cla_modifiers = Cla.cla_modifiers;
  val cla_meth' = Cla.cla_meth'
  end;

structure Blast = BlastFun(Blast_Data);
val blast_tac = Blast.blast_tac;
