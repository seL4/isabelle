
(*** Applying BlastFun to create Blast_tac ***)
structure Blast_Data = 
  struct
  type claset	= Cla.claset
  val notE	= notE
  val ccontr	= ccontr
  val contr_tac = Cla.contr_tac
  val dup_intr	= Cla.dup_intr
  val hyp_subst_tac = Hypsubst.blast_hyp_subst_tac
  val claset	= Cla.claset
  val rep_cs    = Cla.rep_cs
  val atomize	= thms "atomize'"
  val cla_modifiers = Cla.cla_modifiers;
  val cla_meth' = Cla.cla_meth'
  end;

structure Blast = BlastFun(Blast_Data);

val Blast_tac = Blast.Blast_tac
and blast_tac = Blast.blast_tac;
