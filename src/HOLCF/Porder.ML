
(* legacy ML bindings *)

val is_ub_def = thm "is_ub_def";
val is_lub_def = thm "is_lub_def";
val tord_def = thm "tord_def";
val chain_def = thm "chain_def";
val max_in_chain_def = thm "max_in_chain_def";
val finite_chain_def = thm "finite_chain_def";
val lub_def = thm "lub_def";
val unique_lub = thm "unique_lub";
val chain_mono = thm "chain_mono";
val chain_mono3 = thm "chain_mono3";
val chain_tord = thm "chain_tord";
val lub = thm "lub";
val lubI = thm "lubI";
val thelubI = thm "thelubI";
val lub_singleton = thm "lub_singleton";
val is_lubD1 = thm "is_lubD1";
val is_lub_lub = thm "is_lub_lub";
val is_lubI = thm "is_lubI";
val chainE = thm "chainE";
val chainI = thm "chainI";
val chain_shift = thm "chain_shift";
val ub_rangeD = thm "ub_rangeD";
val ub_rangeI = thm "ub_rangeI";
val is_ub_lub = thm "is_ub_lub";
val lub_finch1 = thm "lub_finch1";
val lub_finch2 = thm "lub_finch2";
val bin_chain = thm "bin_chain";
val bin_chainmax = thm "bin_chainmax";
val lub_bin_chain = thm "lub_bin_chain";
val lub_chain_maxelem = thm "lub_chain_maxelem";
val lub_const = thm "lub_const";

structure Porder =
struct
  val thy = the_context ();
  val is_ub_def = is_ub_def;
  val is_lub_def = is_lub_def;
  val tord_def = tord_def;
  val chain_def = chain_def;
  val max_in_chain_def = max_in_chain_def;
  val finite_chain_def = finite_chain_def;
  val lub_def = lub_def;
end;
