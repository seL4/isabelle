
(* legacy ML bindings *)

val antisym_less_inverse = thm "antisym_less_inverse";
val antisym_less = thm "antisym_less";
val bin_chainmax = thm "bin_chainmax";
val bin_chain = thm "bin_chain";
val box_less = thm "box_less";
val chain_def = thm "chain_def";
val chainE = thm "chainE";
val chainI = thm "chainI";
val chain_mono3 = thm "chain_mono3";
val chain_mono = thm "chain_mono";
val chain_shift = thm "chain_shift";
val chain_tord = thm "chain_tord";
val finite_chain_def = thm "finite_chain_def";
val is_lubD1 = thm "is_lubD1";
val is_lub_def = thm "is_lub_def";
val is_lubI = thm "is_lubI";
val is_lub_lub = thm "is_lub_lub";
val is_lub_range_shift = thm "is_lub_range_shift";
val is_ub_def = thm "is_ub_def";
val is_ub_lub = thm "is_ub_lub";
val is_ub_range_shift = thm "is_ub_range_shift";
val lub_bin_chain = thm "lub_bin_chain";
val lub_chain_maxelem = thm "lub_chain_maxelem";
val lub_const = thm "lub_const";
val lub_def = thm "lub_def";
val lub_finch1 = thm "lub_finch1";
val lub_finch2 = thm "lub_finch2";
val lubI = thm "lubI";
val lub_singleton = thm "lub_singleton";
val lub = thm "lub";
val max_in_chain_def = thm "max_in_chain_def";
val minimal2UU = thm "minimal2UU";
val po_eq_conv = thm "po_eq_conv";
val refl_less = thm "refl_less";
val thelubI = thm "thelubI";
val tord_def = thm "tord_def";
val trans_less = thm "trans_less";
val ub_rangeD = thm "ub_rangeD";
val ub_rangeI = thm "ub_rangeI";
val unique_lub = thm "unique_lub";

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
