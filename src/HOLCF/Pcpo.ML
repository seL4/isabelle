
(* legacy ML bindings *)

val cpo = thm "cpo";
val least = thm "least";
val UU_def = thm "UU_def";
val chfin = thm "chfin";
val ax_flat = thm "ax_flat";
val UU_least = thm "UU_least";
val minimal = thm "minimal";
val thelubE = thm "thelubE";
val is_ub_thelub = thm "is_ub_thelub";
val is_lub_thelub = thm "is_lub_thelub";
val lub_range_shift = thm "lub_range_shift";
val maxinch_is_thelub = thm "maxinch_is_thelub";
val lub_mono = thm "lub_mono";
val lub_equal = thm "lub_equal";
val lub_mono2 = thm "lub_mono2";
val lub_equal2 = thm "lub_equal2";
val lub_mono3 = thm "lub_mono3";
val eq_UU_iff = thm "eq_UU_iff";
val UU_I = thm "UU_I";
val not_less2not_eq = thm "not_less2not_eq";
val chain_UU_I = thm "chain_UU_I";
val chain_UU_I_inverse = thm "chain_UU_I_inverse";
val chain_UU_I_inverse2 = thm "chain_UU_I_inverse2";
val notUU_I = thm "notUU_I";
val chain_mono2 = thm "chain_mono2";
val flat_imp_chfin = thm "flat_imp_chfin";
val flat_eq = thm "flat_eq";
val chfin2finch = thm "chfin2finch";
val infinite_chain_adm_lemma = thm "infinite_chain_adm_lemma";
val increasing_chain_adm_lemma = thm "increasing_chain_adm_lemma";

structure Pcpo =
struct
  val thy = the_context ();
  val UU_def = UU_def;
end;
