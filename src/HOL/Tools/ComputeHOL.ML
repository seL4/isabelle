signature ComputeHOL =
sig
  val prep_thms : thm list -> thm list
  val to_meta_eq : thm -> thm
  val to_hol_eq : thm -> thm
  val symmetric : thm -> thm 
  val trans : thm -> thm -> thm
end

structure ComputeHOL : ComputeHOL =
struct

fun all_prems_conv ci ct = Conv.prems_conv (Logic.count_prems (term_of ct)) ci ct

local
fun lhs_of eq = fst (Thm.dest_equals (cprop_of eq));
in
fun rewrite_conv [] ct = raise CTERM ("rewrite_conv", [])
  | rewrite_conv (eq :: eqs) ct =
      Thm.instantiate (Thm.match (lhs_of eq, ct)) eq
      handle Pattern.MATCH => rewrite_conv eqs ct;
end

val convert_conditions = Conv.fconv_rule (all_prems_conv (fn _ => Conv.else_conv (rewrite_conv [@{thm "Trueprop_eq_eq"}], Conv.all_conv)))

val eq_th = @{thm "HOL.eq_reflection"}
val meta_eq_trivial = @{thm "ComputeHOL.meta_eq_trivial"}
val bool_to_true = @{thm "ComputeHOL.bool_to_true"}

fun to_meta_eq th = eq_th OF [th] handle THM _ => meta_eq_trivial OF [th] handle THM _ => bool_to_true OF [th]

fun to_hol_eq th = @{thm "meta_eq_imp_eq"} OF [th] handle THM _ => @{thm "eq_trivial"} OF [th] 

fun prep_thms ths = map (convert_conditions o to_meta_eq) ths

local
    val sym_HOL = @{thm "HOL.sym"}
    val sym_Pure = @{thm "ProtoPure.symmetric"}
in
  fun symmetric th = ((sym_HOL OF [th]) handle THM _ => (sym_Pure OF [th]))
end

local
    val trans_HOL = @{thm "HOL.trans"}
    val trans_HOL_1 = @{thm "ComputeHOL.transmeta_1"}
    val trans_HOL_2 = @{thm "ComputeHOL.transmeta_2"}
    val trans_HOL_3 = @{thm "ComputeHOL.transmeta_3"}
    fun tr [] th1 th2 = trans_HOL OF [th1, th2]
      | tr (t::ts) th1 th2 = (t OF [th1, th2] handle THM _ => tr ts th1 th2) 
in
  fun trans th1 th2 = tr [trans_HOL, trans_HOL_1, trans_HOL_2, trans_HOL_3] th1 th2
end

end