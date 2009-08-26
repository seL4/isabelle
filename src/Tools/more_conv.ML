(* Title:  Tools/more_conv.ML
   Author: Sascha Boehme

Further conversions and conversionals.
*)

signature MORE_CONV =
sig
  val rewrs_conv: thm list -> conv

  val sub_conv: (Proof.context -> conv) -> Proof.context -> conv
  val bottom_conv: (Proof.context -> conv) -> Proof.context -> conv
  val top_conv: (Proof.context -> conv) -> Proof.context -> conv
  val top_sweep_conv: (Proof.context -> conv) -> Proof.context -> conv

  val binder_conv: (Proof.context -> conv) -> Proof.context -> conv

  val cache_conv: conv -> conv
end



structure More_Conv : MORE_CONV =
struct


fun rewrs_conv eqs = Conv.first_conv (map Conv.rewr_conv eqs)


fun sub_conv conv ctxt =
  Conv.comb_conv (conv ctxt) else_conv
  Conv.abs_conv (fn (_, cx) => conv cx) ctxt else_conv
  Conv.all_conv

fun bottom_conv conv ctxt ct =
  (sub_conv (bottom_conv conv) ctxt then_conv conv ctxt) ct

fun top_conv conv ctxt ct =
  (conv ctxt then_conv sub_conv (top_conv conv) ctxt) ct

fun top_sweep_conv conv ctxt ct =
  (conv ctxt else_conv sub_conv (top_sweep_conv conv) ctxt) ct


fun binder_conv cv ctxt =
  Conv.arg_conv (Conv.abs_conv (fn (_, cx) => cv cx) ctxt)


fun cache_conv conv =
  let 
    val tab = ref Termtab.empty
    fun add_result t thm =
      let val _ = change tab (Termtab.insert Thm.eq_thm (t, thm))
      in thm end
    fun cconv ct =  
      (case Termtab.lookup (!tab) (Thm.term_of ct) of
        SOME thm => thm
      | NONE => add_result (Thm.term_of ct) (conv ct))
  in cconv end

end
