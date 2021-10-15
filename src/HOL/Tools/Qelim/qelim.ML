(*  Title:      HOL/Tools/Qelim/qelim.ML
    Author:     Amine Chaieb, TU Muenchen

Generic quantifier elimination conversions for HOL formulae.
*)

signature QELIM =
sig
 val gen_qelim_conv: Proof.context -> conv -> conv -> conv -> (cterm -> 'a -> 'a) -> 'a ->
  ('a -> conv) -> ('a -> conv) -> ('a -> conv) -> conv
 val standard_qelim_conv: Proof.context ->
  (cterm list -> conv) -> (cterm list -> conv) ->
  (cterm list -> conv) -> conv
end;

structure Qelim: QELIM =
struct

val all_not_ex = mk_meta_eq @{thm "all_not_ex"};

fun gen_qelim_conv ctxt precv postcv simpex_conv ins env atcv ncv qcv =
 let
  fun conv env p =
   case Thm.term_of p of
    Const(s,T)$_$_ =>
       if domain_type T = HOLogic.boolT
          andalso member (op =) [\<^const_name>\<open>HOL.conj\<close>, \<^const_name>\<open>HOL.disj\<close>,
            \<^const_name>\<open>HOL.implies\<close>, \<^const_name>\<open>HOL.eq\<close>] s
       then Conv.binop_conv (conv env) p
       else atcv env p
  | Const(\<^const_name>\<open>Not\<close>,_)$_ => Conv.arg_conv (conv env) p
  | Const(\<^const_name>\<open>Ex\<close>,_)$Abs (s, _, _) =>
    let
     val (e,p0) = Thm.dest_comb p
     val (x,p') = Thm.dest_abs_global p0
     val env' = ins x env
     val th = Thm.abstract_rule s x ((conv env' then_conv ncv env') p')
                   |> Drule.arg_cong_rule e
     val th' = simpex_conv (Thm.rhs_of th)
     val (_, r) = Thm.dest_equals (Thm.cprop_of th')
    in if Thm.is_reflexive th' then Thm.transitive th (qcv env (Thm.rhs_of th))
       else Thm.transitive (Thm.transitive th th') (conv env r) end
  | Const(\<^const_name>\<open>Ex\<close>,_)$ _ => (Thm.eta_long_conversion then_conv conv env) p
  | Const(\<^const_name>\<open>All\<close>, _)$_ =>
    let
     val allT = Thm.ctyp_of_cterm (Thm.dest_fun p)
     val T = Thm.dest_ctyp0 (Thm.dest_ctyp0 allT)
     val p = Thm.dest_arg p
     val th = Thm.instantiate' [SOME T] [SOME p] all_not_ex
    in Thm.transitive th (conv env (Thm.rhs_of th))
    end
  | _ => atcv env p
 in precv then_conv (conv env) then_conv postcv end

(* Instantiation of some parameter for most common cases *)

local

val ss =
  simpset_of
   (put_simpset HOL_basic_ss \<^context>
    addsimps @{thms simp_thms ex_simps all_simps all_not_ex not_all ex_disj_distrib});
fun pcv ctxt = Simplifier.rewrite (put_simpset ss ctxt)

in

fun standard_qelim_conv ctxt atcv ncv qcv p =
  let
    val pcv = pcv ctxt
    val env = Cterms.list_set_rev (Cterms.build (Drule.add_frees_cterm p))
  in gen_qelim_conv ctxt pcv pcv pcv cons env atcv ncv qcv p end

end;

end;
