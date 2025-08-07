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

fun gen_qelim_conv ctxt precv postcv simpex_conv ins env atcv ncv qcv =
  let
    fun conv env p =
      (case Thm.term_of p of
        \<^Const_>\<open>conj for _ _\<close> => Conv.binop_conv (conv env) p
      | \<^Const_>\<open>disj for _ _\<close> => Conv.binop_conv (conv env) p
      | \<^Const_>\<open>implies for _ _\<close> => Conv.binop_conv (conv env) p
      | \<^Const_>\<open>HOL.eq _ for _ _\<close> => Conv.binop_conv (conv env) p
      | \<^Const_>\<open>Not for _\<close> => Conv.arg_conv (conv env) p
      | \<^Const_>\<open>Ex _ for \<open>Abs (s, _, _)\<close>\<close> =>
          let
            val (e,p0) = Thm.dest_comb p
            val (x,p') = Thm.dest_abs_global p0
            val env' = ins x env
            val th =
              Thm.abstract_rule s x ((conv env' then_conv ncv env') p')
              |> Drule.arg_cong_rule e
            val th' = simpex_conv (Thm.rhs_of th)
            val (_, r) = Thm.dest_equals (Thm.cprop_of th')
          in
            if Thm.is_reflexive th' then Thm.transitive th (qcv env (Thm.rhs_of th))
            else Thm.transitive (Thm.transitive th th') (conv env r)
          end
      | \<^Const_>\<open>Ex _ for _\<close> => (Thm.eta_long_conversion then_conv conv env) p
      | \<^Const_>\<open>All _ for _\<close> =>
          let
            val allT = Thm.ctyp_of_cterm (Thm.dest_fun p)
            val T = Thm.dest_ctyp0 (Thm.dest_ctyp0 allT)
            val P = Thm.dest_arg p
            val th = \<^instantiate>\<open>'a = T and P in lemma "\<forall>x::'a. P x \<equiv> \<nexists>x. \<not> P x" by simp\<close>
          in Thm.transitive th (conv env (Thm.rhs_of th)) end
      | _ => atcv env p)
  in precv then_conv (conv env) then_conv postcv end


(* Instantiation of some parameter for most common cases *)

local

val ss =
  simpset_of
   (put_simpset HOL_basic_ss \<^context>
    |> Simplifier.add_simps @{thms simp_thms ex_simps all_simps all_not_ex not_all ex_disj_distrib});

fun pcv ctxt = Simplifier.rewrite (put_simpset ss ctxt)

in

fun standard_qelim_conv ctxt atcv ncv qcv p =
  let
    val pcv = pcv ctxt
    val env = Cterms.list_set_rev (Cterms.build (Drule.add_frees_cterm p))
  in gen_qelim_conv ctxt pcv pcv pcv cons env atcv ncv qcv p end

end;

end;
