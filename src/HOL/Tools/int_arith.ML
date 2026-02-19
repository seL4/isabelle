(* Author: Tobias Nipkow

A special simproc for the instantiation of the generic linear arithmetic package for int.
*)

signature INT_ARITH =
sig
  val zero_one_idom_simproc: simproc
end

structure Int_Arith : INT_ARITH =
struct

(* Update parameters of arithmetic prover *)

(* reduce contradictory =/</<= to False *)

(* Evaluation of terms of the form "m R n" where R is one of "=", "<=" or "<",
   and m and n are ground terms over rings (roughly speaking).
   That is, m and n consist only of 1s combined with "+", "-" and "*".
*)

val zero_to_of_int_zero_simproc =
  \<^simproc_setup>\<open>passive zero_to_of_int_zero ("0::'a::ring") =
    \<open>fn _ => fn _ => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = \<^Type>\<open>int\<close> then NONE
        else SOME \<^instantiate>\<open>'a = T in lemma "0 \<equiv> of_int 0" by simp\<close>
      end\<close>\<close>;

val one_to_of_int_one_simproc =
  \<^simproc_setup>\<open>passive one_to_of_int_one ("1::'a::ring_1") =
    \<open>fn _ => fn _ => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = \<^Type>\<open>int\<close> then NONE
        else SOME \<^instantiate>\<open>'a = T in lemma "1 \<equiv> of_int 1" by simp\<close>
      end\<close>\<close>;

fun check \<^Const_>\<open>Groups.one \<^Type>\<open>int\<close>\<close> = false
  | check \<^Const_>\<open>Groups.one _\<close> = true
  | check \<^Const_>\<open>Groups.zero _\<close> = true
  | check \<^Const_>\<open>HOL.eq _\<close> = true
  | check \<^Const_>\<open>times _\<close> = true
  | check \<^Const_>\<open>uminus _\<close> = true
  | check \<^Const_>\<open>minus _\<close> = true
  | check \<^Const_>\<open>plus _\<close> = true
  | check \<^Const_>\<open>less _\<close> = true
  | check \<^Const_>\<open>less_eq _\<close> = true
  | check (a $ b) = check a andalso check b
  | check _ = false;

val conv_ss =
  HOL_basic_ss
  |> Simplifier.simpset_map \<^context> (
    Simplifier.add_simps
       @{thms of_int_add [symmetric] of_int_mult [symmetric]
         of_int_diff [symmetric] of_int_minus [symmetric] of_int_less_iff [symmetric]
         of_int_le_iff [symmetric] of_int_eq_iff [symmetric]}
    #> Simplifier.add_proc zero_to_of_int_zero_simproc
    #> Simplifier.add_proc one_to_of_int_one_simproc);

val zero_one_idom_simproc =
  \<^simproc_setup>\<open>passive zero_one_idom
    ("(x::'a::ring_char_0) = y" | "(u::'b::linordered_idom) < v" | "(u::'b::linordered_idom) \<le> v") =
    \<open>fn _ => fn ctxt => fn ct =>
      if check (Thm.term_of ct)
      then SOME (Simplifier.rewrite (put_simpset conv_ss ctxt) ct)
      else NONE\<close>\<close>

end;
