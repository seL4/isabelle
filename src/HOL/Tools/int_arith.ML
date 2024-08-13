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

val zeroth = Thm.symmetric (mk_meta_eq @{thm of_int_0});

val zero_to_of_int_zero_simproc =
  \<^simproc_setup>\<open>passive zero_to_of_int_zero ("0::'a::ring") =
    \<open>fn _ => fn _ => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = \<^typ>\<open>int\<close> then NONE
        else SOME (Thm.instantiate' [SOME T] [] zeroth)
      end\<close>\<close>;

val oneth = Thm.symmetric (mk_meta_eq @{thm of_int_1});

val one_to_of_int_one_simproc =
  \<^simproc_setup>\<open>passive one_to_of_int_one ("1::'a::ring_1") =
    \<open>fn _ => fn _ => fn ct =>
      let val T = Thm.ctyp_of_cterm ct in
        if Thm.typ_of T = \<^typ>\<open>int\<close> then NONE
        else SOME (Thm.instantiate' [SOME T] [] oneth)
      end\<close>\<close>;

fun check (Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>int\<close>)) = false
  | check (Const (\<^const_name>\<open>Groups.one\<close>, _)) = true
  | check (Const (s, _)) = member (op =) [\<^const_name>\<open>HOL.eq\<close>,
      \<^const_name>\<open>Groups.times\<close>, \<^const_name>\<open>Groups.uminus\<close>,
      \<^const_name>\<open>Groups.minus\<close>, \<^const_name>\<open>Groups.plus\<close>,
      \<^const_name>\<open>Groups.zero\<close>,
      \<^const_name>\<open>Orderings.less\<close>, \<^const_name>\<open>Orderings.less_eq\<close>] s
  | check (a $ b) = check a andalso check b
  | check _ = false;

val conv_ss =
  \<^context>
  |> put_simpset HOL_basic_ss
  |> fold (Simplifier.add_simp o (fn th => th RS sym))
       @{thms of_int_add of_int_mult
         of_int_diff of_int_minus of_int_less_iff
         of_int_le_iff of_int_eq_iff}
  |> Simplifier.add_proc zero_to_of_int_zero_simproc
  |> Simplifier.add_proc one_to_of_int_one_simproc
  |> simpset_of;

val zero_one_idom_simproc =
  \<^simproc_setup>\<open>passive zero_one_idom
    ("(x::'a::ring_char_0) = y" | "(u::'b::linordered_idom) < v" | "(u::'b::linordered_idom) \<le> v") =
    \<open>fn _ => fn ctxt => fn ct =>
      if check (Thm.term_of ct)
      then SOME (Simplifier.rewrite (put_simpset conv_ss ctxt) ct)
      else NONE\<close>\<close>

end;
