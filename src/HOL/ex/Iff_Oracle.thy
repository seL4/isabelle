(*  Title:      HOL/ex/Iff_Oracle.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius
*)

section \<open>Example of Declaring an Oracle\<close>

theory Iff_Oracle
imports Main
begin

subsection \<open>Oracle declaration\<close>

text \<open>
  This oracle makes tautologies of the form @{prop "P \<longleftrightarrow> P \<longleftrightarrow> P \<longleftrightarrow> P"}.
  The length is specified by an integer, which is checked to be even
  and positive.
\<close>

oracle iff_oracle = \<open>
  let
    fun mk_iff 1 = Var (("P", 0), @{typ bool})
      | mk_iff n = HOLogic.mk_eq (Var (("P", 0), @{typ bool}), mk_iff (n - 1));
  in
    fn (thy, n) =>
      if n > 0 andalso n mod 2 = 0
      then Thm.global_cterm_of thy (HOLogic.mk_Trueprop (mk_iff n))
      else raise Fail ("iff_oracle: " ^ string_of_int n)
  end
\<close>


subsection \<open>Oracle as low-level rule\<close>

ML \<open>iff_oracle (@{theory}, 2)\<close>
ML \<open>iff_oracle (@{theory}, 10)\<close>

ML \<open>
  Thm.peek_status (iff_oracle (@{theory}, 10));
  @{assert} (#oracle it);
\<close>

text \<open>These oracle calls had better fail.\<close>

ML \<open>
  (iff_oracle (@{theory}, 5); error "Bad oracle")
    handle Fail _ => writeln "Oracle failed, as expected"
\<close>

ML \<open>
  (iff_oracle (@{theory}, 1); error "Bad oracle")
    handle Fail _ => writeln "Oracle failed, as expected"
\<close>


subsection \<open>Oracle as proof method\<close>

method_setup iff =
  \<open>Scan.lift Parse.nat >> (fn n => fn ctxt =>
    SIMPLE_METHOD
      (HEADGOAL (rtac (iff_oracle (Proof_Context.theory_of ctxt, n)))
        handle Fail _ => no_tac))\<close>


lemma "A \<longleftrightarrow> A"
  by (iff 2)

lemma "A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A"
  by (iff 10)

lemma "A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A \<longleftrightarrow> A"
  apply (iff 5)?
  oops

lemma A
  apply (iff 1)?
  oops

end
