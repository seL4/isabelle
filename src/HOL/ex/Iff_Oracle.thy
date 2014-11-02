(*  Title:      HOL/ex/Iff_Oracle.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Makarius
*)

section {* Example of Declaring an Oracle *}

theory Iff_Oracle
imports Main
begin

subsection {* Oracle declaration *}

text {*
  This oracle makes tautologies of the form @{prop "P <-> P <-> P <-> P"}.
  The length is specified by an integer, which is checked to be even
  and positive.
*}

oracle iff_oracle = {*
  let
    fun mk_iff 1 = Var (("P", 0), @{typ bool})
      | mk_iff n = HOLogic.mk_eq (Var (("P", 0), @{typ bool}), mk_iff (n - 1));
  in
    fn (thy, n) =>
      if n > 0 andalso n mod 2 = 0
      then Thm.cterm_of thy (HOLogic.mk_Trueprop (mk_iff n))
      else raise Fail ("iff_oracle: " ^ string_of_int n)
  end
*}


subsection {* Oracle as low-level rule *}

ML {* iff_oracle (@{theory}, 2) *}
ML {* iff_oracle (@{theory}, 10) *}
ML {* Thm.peek_status (iff_oracle (@{theory}, 10)) *}

text {* These oracle calls had better fail. *}

ML {*
  (iff_oracle (@{theory}, 5); error "Bad oracle")
    handle Fail _ => warning "Oracle failed, as expected"
*}

ML {*
  (iff_oracle (@{theory}, 1); error "Bad oracle")
    handle Fail _ => warning "Oracle failed, as expected"
*}


subsection {* Oracle as proof method *}

method_setup iff = {*
  Scan.lift Parse.nat >> (fn n => fn ctxt =>
    SIMPLE_METHOD
      (HEADGOAL (rtac (iff_oracle (Proof_Context.theory_of ctxt, n)))
        handle Fail _ => no_tac))
*}


lemma "A <-> A"
  by (iff 2)

lemma "A <-> A <-> A <-> A <-> A <-> A <-> A <-> A <-> A <-> A"
  by (iff 10)

lemma "A <-> A <-> A <-> A <-> A"
  apply (iff 5)?
  oops

lemma A
  apply (iff 1)?
  oops

end
