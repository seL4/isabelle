(*  Title:      FOL/ex/Iff_Oracle.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Example of Declaring an Oracle *}

theory Iff_Oracle
imports FOL
begin

subsection {* Oracle declaration *}

text {*
  This oracle makes tautologies of the form @{text "P <-> P <-> P <-> P"}.
  The length is specified by an integer, which is checked to be even
  and positive.
*}

oracle iff_oracle = {*
  let
    fun mk_iff 1 = Var (("P", 0), @{typ o})
      | mk_iff n = FOLogic.iff $ Var (("P", 0), @{typ o}) $ mk_iff (n - 1);
  in
    fn (thy, n) =>
      if n > 0 andalso n mod 2 = 0
      then Thm.cterm_of thy (FOLogic.mk_Trueprop (mk_iff n))
      else raise Fail ("iff_oracle: " ^ string_of_int n)
  end
*}


subsection {* Oracle as low-level rule *}

ML {* iff_oracle (@{theory}, 2) *}
ML {* iff_oracle (@{theory}, 10) *}
ML {* Thm.proof_body_of (iff_oracle (@{theory}, 10)) *}

text {* These oracle calls had better fail. *}

ML {*
  (iff_oracle (@{theory}, 5); error "?")
    handle Fail _ => warning "Oracle failed, as expected"
*}

ML {*
  (iff_oracle (@{theory}, 1); error "?")
    handle Fail _ => warning "Oracle failed, as expected"
*}


subsection {* Oracle as proof method *}

method_setup iff = {*
  Scan.lift OuterParse.nat >> (fn n => fn ctxt =>
    SIMPLE_METHOD
      (HEADGOAL (Tactic.rtac (iff_oracle (ProofContext.theory_of ctxt, n)))
        handle Fail _ => no_tac))
*} "iff oracle"


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
