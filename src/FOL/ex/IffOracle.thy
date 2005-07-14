(*  Title:      FOL/ex/IffOracle.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Example of Declaring an Oracle *}

theory IffOracle
imports FOL
begin

subsection {* Oracle declaration *}

text {*
  This oracle makes tautologies of the form @{text "P <-> P <-> P <-> P"}.
  The length is specified by an integer, which is checked to be even
  and positive.
*}

oracle iff_oracle (int) = {*
  let
    fun mk_iff 1 = Var (("P", 0), FOLogic.oT)
      | mk_iff n = FOLogic.iff $ Var (("P", 0), FOLogic.oT) $ mk_iff (n - 1);
  in
    fn thy => fn n =>
      if n > 0 andalso n mod 2 = 0
      then FOLogic.mk_Trueprop (mk_iff n)
      else raise Fail ("iff_oracle: " ^ string_of_int n)
  end
*}


subsection {* Oracle as low-level rule *}

ML {* iff_oracle (the_context ()) 2 *}
ML {* iff_oracle (the_context ()) 10 *}
ML {* #der (Thm.rep_thm it) *}

text {* These oracle calls had better fail *}

ML {*
  (iff_oracle (the_context ()) 5; raise ERROR)
    handle Fail _ => warning "Oracle failed, as expected"
*}

ML {*
  (iff_oracle (the_context ()) 1; raise ERROR)
    handle Fail _ => warning "Oracle failed, as expected"
*}


subsection {* Oracle as proof method *}

method_setup iff = {*
  Method.simple_args Args.nat (fn n => fn ctxt =>
    Method.SIMPLE_METHOD
      (HEADGOAL (Tactic.rtac (iff_oracle (ProofContext.theory_of ctxt) n))
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
