(* Author: Tobias Nipkow *)

section \<open>Improved Simproc for $<$\<close>

theory Less_False
imports Main
begin

simproc_setup less_False ("(x::'a::order) < y") = \<open>fn _ => fn ctxt => fn ct =>
  let
    fun prp t thm = Thm.full_prop_of thm aconv t;

    val eq_False_if_not = @{thm eq_False} RS iffD2

    fun prove_less_False ((less as Const(_,T)) $ r $ s) =
      let val prems = Simplifier.prems_of ctxt;
          val le = Const (@{const_name less_eq}, T);
          val t = HOLogic.mk_Trueprop(le $ s $ r);
      in case find_first (prp t) prems of
           NONE =>
             let val t = HOLogic.mk_Trueprop(less $ s $ r)
             in case find_first (prp t) prems of
                  NONE => NONE
                | SOME thm => SOME(mk_meta_eq((thm RS @{thm less_not_sym}) RS eq_False_if_not))
             end
         | SOME thm => NONE
      end;
  in prove_less_False (Thm.term_of ct) end
\<close>

end
