(*  Title:      HOL/ex/Fib
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1997  University of Cambridge

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)


(** The difficulty in these proofs is to ensure that the induction hypotheses
    are applied before the definition of "fib".  Towards this end, the 
    "fib" equations are not added to the simpset and are applied very 
    selectively at first.
**)

bind_thm ("fib_Suc_Suc", hd(rev fib.rules));


(*Concrete Mathematics, page 280*)
goal thy "fib (Suc (n + k)) = fib(Suc k) * fib(Suc n) + fib k * fib n";
by (res_inst_tac [("u","n")] fib.induct 1);
(*Simplify the LHS just enough to apply the induction hypotheses*)
by (asm_full_simp_tac
    (!simpset addsimps [read_instantiate[("x", "Suc(?m+?n)")] fib_Suc_Suc]) 3);
by (ALLGOALS 
    (asm_simp_tac (!simpset addsimps 
		   (fib.rules @ add_ac @ mult_ac @
		    [add_mult_distrib, add_mult_distrib2]))));
qed "fib_add";


goal thy "fib (Suc n) ~= 0";
by (res_inst_tac [("u","n")] fib.induct 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps fib.rules)));
qed "fib_Suc_neq_0";
Addsimps [fib_Suc_neq_0];



(*Concrete Mathematics, page 278: Cassini's identity*)
goal thy "fib (Suc (Suc n)) * fib n = \
\              (if n mod 2 = 0 then pred(fib(Suc n) * fib(Suc n)) \
\                              else Suc (fib(Suc n) * fib(Suc n)))";
by (res_inst_tac [("u","n")] fib.induct 1);
by (res_inst_tac [("P", "%z. ?ff(x) * z = ?kk(x)")] (fib_Suc_Suc RS ssubst) 3);
by (stac (read_instantiate [("x", "Suc(Suc ?n)")] fib_Suc_Suc) 3);
by (asm_simp_tac (!simpset addsimps [add_mult_distrib, add_mult_distrib2]) 3);
by (stac (read_instantiate [("x", "Suc ?n")] fib_Suc_Suc) 3);
by (ALLGOALS  (*using fib.rules here results in a longer proof!*)
    (asm_simp_tac (!simpset addsimps [add_mult_distrib, add_mult_distrib2, 
				      mod_less, mod_Suc]
                            addsplits [expand_if])));
by (safe_tac (!claset addSDs [mod2_neq_0]));
by (ALLGOALS
    (asm_full_simp_tac
     (!simpset addsimps (fib.rules @ add_ac @ mult_ac @
			 [add_mult_distrib, add_mult_distrib2, 
			  mod_less, mod_Suc]))));
qed "fib_Cassini";


(** exercise: prove gcd(fib m, fib n) = fib(gcd(m,n)) **)
