(*  Title:      ZF/AC.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The Axiom of Choice

This definition comes from Halmos (1960), page 59.
*)

theory AC = Main:

axioms AC: "[| a: A;  !!x. x:A ==> (EX y. y:B(x)) |] ==> EX z. z : Pi(A,B)"

(*The same as AC, but no premise a \<in> A*)
lemma AC_Pi: "[| !!x. x \<in> A ==> (\<exists>y. y \<in> B(x)) |] ==> \<exists>z. z \<in> Pi(A,B)"
apply (case_tac "A=0")
apply (simp add: Pi_empty1, blast)
(*The non-trivial case*)
apply (blast intro: AC)
done

(*Using dtac, this has the advantage of DELETING the universal quantifier*)
lemma AC_ball_Pi: "\<forall>x \<in> A. \<exists>y. y \<in> B(x) ==> \<exists>y. y \<in> Pi(A,B)"
apply (rule AC_Pi)
apply (erule bspec)
apply assumption
done

lemma AC_Pi_Pow: "\<exists>f. f \<in> (\<Pi>X \<in> Pow(C)-{0}. X)"
apply (rule_tac B1 = "%x. x" in AC_Pi [THEN exE])
apply (erule_tac [2] exI)
apply blast
done

lemma AC_func:
     "[| !!x. x \<in> A ==> (\<exists>y. y \<in> x) |] ==> \<exists>f \<in> A->Union(A). \<forall>x \<in> A. f`x \<in> x"
apply (rule_tac B1 = "%x. x" in AC_Pi [THEN exE])
prefer 2 apply (blast dest: apply_type intro: Pi_type)
apply (blast intro: elim:); 
done

lemma non_empty_family: "[| 0 \<notin> A;  x \<in> A |] ==> \<exists>y. y \<in> x"
apply (subgoal_tac "x \<noteq> 0")
apply blast+
done

lemma AC_func0: "0 \<notin> A ==> \<exists>f \<in> A->Union(A). \<forall>x \<in> A. f`x \<in> x"
apply (rule AC_func)
apply (simp_all add: non_empty_family) 
done

lemma AC_func_Pow: "\<exists>f \<in> (Pow(C)-{0}) -> C. \<forall>x \<in> Pow(C)-{0}. f`x \<in> x"
apply (rule AC_func0 [THEN bexE])
apply (rule_tac [2] bexI)
prefer 2 apply (assumption)
apply (erule_tac [2] fun_weaken_type)
apply blast+
done

lemma AC_Pi0: "0 \<notin> A ==> \<exists>f. f \<in> (\<Pi>x \<in> A. x)"
apply (rule AC_Pi)
apply (simp_all add: non_empty_family) 
done

end
