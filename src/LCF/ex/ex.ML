(*  Title:      LCF/ex/ex.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Some examples from Lawrence Paulson's book Logic and Computation.
*)


(***  Section 10.4  ***)

val ex_thy =
  thy
  |> Theory.add_consts
   [("P", "'a => tr", NoSyn),
    ("G", "'a => 'a", NoSyn),
    ("H", "'a => 'a", NoSyn),
    ("K", "('a => 'a) => ('a => 'a)", NoSyn)]
  |> PureThy.add_store_axioms
   [("P_strict", "P(UU) = UU"),
    ("K", "K = (%h x. P(x) => x | h(h(G(x))))"),
    ("H", "H = FIX(K)")]
  |> Theory.add_name "Ex 10.4";

val ax = get_axiom ex_thy;

val P_strict = ax"P_strict";
val K = ax"K";
val H = ax"H";

val ex_ss = LCF_ss addsimps [P_strict,K];


val H_unfold = prove_goal ex_thy "H = K(H)"
 (fn _ => [stac H 1, rtac (FIX_eq RS sym) 1]);

val H_strict = prove_goal ex_thy "H(UU)=UU"
 (fn _ => [stac H_unfold 1, simp_tac ex_ss 1]);

val ex_ss = ex_ss addsimps [H_strict];

goal ex_thy "ALL x. H(FIX(K,x)) = FIX(K,x)";
by(induct_tac "K" 1);
by(simp_tac ex_ss 1);
by(simp_tac (ex_ss setloop (split_tac [COND_cases_iff])) 1);
by(strip_tac 1);
by(stac H_unfold 1);
by(asm_simp_tac ex_ss 1);
val H_idemp_lemma = topthm();

val H_idemp = rewrite_rule [mk_meta_eq (H RS sym)] H_idemp_lemma;


(***  Example 3.8  ***)

val ex_thy =
  thy
  |> Theory.add_consts
   [("P", "'a => tr", NoSyn),
    ("F", "'a => 'a", NoSyn),
    ("G", "'a => 'a", NoSyn),
    ("H", "'a => 'b => 'b", NoSyn),
    ("K", "('a => 'b => 'b) => ('a => 'b => 'b)", NoSyn)]
  |> PureThy.add_store_axioms
   [("F_strict", "F(UU) = UU"),
    ("K", "K = (%h x y. P(x) => y | F(h(G(x),y)))"),
    ("H", "H = FIX(K)")]
  |> Theory.add_name "Ex 3.8";

val ax = get_axiom ex_thy;

val F_strict = ax"F_strict";
val K = ax"K";
val H = ax"H";

val ex_ss = LCF_ss addsimps [F_strict,K];

goal ex_thy "ALL x. F(H(x::'a,y::'b)) = H(x,F(y))";
by(stac H 1);
by(induct_tac "K::('a=>'b=>'b)=>('a=>'b=>'b)" 1);
by(simp_tac ex_ss 1);
by(asm_simp_tac (ex_ss setloop (split_tac [COND_cases_iff])) 1);
result();


(*** Addition with fixpoint of successor ***)

val ex_thy =
  thy
  |> Theory.add_consts
   [("s", "'a => 'a", NoSyn),
    ("p", "'a => 'a => 'a", NoSyn)]
  |> PureThy.add_store_axioms
   [("p_strict", "p(UU) = UU"),
    ("p_s", "p(s(x),y) = s(p(x,y))")]
  |> Theory.add_name "fix ex";

val ax = get_axiom ex_thy;

val p_strict = ax"p_strict";
val p_s = ax"p_s";

val ex_ss = LCF_ss addsimps [p_strict,p_s];

goal ex_thy "p(FIX(s),y) = FIX(s)";
by(induct_tac "s" 1);
by(simp_tac ex_ss 1);
by(simp_tac ex_ss 1);
result();


(*** Prefixpoints ***)

val asms = goal thy "[| f(p) << p; !!q. f(q) << q ==> p << q |] ==> FIX(f)=p";
by(rewtac eq_def);
by (rtac conjI 1);
by(induct_tac "f" 1);
by (rtac minimal 1);
by(strip_tac 1);
by (rtac less_trans 1);
by (resolve_tac asms 2);
by (etac less_ap_term 1);
by (resolve_tac asms 1);
by (rtac (FIX_eq RS eq_imp_less1) 1);
result();
