(*  Title:      HOL/Quadratic_Reciprocity/Finite2.thy
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*Finite Sets and Finite Sums*}

theory Finite2 = Main + IntFact:;

text{*These are useful for combinatorial and number-theoretic counting
arguments.*}

text{*Note.  This theory is being revised.  See the web page
\url{http://www.andrew.cmu.edu/~avigad/isabelle}.*}

(******************************************************************)
(*                                                                *)
(* gsetprod: A generalized set product function, for ints only.   *)
(* Note that "setprod", as defined in IntFact, is equivalent to   *)
(*   our "gsetprod id".                                           *) 
(*                                                                *)
(******************************************************************)

consts
  gsetprod :: "('a => int) => 'a set => int"

defs
  gsetprod_def: "gsetprod f A ==  if finite A then fold (op * o f) 1 A else 1";

lemma gsetprod_empty [simp]: "gsetprod f {} = 1";
  by (auto simp add: gsetprod_def)

lemma gsetprod_insert [simp]: "[| finite A; a \<notin> A |] ==> 
    gsetprod f (insert a A) = f a * gsetprod f A";
  by (simp add: gsetprod_def LC_def LC.fold_insert)

(******************************************************************)
(*                                                                *)
(* Useful properties of sums and products                         *)
(*                                                                *)
(******************************************************************);

subsection {* Useful properties of sums and products *}

lemma setprod_gsetprod_id: "setprod A = gsetprod id A";
  by (auto simp add: setprod_def gsetprod_def)

lemma setsum_same_function: "[| finite S; \<forall>x \<in> S. f x = g x |] ==> 
    setsum f S = setsum g S";
by (induct set: Finites, auto)

lemma gsetprod_same_function: "[| finite S; \<forall>x \<in> S. f x = g x |] ==> 
  gsetprod f S = gsetprod g S";
by (induct set: Finites, auto)

lemma setsum_same_function_zcong: 
   "[| finite S; \<forall>x \<in> S. [f x = g x](mod m) |] 
     ==> [setsum f S = setsum g S] (mod m)";
   by (induct set: Finites, auto simp add: zcong_zadd)

lemma gsetprod_same_function_zcong: 
   "[| finite S; \<forall>x \<in> S. [f x = g x](mod m) |] 
     ==> [gsetprod f S = gsetprod g S] (mod m)";
by (induct set: Finites, auto simp add: zcong_zmult)

lemma gsetprod_Un_Int: "finite A ==> finite B
    ==> gsetprod g (A \<union> B) * gsetprod g (A \<inter> B) = 
    gsetprod g A * gsetprod g B";
  apply (induct set: Finites)
by (auto simp add: Int_insert_left insert_absorb)

lemma gsetprod_Un_disjoint: "[| finite A; finite B; A \<inter> B = {} |] ==> 
    gsetprod g (A \<union> B) = gsetprod g A * gsetprod g B";
  apply (subst gsetprod_Un_Int [symmetric])
by auto

lemma setsum_const: "finite X ==> setsum (%x. (c :: int)) X = c * int(card X)";
  apply (induct set: Finites)
by (auto simp add: zadd_zmult_distrib2)

lemma setsum_const2: "finite X ==> int (setsum (%x. (c :: nat)) X) = 
    int(c) * int(card X)";
  apply (induct set: Finites)
  apply (auto simp add: zadd_zmult_distrib2)
done

lemma setsum_minus: "finite A ==> setsum (%x. ((f x)::int) - g x) A = 
  setsum f A - setsum g A";
  by (induct set: Finites, auto)

lemma setsum_const_mult: "finite A ==> setsum (%x. c * ((f x)::int)) A = 
    c * setsum f A";
  apply (induct set: Finites, auto)
  by (auto simp only: zadd_zmult_distrib2) 

lemma setsum_non_neg: "[| finite A; \<forall>x \<in> A. (0::int) \<le> f x |] ==>
    0 \<le>  setsum f A";
  by (induct set: Finites, auto)

lemma gsetprod_const: "finite X ==> gsetprod (%x. (c :: int)) X = c ^ (card X)";
  apply (induct set: Finites)
by auto

(******************************************************************)
(*                                                                *)
(* Cardinality of some explicit finite sets                       *)
(*                                                                *)
(******************************************************************);

subsection {* Cardinality of explicit finite sets *}

lemma finite_surjI: "[| B \<subseteq> f ` A; finite A |] ==> finite B";
by (simp add: finite_subset finite_imageI)

lemma bdd_nat_set_l_finite: "finite { y::nat . y < x}";
apply (rule_tac N = "{y. y < x}" and n = x in bounded_nat_set_is_finite)
by auto

lemma bdd_nat_set_le_finite: "finite { y::nat . y \<le> x  }";
apply (subgoal_tac "{ y::nat . y \<le> x  } = { y::nat . y < Suc x}")
by (auto simp add: bdd_nat_set_l_finite)

lemma  bdd_int_set_l_finite: "finite { x::int . 0 \<le> x & x < n}";
apply (subgoal_tac " {(x :: int). 0 \<le> x & x < n} \<subseteq> 
    int ` {(x :: nat). x < nat n}");
apply (erule finite_surjI)
apply (auto simp add: bdd_nat_set_l_finite image_def)
apply (rule_tac x = "nat x" in exI, simp) 
done

lemma bdd_int_set_le_finite: "finite {x::int. 0 \<le> x & x \<le> n}";
apply (subgoal_tac "{x. 0 \<le> x & x \<le> n} = {x. 0 \<le> x & x < n + 1}")
apply (erule ssubst)
apply (rule bdd_int_set_l_finite)
by auto

lemma bdd_int_set_l_l_finite: "finite {x::int. 0 < x & x < n}";
apply (subgoal_tac "{x::int. 0 < x & x < n} \<subseteq> {x::int. 0 \<le> x & x < n}")
by (auto simp add: bdd_int_set_l_finite finite_subset)

lemma bdd_int_set_l_le_finite: "finite {x::int. 0 < x & x \<le> n}";
apply (subgoal_tac "{x::int. 0 < x & x \<le> n} \<subseteq> {x::int. 0 \<le> x & x \<le> n}")
by (auto simp add: bdd_int_set_le_finite finite_subset)

lemma card_bdd_nat_set_l: "card {y::nat . y < x} = x";
apply (induct_tac x, force)
proof -;
  fix n::nat;
  assume "card {y. y < n} = n"; 
  have "{y. y < Suc n} = insert n {y. y < n}";
    by auto
  then have "card {y. y < Suc n} = card (insert n {y. y < n})";
    by auto
  also have "... = Suc (card {y. y < n})";
    apply (rule card_insert_disjoint)
    by (auto simp add: bdd_nat_set_l_finite)
  finally show "card {y. y < Suc n} = Suc n"; 
    by (simp add: prems)
qed;

lemma card_bdd_nat_set_le: "card { y::nat. y \<le> x} = Suc x";
apply (subgoal_tac "{ y::nat. y \<le> x} = { y::nat. y < Suc x}")
by (auto simp add: card_bdd_nat_set_l)

lemma card_bdd_int_set_l: "0 \<le> (n::int) ==> card {y. 0 \<le> y & y < n} = nat n";
proof -;
  fix n::int;
  assume "0 \<le> n";
  have "finite {y. y < nat n}";
    by (rule bdd_nat_set_l_finite)
  moreover have "inj_on (%y. int y) {y. y < nat n}";
    by (auto simp add: inj_on_def)
  ultimately have "card (int ` {y. y < nat n}) = card {y. y < nat n}";
    by (rule card_image)
  also from prems have "int ` {y. y < nat n} = {y. 0 \<le> y & y < n}";
    apply (auto simp add: zless_nat_eq_int_zless image_def)
    apply (rule_tac x = "nat x" in exI)
    by (auto simp add: nat_0_le)
  also; have "card {y. y < nat n} = nat n" 
    by (rule card_bdd_nat_set_l)
  finally show "card {y. 0 \<le> y & y < n} = nat n"; .;
qed;

lemma card_bdd_int_set_le: "0 \<le> (n::int) ==> card {y. 0 \<le> y & y \<le> n} = 
  nat n + 1";
apply (subgoal_tac "{y. 0 \<le> y & y \<le> n} = {y. 0 \<le> y & y < n+1}")
apply (insert card_bdd_int_set_l [of "n+1"])
by (auto simp add: nat_add_distrib)

lemma card_bdd_int_set_l_le: "0 \<le> (n::int) ==> 
    card {x. 0 < x & x \<le> n} = nat n";
proof -;
  fix n::int;
  assume "0 \<le> n";
  have "finite {x. 0 \<le> x & x < n}";
    by (rule bdd_int_set_l_finite)
  moreover have "inj_on (%x. x+1) {x. 0 \<le> x & x < n}";
    by (auto simp add: inj_on_def)
  ultimately have "card ((%x. x+1) ` {x. 0 \<le> x & x < n}) = 
     card {x. 0 \<le> x & x < n}";
    by (rule card_image)
  also from prems have "... = nat n";
    by (rule card_bdd_int_set_l)
  also; have "(%x. x + 1) ` {x. 0 \<le> x & x < n} = {x. 0 < x & x<= n}";
    apply (auto simp add: image_def)
    apply (rule_tac x = "x - 1" in exI)
    by arith
  finally; show "card {x. 0 < x & x \<le> n} = nat n";.;
qed;

lemma card_bdd_int_set_l_l: "0 < (n::int) ==> 
    card {x. 0 < x & x < n} = nat n - 1";
  apply (subgoal_tac "{x. 0 < x & x < n} = {x. 0 < x & x \<le> n - 1}")
  apply (insert card_bdd_int_set_l_le [of "n - 1"])
  by (auto simp add: nat_diff_distrib)

lemma int_card_bdd_int_set_l_l: "0 < n ==> 
    int(card {x. 0 < x & x < n}) = n - 1";
  apply (auto simp add: card_bdd_int_set_l_l)
  apply (subgoal_tac "Suc 0 \<le> nat n")
  apply (auto simp add: zdiff_int [THEN sym])
  apply (subgoal_tac "0 < nat n", arith)
  by (simp add: zero_less_nat_eq)

lemma int_card_bdd_int_set_l_le: "0 \<le> n ==> 
    int(card {x. 0 < x & x \<le> n}) = n";
  by (auto simp add: card_bdd_int_set_l_le)

(******************************************************************)
(*                                                                *)
(* Cartesian products of finite sets                              *)
(*                                                                *)
(******************************************************************)

subsection {* Cardinality of finite cartesian products *}

lemma insert_Sigma [simp]: "~(A = {}) ==>
  (insert x A) <*> B = ({ x } <*> B) \<union> (A <*> B)";
  by blast

lemma cartesian_product_finite: "[| finite A; finite B |] ==> 
    finite (A <*> B)";
  apply (rule_tac F = A in finite_induct)
  by auto

lemma cartesian_product_card_a [simp]: "finite A ==> 
    card({x} <*> A) = card(A)"; 
  apply (subgoal_tac "inj_on (%y .(x,y)) A");
  apply (frule card_image, assumption)
  apply (subgoal_tac "(Pair x ` A) = {x} <*> A");
  by (auto simp add: inj_on_def)

lemma cartesian_product_card [simp]: "[| finite A; finite B |] ==> 
  card (A <*> B) = card(A) * card(B)";
  apply (rule_tac F = A in finite_induct, auto)
  apply (case_tac "F = {}", force)
  apply (subgoal_tac "card({x} <*> B \<union> F <*> B) = card({x} <*> B) + 
    card(F <*> B)");
  apply simp
  apply (rule card_Un_disjoint)
  by auto

(******************************************************************)
(*                                                                *)
(* Sums and products over finite sets                             *)
(*                                                                *)
(******************************************************************)

subsection {* Reindexing sums and products *}

lemma sum_prop [rule_format]: "finite B ==>
                  inj_on f B --> setsum h (f ` B) = setsum (h \<circ> f) B";
apply (rule finite_induct, assumption, force)
apply (rule impI, auto)
apply (simp add: inj_on_def)
apply (subgoal_tac "f x \<notin> f ` F")
apply (subgoal_tac "finite (f ` F)");
apply (auto simp add: setsum_insert)
by (simp add: inj_on_def) 

lemma sum_prop_id: "finite B ==> inj_on f B ==> 
    setsum f B = setsum id (f ` B)";
by (auto simp add: sum_prop id_o)

lemma prod_prop [rule_format]: "finite B ==>
        inj_on f B --> gsetprod h (f ` B) = gsetprod (h \<circ> f) B";
  apply (rule finite_induct, assumption, force)
  apply (rule impI)
  apply (auto simp add: inj_on_def)
  apply (subgoal_tac "f x \<notin> f ` F")
  apply (subgoal_tac "finite (f ` F)");
by (auto simp add: gsetprod_insert)

lemma prod_prop_id: "[| finite B; inj_on f B |] ==> 
    gsetprod id (f ` B) = (gsetprod f B)";
  by (simp add: prod_prop id_o)

subsection {* Lemmas for counting arguments *}

lemma finite_union_finite_subsets: "[| finite A; \<forall>X \<in> A. finite X |] ==> 
    finite (Union A)";
apply (induct set: Finites)
by auto

lemma finite_index_UNION_finite_sets: "finite A ==> 
    (\<forall>x \<in> A. finite (f x)) --> finite (UNION A f)";
by (induct_tac rule: finite_induct, auto)

lemma card_union_disjoint_sets: "finite A ==> 
    ((\<forall>X \<in> A. finite X) & (\<forall>X \<in> A. \<forall>Y \<in> A. X \<noteq> Y --> X \<inter> Y = {})) ==> 
    card (Union A) = setsum card A";
  apply auto
  apply (induct set: Finites, auto)
  apply (frule_tac B = "Union F" and A = x in card_Un_Int)
by (auto simp add: finite_union_finite_subsets)

(*
  We just duplicated something in the standard library: the next lemma 
  is setsum_UN_disjoint in Finite_Set

lemma setsum_indexed_union_disjoint_sets [rule_format]: "finite A ==> 
    ((\<forall>x \<in> A. finite (g x)) & 
    (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y --> (g x) \<inter> (g y) = {})) --> 
      setsum f (UNION A g) = setsum (%x. setsum f (g x)) A";
apply (induct_tac rule: finite_induct)
apply (assumption, simp, clarify)
apply (subgoal_tac "g x \<inter> (UNION F g) = {}");
apply (subgoal_tac "finite (UNION F g)");
apply (simp add: setsum_Un_disjoint)
by (auto simp add: finite_index_UNION_finite_sets)

*)

lemma int_card_eq_setsum [rule_format]: "finite A ==> 
    int (card A) = setsum (%x. 1) A";
  by (erule finite_induct, auto)

lemma card_indexed_union_disjoint_sets [rule_format]: "finite A ==> 
    ((\<forall>x \<in> A. finite (g x)) & 
    (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y --> (g x) \<inter> (g y) = {})) --> 
      card (UNION A g) = setsum (%x. card (g x)) A";
apply clarify
apply (frule_tac f = "%x.(1::nat)" and A = g in 
    setsum_UN_disjoint);
apply assumption+;
apply (subgoal_tac "finite (UNION A g)");
apply (subgoal_tac "(\<Sum>x \<in> UNION A g. 1) = (\<Sum>x \<in> A. \<Sum>x \<in> g x. 1)");
apply (auto simp only: card_eq_setsum)
apply (erule setsum_same_function)
by (auto simp add: card_eq_setsum)

lemma int_card_indexed_union_disjoint_sets [rule_format]: "finite A ==> 
    ((\<forall>x \<in> A. finite (g x)) & 
    (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y --> (g x) \<inter> (g y) = {})) --> 
       int(card (UNION A g)) = setsum (%x. int( card (g x))) A";
apply clarify
apply (frule_tac f = "%x.(1::int)" and A = g in 
    setsum_UN_disjoint);
apply assumption+;
apply (subgoal_tac "finite (UNION A g)");
apply (subgoal_tac "(\<Sum>x \<in> UNION A g. 1) = (\<Sum>x \<in> A. \<Sum>x \<in> g x. 1)");
apply (auto simp only: int_card_eq_setsum)
apply (erule setsum_same_function)
by (auto simp add: int_card_eq_setsum)

lemma setsum_bij_eq: "[| finite A; finite B; f ` A \<subseteq> B; inj_on f A; 
    g ` B \<subseteq> A; inj_on g B |] ==> setsum g B = setsum (g \<circ> f) A";
apply (frule_tac h = g and f = f in sum_prop, auto)
apply (subgoal_tac "setsum g B = setsum g (f ` A)");
apply (simp add: inj_on_def)
apply (subgoal_tac "card A = card B")
apply (drule_tac A = "f ` A" and B = B in card_seteq)
apply (auto simp add: card_image)
apply (frule_tac A = A and B = B and f = f in card_inj_on_le, auto)
apply (frule_tac A = B and B = A and f = g in card_inj_on_le)
by auto

lemma gsetprod_bij_eq: "[| finite A; finite B; f ` A \<subseteq> B; inj_on f A; 
    g ` B \<subseteq> A; inj_on g B |] ==> gsetprod g B = gsetprod (g \<circ> f) A";
  apply (frule_tac h = g and f = f in prod_prop, auto) 
  apply (subgoal_tac "gsetprod g B = gsetprod g (f ` A)"); 
  apply (simp add: inj_on_def)
  apply (subgoal_tac "card A = card B")
  apply (drule_tac A = "f ` A" and B = B in card_seteq)
  apply (auto simp add: card_image)
  apply (frule_tac A = A and B = B and f = f in card_inj_on_le, auto)
by (frule_tac A = B and B = A and f = g in card_inj_on_le, auto)

lemma setsum_union_disjoint_sets [rule_format]: "finite A ==> 
    ((\<forall>X \<in> A. finite X) & (\<forall>X \<in> A. \<forall>Y \<in> A. X \<noteq> Y --> X \<inter> Y = {})) 
    --> setsum f (Union A) = setsum (%x. setsum f x) A";
apply (induct_tac rule: finite_induct)
apply (assumption, simp, clarify)
apply (subgoal_tac "x \<inter> (Union F) = {}");
apply (subgoal_tac "finite (Union F)");
  by (auto simp add: setsum_Un_disjoint Union_def)

lemma gsetprod_union_disjoint_sets [rule_format]: "[| 
    finite (A :: int set set); 
    (\<forall>X \<in> A. finite (X :: int set));
    (\<forall>X \<in> A. (\<forall>Y \<in> A. (X :: int set) \<noteq> (Y :: int set) --> 
      (X \<inter> Y) = {})) |] ==> 
  ( gsetprod (f :: int => int) (Union A) = gsetprod (%x. gsetprod f x) A)";
  apply (induct set: Finites)
  apply (auto simp add: gsetprod_empty) 
  apply (subgoal_tac "gsetprod f (x \<union> Union F) = 
    gsetprod f x * gsetprod f (Union F)");
  apply simp
  apply (rule gsetprod_Un_disjoint)
by (auto simp add: gsetprod_Un_disjoint Union_def)

lemma gsetprod_disjoint_sets: "[| finite A;
    \<forall>X \<in> A. finite X; 
    \<forall>X \<in> A. \<forall>Y \<in> A. (X \<noteq> Y --> X \<inter> Y = {}) |] ==> 
  gsetprod id (Union A) = gsetprod (gsetprod id) A";
  apply (rule_tac f = id in gsetprod_union_disjoint_sets)
  by auto

lemma setprod_disj_sets: "[| finite (A::int set set);
    \<forall>X \<in> A. finite X;
    \<forall>X \<in> A. \<forall>Y \<in> A. (X \<noteq> Y --> X \<inter> Y = {}) |] ==> 
  setprod (Union A) = gsetprod (%x. setprod x) A";
  by (auto simp add: setprod_gsetprod_id gsetprod_disjoint_sets)

end;
