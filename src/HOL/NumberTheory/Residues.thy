(*  Title:      HOL/Quadratic_Reciprocity/Residues.thy
    ID:         $Id$
    Authors:    Jeremy Avigad, David Gray, and Adam Kramer
*)

header {* Residue Sets *}

theory Residues = Int2:;

text{*Note.  This theory is being revised.  See the web page
\url{http://www.andrew.cmu.edu/~avigad/isabelle}.*}

(*****************************************************************)
(*                                                               *)
(* Define the residue of a set, the standard residue, quadratic  *)
(* residues, and prove some basic properties.                    *)
(*                                                               *)
(*****************************************************************)

constdefs
  ResSet      :: "int => int set => bool"
  "ResSet m X == \<forall>y1 y2. (((y1 \<in> X) & (y2 \<in> X) & [y1 = y2] (mod m)) --> 
    y1 = y2)"

  StandardRes :: "int => int => int"
  "StandardRes m x == x mod m"

  QuadRes     :: "int => int => bool"
  "QuadRes m x == \<exists>y. ([(y ^ 2) = x] (mod m))"

  Legendre    :: "int => int => int"      
  "Legendre a p == (if ([a = 0] (mod p)) then 0
                     else if (QuadRes p a) then 1
                     else -1)"

  SR          :: "int => int set"
  "SR p == {x. (0 \<le> x) & (x < p)}"

  SRStar      :: "int => int set"
  "SRStar p == {x. (0 < x) & (x < p)}";

(******************************************************************)
(*                                                                *)
(* Some useful properties of StandardRes                          *)
(*                                                                *)
(******************************************************************)

subsection {* Properties of StandardRes *}

lemma StandardRes_prop1: "[x = StandardRes m x] (mod m)";
  by (auto simp add: StandardRes_def zcong_zmod)

lemma StandardRes_prop2: "0 < m ==> (StandardRes m x1 = StandardRes m x2)
      = ([x1 = x2] (mod m))";
  by (auto simp add: StandardRes_def zcong_zmod_eq)

lemma StandardRes_prop3: "(~[x = 0] (mod p)) = (~(StandardRes p x = 0))";
  by (auto simp add: StandardRes_def zcong_def zdvd_iff_zmod_eq_0)

lemma StandardRes_prop4: "2 < m 
     ==> [StandardRes m x * StandardRes m y = (x * y)] (mod m)";
  by (auto simp add: StandardRes_def zcong_zmod_eq 
                     zmod_zmult_distrib [of x y m])

lemma StandardRes_lbound: "0 < p ==> 0 \<le> StandardRes p x";
  by (auto simp add: StandardRes_def pos_mod_sign)

lemma StandardRes_ubound: "0 < p ==> StandardRes p x < p";
  by (auto simp add: StandardRes_def pos_mod_bound)

lemma StandardRes_eq_zcong: 
   "(StandardRes m x = 0) = ([x = 0](mod m))";
  by (auto simp add: StandardRes_def zcong_eq_zdvd_prop dvd_def) 

(******************************************************************)
(*                                                                *)
(* Some useful stuff relating StandardRes and SRStar and SR       *)
(*                                                                *)
(******************************************************************)

subsection {* Relations between StandardRes, SRStar, and SR *}

lemma SRStar_SR_prop: "x \<in> SRStar p ==> x \<in> SR p";
  by (auto simp add: SRStar_def SR_def)

lemma StandardRes_SR_prop: "x \<in> SR p ==> StandardRes p x = x";
  by (auto simp add: SR_def StandardRes_def mod_pos_pos_trivial)

lemma StandardRes_SRStar_prop1: "2 < p ==> (StandardRes p x \<in> SRStar p) 
     = (~[x = 0] (mod p))";
  apply (auto simp add: StandardRes_prop3 StandardRes_def
                        SRStar_def pos_mod_bound)
  apply (subgoal_tac "0 < p")
by (drule_tac a = x in pos_mod_sign, arith, simp)

lemma StandardRes_SRStar_prop1a: "x \<in> SRStar p ==> ~([x = 0] (mod p))";
  by (auto simp add: SRStar_def zcong_def zdvd_not_zless)

lemma StandardRes_SRStar_prop2: "[| 2 < p; p \<in> zprime; x \<in> SRStar p |] 
     ==> StandardRes p (MultInv p x) \<in> SRStar p";
  apply (frule_tac x = "(MultInv p x)" in StandardRes_SRStar_prop1, simp);
  apply (rule MultInv_prop3)
  apply (auto simp add: SRStar_def zcong_def zdvd_not_zless)
done

lemma StandardRes_SRStar_prop3: "x \<in> SRStar p ==> StandardRes p x = x";
  by (auto simp add: SRStar_SR_prop StandardRes_SR_prop)

lemma StandardRes_SRStar_prop4: "[| p \<in> zprime; 2 < p; x \<in> SRStar p |] 
     ==> StandardRes p x \<in> SRStar p";
  by (frule StandardRes_SRStar_prop3, auto)

lemma SRStar_mult_prop1: "[| p \<in> zprime; 2 < p; x \<in> SRStar p; y \<in> SRStar p|] 
     ==> (StandardRes p (x * y)):SRStar p";
  apply (frule_tac x = x in StandardRes_SRStar_prop4, auto)
  apply (frule_tac x = y in StandardRes_SRStar_prop4, auto)
  apply (auto simp add: StandardRes_SRStar_prop1 zcong_zmult_prop3)
done

lemma SRStar_mult_prop2: "[| p \<in> zprime; 2 < p; ~([a = 0](mod p)); 
     x \<in> SRStar p |] 
     ==> StandardRes p (a * MultInv p x) \<in> SRStar p";
  apply (frule_tac x = x in StandardRes_SRStar_prop2, auto)
  apply (frule_tac x = "MultInv p x" in StandardRes_SRStar_prop1)
  apply (auto simp add: StandardRes_SRStar_prop1 zcong_zmult_prop3)
done

lemma SRStar_card: "2 < p ==> int(card(SRStar p)) = p - 1";
  by (auto simp add: SRStar_def int_card_bdd_int_set_l_l)

lemma SRStar_finite: "2 < p ==> finite( SRStar p)";
  by (auto simp add: SRStar_def bdd_int_set_l_l_finite)

(******************************************************************)
(*                                                                *)
(* Some useful stuff about ResSet and StandardRes                 *)
(*                                                                *)
(******************************************************************)

subsection {* Properties relating ResSets with StandardRes *}

lemma aux: "x mod m = y mod m ==> [x = y] (mod m)";
  apply (subgoal_tac "x = y ==> [x = y](mod m)");
  apply (subgoal_tac "[x mod m = y mod m] (mod m) ==> [x = y] (mod m)");
  apply (auto simp add: zcong_zmod [of x y m])
done

lemma StandardRes_inj_on_ResSet: "ResSet m X ==> (inj_on (StandardRes m) X)";
  apply (auto simp add: ResSet_def StandardRes_def inj_on_def)
  apply (drule_tac m = m in aux, auto)
done

lemma StandardRes_Sum: "[| finite X; 0 < m |] 
     ==> [setsum f X = setsum (StandardRes m o f) X](mod m)"; 
  apply (rule_tac F = X in finite_induct)
  apply (auto intro!: zcong_zadd simp add: StandardRes_prop1)
done

lemma SR_pos: "0 < m ==> (StandardRes m ` X) \<subseteq> {x. 0 \<le> x & x < m}";
  by (auto simp add: StandardRes_ubound StandardRes_lbound)

lemma ResSet_finite: "0 < m ==> ResSet m X ==> finite X";
  apply (rule_tac f = "StandardRes m" in finite_imageD) 
  apply (rule_tac B = "{x. (0 :: int) \<le> x & x < m}" in finite_subset);
by (auto simp add: StandardRes_inj_on_ResSet bdd_int_set_l_finite SR_pos)

lemma mod_mod_is_mod: "[x = x mod m](mod m)";
  by (auto simp add: zcong_zmod)

lemma StandardRes_prod: "[| finite X; 0 < m |] 
     ==> [gsetprod f X = gsetprod (StandardRes m o f) X] (mod m)";
  apply (rule_tac F = X in finite_induct)
by (auto intro!: zcong_zmult simp add: StandardRes_prop1)

lemma ResSet_image: "[| 0 < m; ResSet m A; \<forall>x \<in> A. \<forall>y \<in> A. ([f x = f y](mod m) --> x = y) |] ==> ResSet m (f ` A)";
  by (auto simp add: ResSet_def)

(****************************************************************)
(*                                                              *)
(* Property for SRStar                                          *)
(*                                                              *)
(****************************************************************)

lemma ResSet_SRStar_prop: "ResSet p (SRStar p)";
  by (auto simp add: SRStar_def ResSet_def zcong_zless_imp_eq)

end;