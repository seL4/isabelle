(*  ID:   $Id$
    Author:     Konrad Slind
    Copyright   1995 TU Munich
*)

header {*Well-founded Relations*}

theory Wellfounded_Relations
imports Finite_Set
begin

text{*Derived WF relations such as inverse image, lexicographic product and
measure. The simple relational product, in which @{term "(x',y')"} precedes
@{term "(x,y)"} if @{term "x'<x"} and @{term "y'<y"}, is a subset of the
lexicographic product, and therefore does not need to be defined separately.*}

constdefs
 less_than :: "(nat*nat)set"
    "less_than == trancl pred_nat"

 measure   :: "('a => nat) => ('a * 'a)set"
    "measure == inv_image less_than"

 lex_prod  :: "[('a*'a)set, ('b*'b)set] => (('a*'b)*('a*'b))set"
               (infixr "<*lex*>" 80)
    "ra <*lex*> rb == {((a,b),(a',b')). (a,a') : ra | a=a' & (b,b') : rb}"

 finite_psubset  :: "('a set * 'a set) set"
   --{* finite proper subset*}
    "finite_psubset == {(A,B). A < B & finite B}"

 same_fst :: "('a => bool) => ('a => ('b * 'b)set) => (('a*'b)*('a*'b))set"
    "same_fst P R == {((x',y'),(x,y)) . x'=x & P x & (y',y) : R x}"
   --{*For @{text rec_def} declarations where the first n parameters
       stay unchanged in the recursive call. 
       See @{text "Library/While_Combinator.thy"} for an application.*}




subsection{*Measure Functions make Wellfounded Relations*}

subsubsection{*`Less than' on the natural numbers*}

lemma wf_less_than [iff]: "wf less_than"
by (simp add: less_than_def wf_pred_nat [THEN wf_trancl])

lemma trans_less_than [iff]: "trans less_than"
by (simp add: less_than_def trans_trancl)

lemma less_than_iff [iff]: "((x,y): less_than) = (x<y)"
by (simp add: less_than_def less_def)

lemma full_nat_induct:
  assumes ih: "(!!n. (ALL m. Suc m <= n --> P m) ==> P n)"
  shows "P n"
apply (rule wf_less_than [THEN wf_induct])
apply (rule ih, auto)
done

subsubsection{*The Inverse Image into a Wellfounded Relation is Wellfounded.*}

lemma wf_inv_image [simp,intro!]: "wf(r) ==> wf(inv_image r (f::'a=>'b))"
apply (simp (no_asm_use) add: inv_image_def wf_eq_minimal)
apply clarify
apply (subgoal_tac "EX (w::'b) . w : {w. EX (x::'a) . x: Q & (f x = w) }")
prefer 2 apply (blast del: allE)
apply (erule allE)
apply (erule (1) notE impE)
apply blast
done


subsubsection{*Finally, All Measures are Wellfounded.*}

lemma wf_measure [iff]: "wf (measure f)"
apply (unfold measure_def)
apply (rule wf_less_than [THEN wf_inv_image])
done

lemma measure_induct_rule [case_names less]:
  fixes f :: "'a \<Rightarrow> nat"
  assumes step: "\<And>x. (\<And>y. f y < f x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P a"
proof -
  have "wf (measure f)" ..
  then show ?thesis
  proof induct
    case (less x)
    show ?case
    proof (rule step)
      fix y
      assume "f y < f x"
      then have "(y, x) \<in> measure f"
        by (simp add: measure_def inv_image_def)
      then show "P y" by (rule less)
    qed
  qed
qed

lemma measure_induct:
  fixes f :: "'a \<Rightarrow> nat"
  shows "(\<And>x. \<forall>y. f y < f x \<longrightarrow> P y \<Longrightarrow> P x) \<Longrightarrow> P a"
  by (rule measure_induct_rule [of f P a]) iprover


subsection{*Other Ways of Constructing Wellfounded Relations*}

text{*Wellfoundedness of lexicographic combinations*}
lemma wf_lex_prod [intro!]: "[| wf(ra); wf(rb) |] ==> wf(ra <*lex*> rb)"
apply (unfold wf_def lex_prod_def) 
apply (rule allI, rule impI)
apply (simp (no_asm_use) only: split_paired_All)
apply (drule spec, erule mp) 
apply (rule allI, rule impI)
apply (drule spec, erule mp, blast) 
done

text{*Transitivity of WF combinators.*}
lemma trans_lex_prod [intro!]: 
    "[| trans R1; trans R2 |] ==> trans (R1 <*lex*> R2)"
by (unfold trans_def lex_prod_def, blast) 

subsubsection{*Wellfoundedness of proper subset on finite sets.*}
lemma wf_finite_psubset: "wf(finite_psubset)"
apply (unfold finite_psubset_def)
apply (rule wf_measure [THEN wf_subset])
apply (simp add: measure_def inv_image_def less_than_def less_def [symmetric])
apply (fast elim!: psubset_card_mono)
done

lemma trans_finite_psubset: "trans finite_psubset"
by (simp add: finite_psubset_def psubset_def trans_def, blast)


subsubsection{*Wellfoundedness of finite acyclic relations*}

text{*This proof belongs in this theory because it needs Finite.*}

lemma finite_acyclic_wf [rule_format]: "finite r ==> acyclic r --> wf r"
apply (erule finite_induct, blast)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
done

lemma finite_acyclic_wf_converse: "[|finite r; acyclic r|] ==> wf (r^-1)"
apply (erule finite_converse [THEN iffD2, THEN finite_acyclic_wf])
apply (erule acyclic_converse [THEN iffD2])
done

lemma wf_iff_acyclic_if_finite: "finite r ==> wf r = acyclic r"
by (blast intro: finite_acyclic_wf wf_acyclic)


subsubsection{*Wellfoundedness of @{term same_fst}*}

lemma same_fstI [intro!]:
     "[| P x; (y',y) : R x |] ==> ((x,y'),(x,y)) : same_fst P R"
by (simp add: same_fst_def)

lemma wf_same_fst:
  assumes prem: "(!!x. P x ==> wf(R x))"
  shows "wf(same_fst P R)"
apply (simp cong del: imp_cong add: wf_def same_fst_def)
apply (intro strip)
apply (rename_tac a b)
apply (case_tac "wf (R a)")
 apply (erule_tac a = b in wf_induct, blast)
apply (blast intro: prem)
done


subsection{*Weakly decreasing sequences (w.r.t. some well-founded order) 
   stabilize.*}

text{*This material does not appear to be used any longer.*}

lemma lemma1: "[| ALL i. (f (Suc i), f i) : r^* |] ==> (f (i+k), f i) : r^*"
apply (induct_tac "k", simp_all)
apply (blast intro: rtrancl_trans)
done

lemma lemma2: "[| ALL i. (f (Suc i), f i) : r^*; wf (r^+) |]  
      ==> ALL m. f m = x --> (EX i. ALL k. f (m+i+k) = f (m+i))"
apply (erule wf_induct, clarify)
apply (case_tac "EX j. (f (m+j), f m) : r^+")
 apply clarify
 apply (subgoal_tac "EX i. ALL k. f ((m+j) +i+k) = f ( (m+j) +i) ")
  apply clarify
  apply (rule_tac x = "j+i" in exI)
  apply (simp add: add_ac, blast)
apply (rule_tac x = 0 in exI, clarsimp)
apply (drule_tac i = m and k = k in lemma1)
apply (blast elim: rtranclE dest: rtrancl_into_trancl1)
done

lemma wf_weak_decr_stable: "[| ALL i. (f (Suc i), f i) : r^*; wf (r^+) |]  
      ==> EX i. ALL k. f (i+k) = f i"
apply (drule_tac x = 0 in lemma2 [THEN spec], auto)
done

(* special case of the theorem above: <= *)
lemma weak_decr_stable:
     "ALL i. f (Suc i) <= ((f i)::nat) ==> EX i. ALL k. f (i+k) = f i"
apply (rule_tac r = pred_nat in wf_weak_decr_stable)
apply (simp add: pred_nat_trancl_eq_le)
apply (intro wf_trancl wf_pred_nat)
done


ML
{*
val less_than_def = thm "less_than_def";
val measure_def = thm "measure_def";
val lex_prod_def = thm "lex_prod_def";
val finite_psubset_def = thm "finite_psubset_def";

val wf_less_than = thm "wf_less_than";
val trans_less_than = thm "trans_less_than";
val less_than_iff = thm "less_than_iff";
val full_nat_induct = thm "full_nat_induct";
val wf_inv_image = thm "wf_inv_image";
val wf_measure = thm "wf_measure";
val measure_induct = thm "measure_induct";
val wf_lex_prod = thm "wf_lex_prod";
val trans_lex_prod = thm "trans_lex_prod";
val wf_finite_psubset = thm "wf_finite_psubset";
val trans_finite_psubset = thm "trans_finite_psubset";
val finite_acyclic_wf = thm "finite_acyclic_wf";
val finite_acyclic_wf_converse = thm "finite_acyclic_wf_converse";
val wf_iff_acyclic_if_finite = thm "wf_iff_acyclic_if_finite";
val wf_weak_decr_stable = thm "wf_weak_decr_stable";
val weak_decr_stable = thm "weak_decr_stable";
val same_fstI = thm "same_fstI";
val wf_same_fst = thm "wf_same_fst";
*}


end
