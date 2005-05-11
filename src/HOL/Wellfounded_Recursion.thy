(*  ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge
*)

header {*Well-founded Recursion*}

theory Wellfounded_Recursion
imports Transitive_Closure
begin

consts
  wfrec_rel :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => ('a * 'b) set"

inductive "wfrec_rel R F"
intros
  wfrecI: "ALL z. (z, x) : R --> (z, g z) : wfrec_rel R F ==>
            (x, F g x) : wfrec_rel R F"

constdefs
  wf         :: "('a * 'a)set => bool"
  "wf(r) == (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x. P(x)))"

  acyclic :: "('a*'a)set => bool"
  "acyclic r == !x. (x,x) ~: r^+"

  cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b"
  "cut f r x == (%y. if (y,x):r then f y else arbitrary)"

  adm_wf :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => bool"
  "adm_wf R F == ALL f g x.
     (ALL z. (z, x) : R --> f z = g z) --> F f x = F g x"

  wfrec :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b"
  "wfrec R F == %x. THE y. (x, y) : wfrec_rel R (%f x. F (cut f R x) x)"

axclass wellorder \<subseteq> linorder
  wf: "wf {(x,y::'a::ord). x<y}"


lemma wfUNIVI: 
   "(!!P x. (ALL x. (ALL y. (y,x) : r --> P(y)) --> P(x)) ==> P(x)) ==> wf(r)"
by (unfold wf_def, blast)

text{*Restriction to domain @{term A}.  
  If @{term r} is well-founded over @{term A} then @{term "wf r"}*}
lemma wfI: 
 "[| r <= A <*> A;   
     !!x P. [| ALL x. (ALL y. (y,x) : r --> P y) --> P x;  x:A |] ==> P x |]   
  ==>  wf r"
by (unfold wf_def, blast)

lemma wf_induct: 
    "[| wf(r);           
        !!x.[| ALL y. (y,x): r --> P(y) |] ==> P(x)  
     |]  ==>  P(a)"
by (unfold wf_def, blast)

lemma wf_not_sym [rule_format]: "wf(r) ==> ALL x. (a,x):r --> (x,a)~:r"
by (erule_tac a=a in wf_induct, blast)

(* [| wf r;  ~Z ==> (a,x) : r;  (x,a) ~: r ==> Z |] ==> Z *)
lemmas wf_asym = wf_not_sym [elim_format]

lemma wf_not_refl [simp]: "wf(r) ==> (a,a) ~: r"
by (blast elim: wf_asym)

(* [| wf r;  (a,a) ~: r ==> PROP W |] ==> PROP W *)
lemmas wf_irrefl = wf_not_refl [elim_format]

text{*transitive closure of a well-founded relation is well-founded! *}
lemma wf_trancl: "wf(r) ==> wf(r^+)"
apply (subst wf_def, clarify)
apply (rule allE, assumption)
  --{*Retains the universal formula for later use!*}
apply (erule mp)
apply (erule_tac a = x in wf_induct)
apply (blast elim: tranclE)
done

lemma wf_converse_trancl: "wf (r^-1) ==> wf ((r^+)^-1)"
apply (subst trancl_converse [symmetric])
apply (erule wf_trancl)
done


subsubsection{*Minimal-element characterization of well-foundedness*}

lemma lemma1: "wf r ==> x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q)"
apply (unfold wf_def)
apply (drule spec)
apply (erule mp [THEN spec], blast)
done

lemma lemma2: "(ALL Q x. x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q)) ==> wf r"
apply (unfold wf_def, clarify)
apply (drule_tac x = "{x. ~ P x}" in spec, blast)
done

lemma wf_eq_minimal: "wf r = (ALL Q x. x:Q --> (EX z:Q. ALL y. (y,z):r --> y~:Q))"
by (blast intro!: lemma1 lemma2)

subsubsection{*Other simple well-foundedness results*}


text{*Well-foundedness of subsets*}
lemma wf_subset: "[| wf(r);  p<=r |] ==> wf(p)"
apply (simp (no_asm_use) add: wf_eq_minimal)
apply fast
done

text{*Well-foundedness of the empty relation*}
lemma wf_empty [iff]: "wf({})"
by (simp add: wf_def)

text{*Well-foundedness of insert*}
lemma wf_insert [iff]: "wf(insert (y,x) r) = (wf(r) & (x,y) ~: r^*)"
apply (rule iffI)
 apply (blast elim: wf_trancl [THEN wf_irrefl]
              intro: rtrancl_into_trancl1 wf_subset 
                     rtrancl_mono [THEN [2] rev_subsetD])
apply (simp add: wf_eq_minimal, safe)
apply (rule allE, assumption, erule impE, blast) 
apply (erule bexE)
apply (rename_tac "a", case_tac "a = x")
 prefer 2
apply blast 
apply (case_tac "y:Q")
 prefer 2 apply blast
apply (rule_tac x = "{z. z:Q & (z,y) : r^*}" in allE)
 apply assumption
apply (erule_tac V = "ALL Q. (EX x. x : Q) --> ?P Q" in thin_rl) 
  --{*essential for speed*}
txt{*Blast with new substOccur fails*}
apply (fast intro: converse_rtrancl_into_rtrancl)
done

text{*Well-foundedness of image*}
lemma wf_prod_fun_image: "[| wf r; inj f |] ==> wf(prod_fun f f ` r)"
apply (simp only: wf_eq_minimal, clarify)
apply (case_tac "EX p. f p : Q")
apply (erule_tac x = "{p. f p : Q}" in allE)
apply (fast dest: inj_onD, blast)
done


subsubsection{*Well-Foundedness Results for Unions*}

text{*Well-foundedness of indexed union with disjoint domains and ranges*}

lemma wf_UN: "[| ALL i:I. wf(r i);  
         ALL i:I. ALL j:I. r i ~= r j --> Domain(r i) Int Range(r j) = {}  
      |] ==> wf(UN i:I. r i)"
apply (simp only: wf_eq_minimal, clarify)
apply (rename_tac A a, case_tac "EX i:I. EX a:A. EX b:A. (b,a) : r i")
 prefer 2
 apply force 
apply clarify
apply (drule bspec, assumption)  
apply (erule_tac x="{a. a:A & (EX b:A. (b,a) : r i) }" in allE)
apply (blast elim!: allE)  
done

lemma wf_Union: 
 "[| ALL r:R. wf r;  
     ALL r:R. ALL s:R. r ~= s --> Domain r Int Range s = {}  
  |] ==> wf(Union R)"
apply (simp add: Union_def)
apply (blast intro: wf_UN)
done

(*Intuition: we find an (R u S)-min element of a nonempty subset A
             by case distinction.
  1. There is a step a -R-> b with a,b : A.
     Pick an R-min element z of the (nonempty) set {a:A | EX b:A. a -R-> b}.
     By definition, there is z':A s.t. z -R-> z'. Because z is R-min in the
     subset, z' must be R-min in A. Because z' has an R-predecessor, it cannot
     have an S-successor and is thus S-min in A as well.
  2. There is no such step.
     Pick an S-min element of A. In this case it must be an R-min
     element of A as well.

*)
lemma wf_Un:
     "[| wf r; wf s; Domain r Int Range s = {} |] ==> wf(r Un s)"
apply (simp only: wf_eq_minimal, clarify) 
apply (rename_tac A a)
apply (case_tac "EX a:A. EX b:A. (b,a) : r") 
 prefer 2
 apply simp
 apply (drule_tac x=A in spec)+
 apply blast 
apply (erule_tac x="{a. a:A & (EX b:A. (b,a) : r) }" in allE)+
apply (blast elim!: allE)  
done

subsubsection {*acyclic*}

lemma acyclicI: "ALL x. (x, x) ~: r^+ ==> acyclic r"
by (simp add: acyclic_def)

lemma wf_acyclic: "wf r ==> acyclic r"
apply (simp add: acyclic_def)
apply (blast elim: wf_trancl [THEN wf_irrefl])
done

lemma acyclic_insert [iff]:
     "acyclic(insert (y,x) r) = (acyclic r & (x,y) ~: r^*)"
apply (simp add: acyclic_def trancl_insert)
apply (blast intro: rtrancl_trans)
done

lemma acyclic_converse [iff]: "acyclic(r^-1) = acyclic r"
by (simp add: acyclic_def trancl_converse)

lemma acyclic_impl_antisym_rtrancl: "acyclic r ==> antisym(r^*)"
apply (simp add: acyclic_def antisym_def)
apply (blast elim: rtranclE intro: rtrancl_into_trancl1 rtrancl_trancl_trancl)
done

(* Other direction:
acyclic = no loops
antisym = only self loops
Goalw [acyclic_def,antisym_def] "antisym( r^* ) ==> acyclic(r - Id)
==> antisym( r^* ) = acyclic(r - Id)";
*)

lemma acyclic_subset: "[| acyclic s; r <= s |] ==> acyclic r"
apply (simp add: acyclic_def)
apply (blast intro: trancl_mono)
done


subsection{*Well-Founded Recursion*}

text{*cut*}

lemma cuts_eq: "(cut f r x = cut g r x) = (ALL y. (y,x):r --> f(y)=g(y))"
by (simp add: expand_fun_eq cut_def)

lemma cut_apply: "(x,a):r ==> (cut f r a)(x) = f(x)"
by (simp add: cut_def)

text{*Inductive characterization of wfrec combinator; for details see:  
John Harrison, "Inductive definitions: automation and application"*}

lemma wfrec_unique: "[| adm_wf R F; wf R |] ==> EX! y. (x, y) : wfrec_rel R F"
apply (simp add: adm_wf_def)
apply (erule_tac a=x in wf_induct) 
apply (rule ex1I)
apply (rule_tac g = "%x. THE y. (x, y) : wfrec_rel R F" in wfrec_rel.wfrecI)
apply (fast dest!: theI')
apply (erule wfrec_rel.cases, simp)
apply (erule allE, erule allE, erule allE, erule mp)
apply (fast intro: the_equality [symmetric])
done

lemma adm_lemma: "adm_wf R (%f x. F (cut f R x) x)"
apply (simp add: adm_wf_def)
apply (intro strip)
apply (rule cuts_eq [THEN iffD2, THEN subst], assumption)
apply (rule refl)
done

lemma wfrec: "wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a"
apply (simp add: wfrec_def)
apply (rule adm_lemma [THEN wfrec_unique, THEN the1_equality], assumption)
apply (rule wfrec_rel.wfrecI)
apply (intro strip)
apply (erule adm_lemma [THEN wfrec_unique, THEN theI'])
done


text{** This form avoids giant explosions in proofs.  NOTE USE OF ==*}
lemma def_wfrec: "[| f==wfrec r H;  wf(r) |] ==> f(a) = H (cut f r a) a"
apply auto
apply (blast intro: wfrec)
done


subsection{*Variants for TFL: the Recdef Package*}

lemma tfl_wf_induct: "ALL R. wf R -->  
       (ALL P. (ALL x. (ALL y. (y,x):R --> P y) --> P x) --> (ALL x. P x))"
apply clarify
apply (rule_tac r = R and P = P and a = x in wf_induct, assumption, blast)
done

lemma tfl_cut_apply: "ALL f R. (x,a):R --> (cut f R a)(x) = f(x)"
apply clarify
apply (rule cut_apply, assumption)
done

lemma tfl_wfrec:
     "ALL M R f. (f=wfrec R M) --> wf R --> (ALL x. f x = M (cut f R x) x)"
apply clarify
apply (erule wfrec)
done

subsection {*LEAST and wellorderings*}

text{* See also @{text wf_linord_ex_has_least} and its consequences in
 @{text Wellfounded_Relations.ML}*}

lemma wellorder_Least_lemma [rule_format]:
     "P (k::'a::wellorder) --> P (LEAST x. P(x)) & (LEAST x. P(x)) <= k"
apply (rule_tac a = k in wf [THEN wf_induct])
apply (rule impI)
apply (rule classical)
apply (rule_tac s = x in Least_equality [THEN ssubst], auto)
apply (auto simp add: linorder_not_less [symmetric])
done

lemmas LeastI   = wellorder_Least_lemma [THEN conjunct1, standard]
lemmas Least_le = wellorder_Least_lemma [THEN conjunct2, standard]

-- "The following 3 lemmas are due to Brian Huffman"
lemma LeastI_ex: "EX x::'a::wellorder. P x ==> P (Least P)"
apply (erule exE)
apply (erule LeastI)
done

lemma LeastI2:
  "[| P (a::'a::wellorder); !!x. P x ==> Q x |] ==> Q (Least P)"
by (blast intro: LeastI)

lemma LeastI2_ex:
  "[| EX a::'a::wellorder. P a; !!x. P x ==> Q x |] ==> Q (Least P)"
by (blast intro: LeastI_ex)

lemma not_less_Least: "[| k < (LEAST x. P x) |] ==> ~P (k::'a::wellorder)"
apply (simp (no_asm_use) add: linorder_not_le [symmetric])
apply (erule contrapos_nn)
apply (erule Least_le)
done

ML
{*
val wf_def = thm "wf_def";
val wfUNIVI = thm "wfUNIVI";
val wfI = thm "wfI";
val wf_induct = thm "wf_induct";
val wf_not_sym = thm "wf_not_sym";
val wf_asym = thm "wf_asym";
val wf_not_refl = thm "wf_not_refl";
val wf_irrefl = thm "wf_irrefl";
val wf_trancl = thm "wf_trancl";
val wf_converse_trancl = thm "wf_converse_trancl";
val wf_eq_minimal = thm "wf_eq_minimal";
val wf_subset = thm "wf_subset";
val wf_empty = thm "wf_empty";
val wf_insert = thm "wf_insert";
val wf_UN = thm "wf_UN";
val wf_Union = thm "wf_Union";
val wf_Un = thm "wf_Un";
val wf_prod_fun_image = thm "wf_prod_fun_image";
val acyclicI = thm "acyclicI";
val wf_acyclic = thm "wf_acyclic";
val acyclic_insert = thm "acyclic_insert";
val acyclic_converse = thm "acyclic_converse";
val acyclic_impl_antisym_rtrancl = thm "acyclic_impl_antisym_rtrancl";
val acyclic_subset = thm "acyclic_subset";
val cuts_eq = thm "cuts_eq";
val cut_apply = thm "cut_apply";
val wfrec_unique = thm "wfrec_unique";
val wfrec = thm "wfrec";
val def_wfrec = thm "def_wfrec";
val tfl_wf_induct = thm "tfl_wf_induct";
val tfl_cut_apply = thm "tfl_cut_apply";
val tfl_wfrec = thm "tfl_wfrec";
val LeastI = thm "LeastI";
val Least_le = thm "Least_le";
val not_less_Least = thm "not_less_Least";
*}

end
