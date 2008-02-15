(*  ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge
*)

header {*Well-founded Recursion*}

theory Wellfounded_Recursion
imports Transitive_Closure Nat
uses ("Tools/function_package/size.ML")
begin

inductive
  wfrec_rel :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b => bool"
  for R :: "('a * 'a) set"
  and F :: "('a => 'b) => 'a => 'b"
where
  wfrecI: "ALL z. (z, x) : R --> wfrec_rel R F z (g z) ==>
            wfrec_rel R F x (F g x)"

constdefs
  wf         :: "('a * 'a)set => bool"
  "wf(r) == (!P. (!x. (!y. (y,x):r --> P(y)) --> P(x)) --> (!x. P(x)))"

  wfP :: "('a => 'a => bool) => bool"
  "wfP r == wf {(x, y). r x y}"

  acyclic :: "('a*'a)set => bool"
  "acyclic r == !x. (x,x) ~: r^+"

  cut        :: "('a => 'b) => ('a * 'a)set => 'a => 'a => 'b"
  "cut f r x == (%y. if (y,x):r then f y else arbitrary)"

  adm_wf :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => bool"
  "adm_wf R F == ALL f g x.
     (ALL z. (z, x) : R --> f z = g z) --> F f x = F g x"

  wfrec :: "('a * 'a) set => (('a => 'b) => 'a => 'b) => 'a => 'b"
  [code func del]: "wfrec R F == %x. THE y. wfrec_rel R (%f x. F (cut f R x) x) x y"

abbreviation acyclicP :: "('a => 'a => bool) => bool" where
  "acyclicP r == acyclic {(x, y). r x y}"

class wellorder = linorder +
  assumes wf: "wf {(x, y). x < y}"


lemma wfP_wf_eq [pred_set_conv]: "wfP (\<lambda>x y. (x, y) \<in> r) = wf r"
  by (simp add: wfP_def)

lemma wfUNIVI: 
   "(!!P x. (ALL x. (ALL y. (y,x) : r --> P(y)) --> P(x)) ==> P(x)) ==> wf(r)"
by (unfold wf_def, blast)

lemmas wfPUNIVI = wfUNIVI [to_pred]

text{*Restriction to domain @{term A} and range @{term B}.  If @{term r} is
    well-founded over their intersection, then @{term "wf r"}*}
lemma wfI: 
 "[| r \<subseteq> A <*> B; 
     !!x P. [|\<forall>x. (\<forall>y. (y,x) : r --> P y) --> P x;  x : A; x : B |] ==> P x |]
  ==>  wf r"
by (unfold wf_def, blast)

lemma wf_induct: 
    "[| wf(r);           
        !!x.[| ALL y. (y,x): r --> P(y) |] ==> P(x)  
     |]  ==>  P(a)"
by (unfold wf_def, blast)

lemmas wfP_induct = wf_induct [to_pred]

lemmas wf_induct_rule = wf_induct [rule_format, consumes 1, case_names less, induct set: wf]

lemmas wfP_induct_rule = wf_induct_rule [to_pred, induct set: wfP]

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

lemmas wfP_trancl = wf_trancl [to_pred]

lemma wf_converse_trancl: "wf (r^-1) ==> wf ((r^+)^-1)"
apply (subst trancl_converse [symmetric])
apply (erule wf_trancl)
done


subsubsection{*Other simple well-foundedness results*}


text{*Minimal-element characterization of well-foundedness*}
lemma wf_eq_minimal: "wf r = (\<forall>Q x. x\<in>Q --> (\<exists>z\<in>Q. \<forall>y. (y,z)\<in>r --> y\<notin>Q))"
proof (intro iffI strip)
  fix Q::"'a set" and x
  assume "wf r" and "x \<in> Q"
  thus "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q"
    by (unfold wf_def, 
        blast dest: spec [of _ "%x. x\<in>Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y,z) \<in> r \<longrightarrow> y\<notin>Q)"]) 
next
  assume 1: "\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q)"
  show "wf r"
  proof (rule wfUNIVI)
    fix P :: "'a \<Rightarrow> bool" and x
    assume 2: "\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x"
    let ?Q = "{x. \<not> P x}"
    have "x \<in> ?Q \<longrightarrow> (\<exists>z\<in>?Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> ?Q)"
      by (rule 1 [THEN spec, THEN spec])
    hence "\<not> P x \<longrightarrow> (\<exists>z. \<not> P z \<and> (\<forall>y. (y, z) \<in> r \<longrightarrow> P y))" by simp
    with 2 have "\<not> P x \<longrightarrow> (\<exists>z. \<not> P z \<and> P z)" by fast
    thus "P x" by simp
  qed
qed

lemma wfE_min: 
  assumes p:"wf R" "x \<in> Q"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using p
  unfolding wf_eq_minimal
  by blast

lemma wfI_min:
  "(\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q)
  \<Longrightarrow> wf R"
  unfolding wf_eq_minimal
  by blast

lemmas wfP_eq_minimal = wf_eq_minimal [to_pred]

text{*Well-foundedness of subsets*}
lemma wf_subset: "[| wf(r);  p<=r |] ==> wf(p)"
apply (simp (no_asm_use) add: wf_eq_minimal)
apply fast
done

lemmas wfP_subset = wf_subset [to_pred]

text{*Well-foundedness of the empty relation*}
lemma wf_empty [iff]: "wf({})"
by (simp add: wf_def)

lemmas wfP_empty [iff] =
  wf_empty [to_pred bot_empty_eq2, simplified bot_fun_eq bot_bool_eq]

lemma wf_Int1: "wf r ==> wf (r Int r')"
by (erule wf_subset, rule Int_lower1)

lemma wf_Int2: "wf r ==> wf (r' Int r)"
by (erule wf_subset, rule Int_lower2)

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

lemma wf_union_compatible:
  assumes "wf R" "wf S"
  assumes comp: "S O R \<subseteq> R"
  shows "wf (R \<union> S)"
proof (rule wfI_min)
  fix x :: 'a and Q 
  let ?Q' = "{ x\<in>Q. \<forall>y. (y,x)\<in>R \<longrightarrow> y \<notin> Q }"
  assume "x \<in> Q"
  obtain a where "a \<in> ?Q'" 
    by (rule wfE_min[OF `wf R` `x \<in> Q`]) blast
  with `wf S`
  obtain z where "z \<in> ?Q'" and zmin: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> ?Q'" by (erule wfE_min)
  { 
    fix y assume ySz: "(y, z) \<in> S"
    then have "y \<notin> ?Q'" by (rule zmin)

    have "y \<notin> Q"
    proof 
      assume "y \<in> Q"
      with `y \<notin> ?Q'` 
      obtain w where wRy: "(w, y) \<in> R" and "w \<in> Q" by auto
      from wRy ySz have "(w, z) \<in> S O R" by (rule rel_compI)
      with comp have "(w, z) \<in> R" ..
      with `z \<in> ?Q'` have "w \<notin> Q" by blast 
      from this `w \<in> Q` show False ..
    qed
  }
  with `z \<in> ?Q'`
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<union> S \<longrightarrow> y \<notin> Q" by blast
qed

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

lemmas wfP_SUP = wf_UN [where I=UNIV and r="\<lambda>i. {(x, y). r i x y}",
  to_pred SUP_UN_eq2 bot_empty_eq, simplified, standard]

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
using wf_union_compatible[of s r] 
by (auto simp: Un_ac)

lemma wf_union_merge: 
  "wf (R \<union> S) = wf (R O R \<union> R O S \<union> S)" (is "wf ?A = wf ?B")
proof
  assume "wf ?A"
  with wf_trancl have wfT: "wf (?A^+)" .
  moreover have "?B \<subseteq> ?A^+"
    by  (subst trancl_unfold, subst trancl_unfold) blast
  ultimately show "wf ?B" by (rule wf_subset)
next
  assume "wf ?B"

  show "wf ?A"
  proof (rule wfI_min)
    fix Q :: "'a set" and x 
    assume "x \<in> Q"

    with `wf ?B`
    obtain z where "z \<in> Q" and "\<And>y. (y, z) \<in> ?B \<Longrightarrow> y \<notin> Q" 
      by (erule wfE_min)
    hence A1: "\<And>y. (y, z) \<in> R O R \<Longrightarrow> y \<notin> Q"
      and A2: "\<And>y. (y, z) \<in> R O S \<Longrightarrow> y \<notin> Q"
      and A3: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> Q"
      by auto
    
    show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?A \<longrightarrow> y \<notin> Q"
    proof (cases "\<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q")
      case True
      with `z \<in> Q` A3 show ?thesis by blast
    next
      case False 
      then obtain z' where "z'\<in>Q" "(z', z) \<in> R" by blast

      have "\<forall>y. (y, z') \<in> ?A \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y assume "(y, z') \<in> ?A"
        thus "y \<notin> Q"
        proof
          assume "(y, z') \<in> R" 
          hence "(y, z) \<in> R O R" using `(z', z) \<in> R` ..
          with A1 show "y \<notin> Q" .
        next
          assume "(y, z') \<in> S" 
          hence "(y, z) \<in> R O S" using  `(z', z) \<in> R` ..
          with A2 show "y \<notin> Q" .
        qed
      qed
      with `z' \<in> Q` show ?thesis ..
    qed
  qed
qed

lemma wf_comp_self: "wf R = wf (R O R)" (* special case *)
  by (fact wf_union_merge[where S = "{}", simplified])

subsubsection {*acyclic*}

lemma acyclicI: "ALL x. (x, x) ~: r^+ ==> acyclic r"
by (simp add: acyclic_def)

lemma wf_acyclic: "wf r ==> acyclic r"
apply (simp add: acyclic_def)
apply (blast elim: wf_trancl [THEN wf_irrefl])
done

lemmas wfP_acyclicP = wf_acyclic [to_pred]

lemma acyclic_insert [iff]:
     "acyclic(insert (y,x) r) = (acyclic r & (x,y) ~: r^*)"
apply (simp add: acyclic_def trancl_insert)
apply (blast intro: rtrancl_trans)
done

lemma acyclic_converse [iff]: "acyclic(r^-1) = acyclic r"
by (simp add: acyclic_def trancl_converse)

lemmas acyclicP_converse [iff] = acyclic_converse [to_pred]

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

lemma wfrec_unique: "[| adm_wf R F; wf R |] ==> EX! y. wfrec_rel R F x y"
apply (simp add: adm_wf_def)
apply (erule_tac a=x in wf_induct) 
apply (rule ex1I)
apply (rule_tac g = "%x. THE y. wfrec_rel R F x y" in wfrec_rel.wfrecI)
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


subsection {* Code generator setup *}

consts_code
  "wfrec"   ("\<module>wfrec?")
attach {*
fun wfrec f x = f (wfrec f) x;
*}


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

subsection {* @{typ nat} is well-founded *}

lemma less_nat_rel: "op < = (\<lambda>m n. n = Suc m)^++"
proof (rule ext, rule ext, rule iffI)
  fix n m :: nat
  assume "m < n"
  then show "(\<lambda>m n. n = Suc m)^++ m n"
  proof (induct n)
    case 0 then show ?case by auto
  next
    case (Suc n) then show ?case
    by (auto simp add: less_Suc_eq_le le_less intro: tranclp.trancl_into_trancl)
  qed
next
  fix n m :: nat
  assume "(\<lambda>m n. n = Suc m)^++ m n"
  then show "m < n"
    by (induct n)
      (simp_all add: less_Suc_eq_le reflexive le_less)
qed

definition
  pred_nat :: "(nat * nat) set" where
  "pred_nat = {(m, n). n = Suc m}"

definition
  less_than :: "(nat * nat)set" where
  "less_than = pred_nat^+"

lemma less_eq: "(m, n) \<in> pred_nat^+ \<longleftrightarrow> m < n"
  unfolding less_nat_rel pred_nat_def trancl_def by simp

lemma pred_nat_trancl_eq_le:
  "(m, n) \<in> pred_nat^* \<longleftrightarrow> m \<le> n"
  unfolding less_eq rtrancl_eq_or_trancl by auto

lemma wf_pred_nat: "wf pred_nat"
  apply (unfold wf_def pred_nat_def, clarify)
  apply (induct_tac x, blast+)
  done

lemma wf_less_than [iff]: "wf less_than"
  by (simp add: less_than_def wf_pred_nat [THEN wf_trancl])

lemma trans_less_than [iff]: "trans less_than"
  by (simp add: less_than_def trans_trancl)

lemma less_than_iff [iff]: "((x,y): less_than) = (x<y)"
  by (simp add: less_than_def less_eq)

lemma wf_less: "wf {(x, y::nat). x < y}"
  using wf_less_than by (simp add: less_than_def less_eq [symmetric])

text {* Complete induction, aka course-of-values induction *}
lemma nat_less_induct:
  assumes prem: "!!n. \<forall>m::nat. m < n --> P m ==> P n" shows "P n"
  apply (induct n rule: wf_induct [OF wf_pred_nat [THEN wf_trancl]])
  apply (rule prem)
  apply (unfold less_eq [symmetric], assumption)
  done

lemmas less_induct = nat_less_induct [rule_format, case_names less]

text {* Type @{typ nat} is a wellfounded order *}

instance nat :: wellorder
  by intro_classes
    (assumption |
      rule le_refl le_trans le_anti_sym nat_less_le nat_le_linear wf_less)+

lemma nat_induct2: "[|P 0; P (Suc 0); !!k. P k ==> P (Suc (Suc k))|] ==> P n"
  apply (rule nat_less_induct)
  apply (case_tac n)
  apply (case_tac [2] nat)
  apply (blast intro: less_trans)+
  done

text {* The method of infinite descent, frequently used in number theory.
Provided by Roelof Oosterhuis.
$P(n)$ is true for all $n\in\mathbb{N}$ if
\begin{itemize}
  \item case ``0'': given $n=0$ prove $P(n)$,
  \item case ``smaller'': given $n>0$ and $\neg P(n)$ prove there exists
        a smaller integer $m$ such that $\neg P(m)$.
\end{itemize} *}

lemma infinite_descent0[case_names 0 smaller]: 
  "\<lbrakk> P 0; !!n. n>0 \<Longrightarrow> \<not> P n \<Longrightarrow> (\<exists>m::nat. m < n \<and> \<not>P m) \<rbrakk> \<Longrightarrow> P n"
by (induct n rule: less_induct, case_tac "n>0", auto)

text{* A compact version without explicit base case: *}
lemma infinite_descent:
  "\<lbrakk> !!n::nat. \<not> P n \<Longrightarrow>  \<exists>m<n. \<not>  P m \<rbrakk> \<Longrightarrow>  P n"
by (induct n rule: less_induct, auto)

text {* Infinite descent using a mapping to $\mathbb{N}$:
$P(x)$ is true for all $x\in D$ if there exists a $V: D \to \mathbb{N}$ and
\begin{itemize}
\item case ``0'': given $V(x)=0$ prove $P(x)$,
\item case ``smaller'': given $V(x)>0$ and $\neg P(x)$ prove there exists a $y \in D$ such that $V(y)<V(x)$ and $~\neg P(y)$.
\end{itemize}
NB: the proof also shows how to use the previous lemma. *}
corollary infinite_descent0_measure [case_names 0 smaller]:
  assumes A0: "!!x. V x = (0::nat) \<Longrightarrow> P x"
    and   A1: "!!x. V x > 0 \<Longrightarrow> \<not>P x \<Longrightarrow> (\<exists>y. V y < V x \<and> \<not>P y)"
  shows "P x"
proof -
  obtain n where "n = V x" by auto
  moreover have "\<And>x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent0)
    case 0 -- "i.e. $V(x) = 0$"
    with A0 show "P x" by auto
  next -- "now $n>0$ and $P(x)$ does not hold for some $x$ with $V(x)=n$"
    case (smaller n)
    then obtain x where vxn: "V x = n " and "V x > 0 \<and> \<not> P x" by auto
    with A1 obtain y where "V y < V x \<and> \<not> P y" by auto
    with vxn obtain m where "m = V y \<and> m<n \<and> \<not> P y" by auto
    thus ?case by auto
  qed
  ultimately show "P x" by auto
qed

text{* Again, without explicit base case: *}
lemma infinite_descent_measure:
assumes "!!x. \<not> P x \<Longrightarrow> \<exists>y. (V::'a\<Rightarrow>nat) y < V x \<and> \<not> P y" shows "P x"
proof -
  from assms obtain n where "n = V x" by auto
  moreover have "!!x. V x = n \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent, auto)
    fix x assume "\<not> P x"
    with assms show "\<exists>m < V x. \<exists>y. V y = m \<and> \<not> P y" by auto
  qed
  ultimately show "P x" by auto
qed

text {* @{text LEAST} theorems for type @{typ nat}*}

lemma Least_Suc:
     "[| P n; ~ P 0 |] ==> (LEAST n. P n) = Suc (LEAST m. P(Suc m))"
  apply (case_tac "n", auto)
  apply (frule LeastI)
  apply (drule_tac P = "%x. P (Suc x) " in LeastI)
  apply (subgoal_tac " (LEAST x. P x) \<le> Suc (LEAST x. P (Suc x))")
  apply (erule_tac [2] Least_le)
  apply (case_tac "LEAST x. P x", auto)
  apply (drule_tac P = "%x. P (Suc x) " in Least_le)
  apply (blast intro: order_antisym)
  done

lemma Least_Suc2:
   "[|P n; Q m; ~P 0; !k. P (Suc k) = Q k|] ==> Least P = Suc (Least Q)"
by (erule (1) Least_Suc [THEN ssubst], simp)


subsection {* size of a datatype value *}

use "Tools/function_package/size.ML"

setup Size.setup

lemma nat_size [simp, code func]: "size (n\<Colon>nat) = n"
  by (induct n) simp_all

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
