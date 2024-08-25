(*  Title:      ZF/func.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section\<open>Functions, Function Spaces, Lambda-Abstraction\<close>

theory func imports equalities Sum begin

subsection\<open>The Pi Operator: Dependent Function Space\<close>

lemma subset_Sigma_imp_relation: "r \<subseteq> Sigma(A,B) \<Longrightarrow> relation(r)"
by (simp add: relation_def, blast)

lemma relation_converse_converse [simp]:
     "relation(r) \<Longrightarrow> converse(converse(r)) = r"
by (simp add: relation_def, blast)

lemma relation_restrict [simp]:  "relation(restrict(r,A))"
by (simp add: restrict_def relation_def, blast)

lemma Pi_iff:
    "f \<in> Pi(A,B) \<longleftrightarrow> function(f) \<and> f<=Sigma(A,B) \<and> A<=domain(f)"
by (unfold Pi_def, blast)

(*For upward compatibility with the former definition*)
lemma Pi_iff_old:
    "f \<in> Pi(A,B) \<longleftrightarrow> f<=Sigma(A,B) \<and> (\<forall>x\<in>A. \<exists>!y. \<langle>x,y\<rangle>: f)"
by (unfold Pi_def function_def, blast)

lemma fun_is_function: "f \<in> Pi(A,B) \<Longrightarrow> function(f)"
by (simp only: Pi_iff)

lemma function_imp_Pi:
     "\<lbrakk>function(f); relation(f)\<rbrakk> \<Longrightarrow> f \<in> domain(f) -> range(f)"
by (simp add: Pi_iff relation_def, blast)

lemma functionI:
     "\<lbrakk>\<And>x y y'. \<lbrakk>\<langle>x,y\<rangle>:r; <x,y'>:r\<rbrakk> \<Longrightarrow> y=y'\<rbrakk> \<Longrightarrow> function(r)"
by (simp add: function_def, blast)

(*Functions are relations*)
lemma fun_is_rel: "f \<in> Pi(A,B) \<Longrightarrow> f \<subseteq> Sigma(A,B)"
by (unfold Pi_def, blast)

lemma Pi_cong:
    "\<lbrakk>A=A';  \<And>x. x \<in> A' \<Longrightarrow> B(x)=B'(x)\<rbrakk> \<Longrightarrow> Pi(A,B) = Pi(A',B')"
by (simp add: Pi_def cong add: Sigma_cong)

(*Sigma_cong, Pi_cong NOT given to Addcongs: they cause
  flex-flex pairs and the "Check your prover" error.  Most
  Sigmas and Pis are abbreviated as * or -> *)

(*Weakening one function type to another; see also Pi_type*)
lemma fun_weaken_type: "\<lbrakk>f \<in> A->B;  B<=D\<rbrakk> \<Longrightarrow> f \<in> A->D"
by (unfold Pi_def, best)

subsection\<open>Function Application\<close>

lemma apply_equality2: "\<lbrakk>\<langle>a,b\<rangle>: f;  \<langle>a,c\<rangle>: f;  f \<in> Pi(A,B)\<rbrakk> \<Longrightarrow> b=c"
by (unfold Pi_def function_def, blast)

lemma function_apply_equality: "\<lbrakk>\<langle>a,b\<rangle>: f;  function(f)\<rbrakk> \<Longrightarrow> f`a = b"
by (unfold apply_def function_def, blast)

lemma apply_equality: "\<lbrakk>\<langle>a,b\<rangle>: f;  f \<in> Pi(A,B)\<rbrakk> \<Longrightarrow> f`a = b"
  unfolding Pi_def
apply (blast intro: function_apply_equality)
done

(*Applying a function outside its domain yields 0*)
lemma apply_0: "a \<notin> domain(f) \<Longrightarrow> f`a = 0"
by (unfold apply_def, blast)

lemma Pi_memberD: "\<lbrakk>f \<in> Pi(A,B);  c \<in> f\<rbrakk> \<Longrightarrow> \<exists>x\<in>A.  c = <x,f`x>"
apply (frule fun_is_rel)
apply (blast dest: apply_equality)
done

lemma function_apply_Pair: "\<lbrakk>function(f);  a \<in> domain(f)\<rbrakk> \<Longrightarrow> <a,f`a>: f"
apply (simp add: function_def, clarify)
apply (subgoal_tac "f`a = y", blast)
apply (simp add: apply_def, blast)
done

lemma apply_Pair: "\<lbrakk>f \<in> Pi(A,B);  a \<in> A\<rbrakk> \<Longrightarrow> <a,f`a>: f"
apply (simp add: Pi_iff)
apply (blast intro: function_apply_Pair)
done

(*Conclusion is flexible -- use rule_tac or else apply_funtype below!*)
lemma apply_type [TC]: "\<lbrakk>f \<in> Pi(A,B);  a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> B(a)"
by (blast intro: apply_Pair dest: fun_is_rel)

(*This version is acceptable to the simplifier*)
lemma apply_funtype: "\<lbrakk>f \<in> A->B;  a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> B"
by (blast dest: apply_type)

lemma apply_iff: "f \<in> Pi(A,B) \<Longrightarrow> \<langle>a,b\<rangle>: f \<longleftrightarrow> a \<in> A \<and> f`a = b"
apply (frule fun_is_rel)
apply (blast intro!: apply_Pair apply_equality)
done

(*Refining one Pi type to another*)
lemma Pi_type: "\<lbrakk>f \<in> Pi(A,C);  \<And>x. x \<in> A \<Longrightarrow> f`x \<in> B(x)\<rbrakk> \<Longrightarrow> f \<in> Pi(A,B)"
apply (simp only: Pi_iff)
apply (blast dest: function_apply_equality)
done

(*Such functions arise in non-standard datatypes, ZF/ex/Ntree for instance*)
lemma Pi_Collect_iff:
     "(f \<in> Pi(A, \<lambda>x. {y \<in> B(x). P(x,y)}))
      \<longleftrightarrow>  f \<in> Pi(A,B) \<and> (\<forall>x\<in>A. P(x, f`x))"
by (blast intro: Pi_type dest: apply_type)

lemma Pi_weaken_type:
        "\<lbrakk>f \<in> Pi(A,B);  \<And>x. x \<in> A \<Longrightarrow> B(x)<=C(x)\<rbrakk> \<Longrightarrow> f \<in> Pi(A,C)"
by (blast intro: Pi_type dest: apply_type)


(** Elimination of membership in a function **)

lemma domain_type: "\<lbrakk>\<langle>a,b\<rangle> \<in> f;  f \<in> Pi(A,B)\<rbrakk> \<Longrightarrow> a \<in> A"
by (blast dest: fun_is_rel)

lemma range_type: "\<lbrakk>\<langle>a,b\<rangle> \<in> f;  f \<in> Pi(A,B)\<rbrakk> \<Longrightarrow> b \<in> B(a)"
by (blast dest: fun_is_rel)

lemma Pair_mem_PiD: "\<lbrakk>\<langle>a,b\<rangle>: f;  f \<in> Pi(A,B)\<rbrakk> \<Longrightarrow> a \<in> A \<and> b \<in> B(a) \<and> f`a = b"
by (blast intro: domain_type range_type apply_equality)

subsection\<open>Lambda Abstraction\<close>

lemma lamI: "a \<in> A \<Longrightarrow> <a,b(a)> \<in> (\<lambda>x\<in>A. b(x))"
  unfolding lam_def
apply (erule RepFunI)
done

lemma lamE:
    "\<lbrakk>p: (\<lambda>x\<in>A. b(x));  \<And>x.\<lbrakk>x \<in> A; p=<x,b(x)>\<rbrakk> \<Longrightarrow> P
\<rbrakk> \<Longrightarrow>  P"
by (simp add: lam_def, blast)

lemma lamD: "\<lbrakk>\<langle>a,c\<rangle>: (\<lambda>x\<in>A. b(x))\<rbrakk> \<Longrightarrow> c = b(a)"
by (simp add: lam_def)

lemma lam_type [TC]:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> b(x): B(x)\<rbrakk> \<Longrightarrow> (\<lambda>x\<in>A. b(x)) \<in> Pi(A,B)"
by (simp add: lam_def Pi_def function_def, blast)

lemma lam_funtype: "(\<lambda>x\<in>A. b(x)) \<in> A -> {b(x). x \<in> A}"
by (blast intro: lam_type)

lemma function_lam: "function (\<lambda>x\<in>A. b(x))"
by (simp add: function_def lam_def)

lemma relation_lam: "relation (\<lambda>x\<in>A. b(x))"
by (simp add: relation_def lam_def)

lemma beta_if [simp]: "(\<lambda>x\<in>A. b(x)) ` a = (if a \<in> A then b(a) else 0)"
by (simp add: apply_def lam_def, blast)

lemma beta: "a \<in> A \<Longrightarrow> (\<lambda>x\<in>A. b(x)) ` a = b(a)"
by (simp add: apply_def lam_def, blast)

lemma lam_empty [simp]: "(\<lambda>x\<in>0. b(x)) = 0"
by (simp add: lam_def)

lemma domain_lam [simp]: "domain(Lambda(A,b)) = A"
by (simp add: lam_def, blast)

(*congruence rule for lambda abstraction*)
lemma lam_cong [cong]:
    "\<lbrakk>A=A';  \<And>x. x \<in> A' \<Longrightarrow> b(x)=b'(x)\<rbrakk> \<Longrightarrow> Lambda(A,b) = Lambda(A',b')"
by (simp only: lam_def cong add: RepFun_cong)

lemma lam_theI:
    "(\<And>x. x \<in> A \<Longrightarrow> \<exists>!y. Q(x,y)) \<Longrightarrow> \<exists>f. \<forall>x\<in>A. Q(x, f`x)"
apply (rule_tac x = "\<lambda>x\<in>A. THE y. Q (x,y)" in exI)
apply simp
apply (blast intro: theI)
done

lemma lam_eqE: "\<lbrakk>(\<lambda>x\<in>A. f(x)) = (\<lambda>x\<in>A. g(x));  a \<in> A\<rbrakk> \<Longrightarrow> f(a)=g(a)"
by (fast intro!: lamI elim: equalityE lamE)


(*Empty function spaces*)
lemma Pi_empty1 [simp]: "Pi(0,A) = {0}"
by (unfold Pi_def function_def, blast)

(*The singleton function*)
lemma singleton_fun [simp]: "{\<langle>a,b\<rangle>} \<in> {a} -> {b}"
by (unfold Pi_def function_def, blast)

lemma Pi_empty2 [simp]: "(A->0) = (if A=0 then {0} else 0)"
by (unfold Pi_def function_def, force)

lemma  fun_space_empty_iff [iff]: "(A->X)=0 \<longleftrightarrow> X=0 \<and> (A \<noteq> 0)"
apply auto
apply (fast intro!: equals0I intro: lam_type)
done


subsection\<open>Extensionality\<close>

(*Semi-extensionality!*)

lemma fun_subset:
    "\<lbrakk>f \<in> Pi(A,B);  g \<in> Pi(C,D);  A<=C;
        \<And>x. x \<in> A \<Longrightarrow> f`x = g`x\<rbrakk> \<Longrightarrow> f<=g"
by (force dest: Pi_memberD intro: apply_Pair)

lemma fun_extension:
    "\<lbrakk>f \<in> Pi(A,B);  g \<in> Pi(A,D);
        \<And>x. x \<in> A \<Longrightarrow> f`x = g`x\<rbrakk> \<Longrightarrow> f=g"
by (blast del: subsetI intro: subset_refl sym fun_subset)

lemma eta [simp]: "f \<in> Pi(A,B) \<Longrightarrow> (\<lambda>x\<in>A. f`x) = f"
apply (rule fun_extension)
apply (auto simp add: lam_type apply_type beta)
done

lemma fun_extension_iff:
     "\<lbrakk>f \<in> Pi(A,B); g \<in> Pi(A,C)\<rbrakk> \<Longrightarrow> (\<forall>a\<in>A. f`a = g`a) \<longleftrightarrow> f=g"
by (blast intro: fun_extension)

(*thm by Mark Staples, proof by lcp*)
lemma fun_subset_eq: "\<lbrakk>f \<in> Pi(A,B); g \<in> Pi(A,C)\<rbrakk> \<Longrightarrow> f \<subseteq> g \<longleftrightarrow> (f = g)"
by (blast dest: apply_Pair
          intro: fun_extension apply_equality [symmetric])


(*Every element of Pi(A,B) may be expressed as a lambda abstraction!*)
lemma Pi_lamE:
  assumes major: "f \<in> Pi(A,B)"
      and minor: "\<And>b. \<lbrakk>\<forall>x\<in>A. b(x):B(x);  f = (\<lambda>x\<in>A. b(x))\<rbrakk> \<Longrightarrow> P"
  shows "P"
apply (rule minor)
apply (rule_tac [2] eta [symmetric])
apply (blast intro: major apply_type)+
done


subsection\<open>Images of Functions\<close>

lemma image_lam: "C \<subseteq> A \<Longrightarrow> (\<lambda>x\<in>A. b(x)) `` C = {b(x). x \<in> C}"
by (unfold lam_def, blast)

lemma Repfun_function_if:
     "function(f)
      \<Longrightarrow> {f`x. x \<in> C} = (if C \<subseteq> domain(f) then f``C else cons(0,f``C))"
apply simp
apply (intro conjI impI)
 apply (blast dest: function_apply_equality intro: function_apply_Pair)
apply (rule equalityI)
 apply (blast intro!: function_apply_Pair apply_0)
apply (blast dest: function_apply_equality intro: apply_0 [symmetric])
done

(*For this lemma and the next, the right-hand side could equivalently
  be written \<Union>x\<in>C. {f`x} *)
lemma image_function:
     "\<lbrakk>function(f);  C \<subseteq> domain(f)\<rbrakk> \<Longrightarrow> f``C = {f`x. x \<in> C}"
by (simp add: Repfun_function_if)

lemma image_fun: "\<lbrakk>f \<in> Pi(A,B);  C \<subseteq> A\<rbrakk> \<Longrightarrow> f``C = {f`x. x \<in> C}"
apply (simp add: Pi_iff)
apply (blast intro: image_function)
done

lemma image_eq_UN:
  assumes f: "f \<in> Pi(A,B)" "C \<subseteq> A" shows "f``C = (\<Union>x\<in>C. {f ` x})"
by (auto simp add: image_fun [OF f])

lemma Pi_image_cons:
     "\<lbrakk>f \<in> Pi(A,B);  x \<in> A\<rbrakk> \<Longrightarrow> f `` cons(x,y) = cons(f`x, f``y)"
by (blast dest: apply_equality apply_Pair)


subsection\<open>Properties of \<^term>\<open>restrict(f,A)\<close>\<close>

lemma restrict_subset: "restrict(f,A) \<subseteq> f"
by (unfold restrict_def, blast)

lemma function_restrictI:
    "function(f) \<Longrightarrow> function(restrict(f,A))"
by (unfold restrict_def function_def, blast)

lemma restrict_type2: "\<lbrakk>f \<in> Pi(C,B);  A<=C\<rbrakk> \<Longrightarrow> restrict(f,A) \<in> Pi(A,B)"
by (simp add: Pi_iff function_def restrict_def, blast)

lemma restrict: "restrict(f,A) ` a = (if a \<in> A then f`a else 0)"
by (simp add: apply_def restrict_def, blast)

lemma restrict_empty [simp]: "restrict(f,0) = 0"
by (unfold restrict_def, simp)

lemma restrict_iff: "z \<in> restrict(r,A) \<longleftrightarrow> z \<in> r \<and> (\<exists>x\<in>A. \<exists>y. z = \<langle>x, y\<rangle>)"
by (simp add: restrict_def)

lemma restrict_restrict [simp]:
     "restrict(restrict(r,A),B) = restrict(r, A \<inter> B)"
by (unfold restrict_def, blast)

lemma domain_restrict [simp]: "domain(restrict(f,C)) = domain(f) \<inter> C"
  unfolding restrict_def
apply (auto simp add: domain_def)
done

lemma restrict_idem: "f \<subseteq> Sigma(A,B) \<Longrightarrow> restrict(f,A) = f"
by (simp add: restrict_def, blast)


(*converse probably holds too*)
lemma domain_restrict_idem:
     "\<lbrakk>domain(r) \<subseteq> A; relation(r)\<rbrakk> \<Longrightarrow> restrict(r,A) = r"
by (simp add: restrict_def relation_def, blast)

lemma domain_restrict_lam [simp]: "domain(restrict(Lambda(A,f),C)) = A \<inter> C"
  unfolding restrict_def lam_def
apply (rule equalityI)
apply (auto simp add: domain_iff)
done

lemma restrict_if [simp]: "restrict(f,A) ` a = (if a \<in> A then f`a else 0)"
by (simp add: restrict apply_0)

lemma restrict_lam_eq:
    "A<=C \<Longrightarrow> restrict(\<lambda>x\<in>C. b(x), A) = (\<lambda>x\<in>A. b(x))"
by (unfold restrict_def lam_def, auto)

lemma fun_cons_restrict_eq:
     "f \<in> cons(a, b) -> B \<Longrightarrow> f = cons(<a, f ` a>, restrict(f, b))"
apply (rule equalityI)
 prefer 2 apply (blast intro: apply_Pair restrict_subset [THEN subsetD])
apply (auto dest!: Pi_memberD simp add: restrict_def lam_def)
done


subsection\<open>Unions of Functions\<close>

(** The Union of a set of COMPATIBLE functions is a function **)

lemma function_Union:
    "\<lbrakk>\<forall>x\<in>S. function(x);
        \<forall>x\<in>S. \<forall>y\<in>S. x<=y | y<=x\<rbrakk>
     \<Longrightarrow> function(\<Union>(S))"
by (unfold function_def, blast)

lemma fun_Union:
    "\<lbrakk>\<forall>f\<in>S. \<exists>C D. f \<in> C->D;
             \<forall>f\<in>S. \<forall>y\<in>S. f<=y | y<=f\<rbrakk> \<Longrightarrow>
          \<Union>(S) \<in> domain(\<Union>(S)) -> range(\<Union>(S))"
  unfolding Pi_def
apply (blast intro!: rel_Union function_Union)
done

lemma gen_relation_Union:
     "(\<And>f. f\<in>F \<Longrightarrow> relation(f)) \<Longrightarrow> relation(\<Union>(F))"
by (simp add: relation_def)


(** The Union of 2 disjoint functions is a function **)

lemmas Un_rls = Un_subset_iff SUM_Un_distrib1 prod_Un_distrib2
                subset_trans [OF _ Un_upper1]
                subset_trans [OF _ Un_upper2]

lemma fun_disjoint_Un:
     "\<lbrakk>f \<in> A->B;  g \<in> C->D;  A \<inter> C = 0\<rbrakk>
      \<Longrightarrow> (f \<union> g) \<in> (A \<union> C) -> (B \<union> D)"
(*Prove the product and domain subgoals using distributive laws*)
apply (simp add: Pi_iff extension Un_rls)
apply (unfold function_def, blast)
done

lemma fun_disjoint_apply1: "a \<notin> domain(g) \<Longrightarrow> (f \<union> g)`a = f`a"
by (simp add: apply_def, blast)

lemma fun_disjoint_apply2: "c \<notin> domain(f) \<Longrightarrow> (f \<union> g)`c = g`c"
by (simp add: apply_def, blast)

subsection\<open>Domain and Range of a Function or Relation\<close>

lemma domain_of_fun: "f \<in> Pi(A,B) \<Longrightarrow> domain(f)=A"
by (unfold Pi_def, blast)

lemma apply_rangeI: "\<lbrakk>f \<in> Pi(A,B);  a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> range(f)"
by (erule apply_Pair [THEN rangeI], assumption)

lemma range_of_fun: "f \<in> Pi(A,B) \<Longrightarrow> f \<in> A->range(f)"
by (blast intro: Pi_type apply_rangeI)

subsection\<open>Extensions of Functions\<close>

lemma fun_extend:
     "\<lbrakk>f \<in> A->B;  c\<notin>A\<rbrakk> \<Longrightarrow> cons(\<langle>c,b\<rangle>,f) \<in> cons(c,A) -> cons(b,B)"
apply (frule singleton_fun [THEN fun_disjoint_Un], blast)
apply (simp add: cons_eq)
done

lemma fun_extend3:
     "\<lbrakk>f \<in> A->B;  c\<notin>A;  b \<in> B\<rbrakk> \<Longrightarrow> cons(\<langle>c,b\<rangle>,f) \<in> cons(c,A) -> B"
by (blast intro: fun_extend [THEN fun_weaken_type])

lemma extend_apply:
     "c \<notin> domain(f) \<Longrightarrow> cons(\<langle>c,b\<rangle>,f)`a = (if a=c then b else f`a)"
by (auto simp add: apply_def)

lemma fun_extend_apply [simp]:
     "\<lbrakk>f \<in> A->B;  c\<notin>A\<rbrakk> \<Longrightarrow> cons(\<langle>c,b\<rangle>,f)`a = (if a=c then b else f`a)"
apply (rule extend_apply)
apply (simp add: Pi_def, blast)
done

lemmas singleton_apply = apply_equality [OF singletonI singleton_fun, simp]

(*For Finite.ML.  Inclusion of right into left is easy*)
lemma cons_fun_eq:
     "c \<notin> A \<Longrightarrow> cons(c,A) -> B = (\<Union>f \<in> A->B. \<Union>b\<in>B. {cons(\<langle>c,b\<rangle>, f)})"
apply (rule equalityI)
apply (safe elim!: fun_extend3)
(*Inclusion of left into right*)
apply (subgoal_tac "restrict (x, A) \<in> A -> B")
 prefer 2 apply (blast intro: restrict_type2)
apply (rule UN_I, assumption)
apply (rule apply_funtype [THEN UN_I])
  apply assumption
 apply (rule consI1)
apply (simp (no_asm))
apply (rule fun_extension)
  apply assumption
 apply (blast intro: fun_extend)
apply (erule consE, simp_all)
done

lemma succ_fun_eq: "succ(n) -> B = (\<Union>f \<in> n->B. \<Union>b\<in>B. {cons(\<langle>n,b\<rangle>, f)})"
by (simp add: succ_def mem_not_refl cons_fun_eq)


subsection\<open>Function Updates\<close>

definition
  update  :: "[i,i,i] \<Rightarrow> i"  where
   "update(f,a,b) \<equiv> \<lambda>x\<in>cons(a, domain(f)). if(x=a, b, f`x)"

nonterminal updbinds and updbind

syntax
  "_updbind"    :: "[i, i] \<Rightarrow> updbind"               (\<open>(2_ :=/ _)\<close>)
  ""            :: "updbind \<Rightarrow> updbinds"             (\<open>_\<close>)
  "_updbinds"   :: "[updbind, updbinds] \<Rightarrow> updbinds" (\<open>_,/ _\<close>)
  "_Update"     :: "[i, updbinds] \<Rightarrow> i"              (\<open>_/'((_)')\<close> [900,0] 900)
syntax_consts "_Update" "_updbind" \<rightleftharpoons> update
translations
  "_Update (f, _updbinds(b,bs))"  == "_Update (_Update(f,b), bs)"
  "f(x:=y)"                       == "CONST update(f,x,y)"

lemma update_apply [simp]: "f(x:=y) ` z = (if z=x then y else f`z)"
apply (simp add: update_def)
apply (case_tac "z \<in> domain(f)")
apply (simp_all add: apply_0)
done

lemma update_idem: "\<lbrakk>f`x = y;  f \<in> Pi(A,B);  x \<in> A\<rbrakk> \<Longrightarrow> f(x:=y) = f"
  unfolding update_def
apply (simp add: domain_of_fun cons_absorb)
apply (rule fun_extension)
apply (best intro: apply_type if_type lam_type, assumption, simp)
done


(* \<lbrakk>f \<in> Pi(A, B); x \<in> A\<rbrakk> \<Longrightarrow> f(x := f`x) = f *)
declare refl [THEN update_idem, simp]

lemma domain_update [simp]: "domain(f(x:=y)) = cons(x, domain(f))"
by (unfold update_def, simp)

lemma update_type: "\<lbrakk>f \<in> Pi(A,B);  x \<in> A;  y \<in> B(x)\<rbrakk> \<Longrightarrow> f(x:=y) \<in> Pi(A, B)"
  unfolding update_def
apply (simp add: domain_of_fun cons_absorb apply_funtype lam_type)
done


subsection\<open>Monotonicity Theorems\<close>

subsubsection\<open>Replacement in its Various Forms\<close>

(*Not easy to express monotonicity in P, since any "bigger" predicate
  would have to be single-valued*)
lemma Replace_mono: "A<=B \<Longrightarrow> Replace(A,P) \<subseteq> Replace(B,P)"
by (blast elim!: ReplaceE)

lemma RepFun_mono: "A<=B \<Longrightarrow> {f(x). x \<in> A} \<subseteq> {f(x). x \<in> B}"
by blast

lemma Pow_mono: "A<=B \<Longrightarrow> Pow(A) \<subseteq> Pow(B)"
by blast

lemma Union_mono: "A<=B \<Longrightarrow> \<Union>(A) \<subseteq> \<Union>(B)"
by blast

lemma UN_mono:
    "\<lbrakk>A<=C;  \<And>x. x \<in> A \<Longrightarrow> B(x)<=D(x)\<rbrakk> \<Longrightarrow> (\<Union>x\<in>A. B(x)) \<subseteq> (\<Union>x\<in>C. D(x))"
by blast

(*Intersection is ANTI-monotonic.  There are TWO premises! *)
lemma Inter_anti_mono: "\<lbrakk>A<=B;  A\<noteq>0\<rbrakk> \<Longrightarrow> \<Inter>(B) \<subseteq> \<Inter>(A)"
by blast

lemma cons_mono: "C<=D \<Longrightarrow> cons(a,C) \<subseteq> cons(a,D)"
by blast

lemma Un_mono: "\<lbrakk>A<=C;  B<=D\<rbrakk> \<Longrightarrow> A \<union> B \<subseteq> C \<union> D"
by blast

lemma Int_mono: "\<lbrakk>A<=C;  B<=D\<rbrakk> \<Longrightarrow> A \<inter> B \<subseteq> C \<inter> D"
by blast

lemma Diff_mono: "\<lbrakk>A<=C;  D<=B\<rbrakk> \<Longrightarrow> A-B \<subseteq> C-D"
by blast

subsubsection\<open>Standard Products, Sums and Function Spaces\<close>

lemma Sigma_mono [rule_format]:
     "\<lbrakk>A<=C;  \<And>x. x \<in> A \<longrightarrow> B(x) \<subseteq> D(x)\<rbrakk> \<Longrightarrow> Sigma(A,B) \<subseteq> Sigma(C,D)"
by blast

lemma sum_mono: "\<lbrakk>A<=C;  B<=D\<rbrakk> \<Longrightarrow> A+B \<subseteq> C+D"
by (unfold sum_def, blast)

(*Note that B->A and C->A are typically disjoint!*)
lemma Pi_mono: "B<=C \<Longrightarrow> A->B \<subseteq> A->C"
by (blast intro: lam_type elim: Pi_lamE)

lemma lam_mono: "A<=B \<Longrightarrow> Lambda(A,c) \<subseteq> Lambda(B,c)"
  unfolding lam_def
apply (erule RepFun_mono)
done

subsubsection\<open>Converse, Domain, Range, Field\<close>

lemma converse_mono: "r<=s \<Longrightarrow> converse(r) \<subseteq> converse(s)"
by blast

lemma domain_mono: "r<=s \<Longrightarrow> domain(r)<=domain(s)"
by blast

lemmas domain_rel_subset = subset_trans [OF domain_mono domain_subset]

lemma range_mono: "r<=s \<Longrightarrow> range(r)<=range(s)"
by blast

lemmas range_rel_subset = subset_trans [OF range_mono range_subset]

lemma field_mono: "r<=s \<Longrightarrow> field(r)<=field(s)"
by blast

lemma field_rel_subset: "r \<subseteq> A*A \<Longrightarrow> field(r) \<subseteq> A"
by (erule field_mono [THEN subset_trans], blast)


subsubsection\<open>Images\<close>

lemma image_pair_mono:
    "\<lbrakk>\<And>x y. \<langle>x,y\<rangle>:r \<Longrightarrow> \<langle>x,y\<rangle>:s;  A<=B\<rbrakk> \<Longrightarrow> r``A \<subseteq> s``B"
by blast

lemma vimage_pair_mono:
    "\<lbrakk>\<And>x y. \<langle>x,y\<rangle>:r \<Longrightarrow> \<langle>x,y\<rangle>:s;  A<=B\<rbrakk> \<Longrightarrow> r-``A \<subseteq> s-``B"
by blast

lemma image_mono: "\<lbrakk>r<=s;  A<=B\<rbrakk> \<Longrightarrow> r``A \<subseteq> s``B"
by blast

lemma vimage_mono: "\<lbrakk>r<=s;  A<=B\<rbrakk> \<Longrightarrow> r-``A \<subseteq> s-``B"
by blast

lemma Collect_mono:
    "\<lbrakk>A<=B;  \<And>x. x \<in> A \<Longrightarrow> P(x) \<longrightarrow> Q(x)\<rbrakk> \<Longrightarrow> Collect(A,P) \<subseteq> Collect(B,Q)"
by blast

(*Used in intr_elim.ML and in individual datatype definitions*)
lemmas basic_monos = subset_refl imp_refl disj_mono conj_mono ex_mono
                     Collect_mono Part_mono in_mono

(* Useful with simp; contributed by Clemens Ballarin. *)

lemma bex_image_simp:
  "\<lbrakk>f \<in> Pi(X, Y); A \<subseteq> X\<rbrakk>  \<Longrightarrow> (\<exists>x\<in>f``A. P(x)) \<longleftrightarrow> (\<exists>x\<in>A. P(f`x))"
  apply safe
   apply rule
    prefer 2 apply assumption
   apply (simp add: apply_equality)
  apply (blast intro: apply_Pair)
  done

lemma ball_image_simp:
  "\<lbrakk>f \<in> Pi(X, Y); A \<subseteq> X\<rbrakk>  \<Longrightarrow> (\<forall>x\<in>f``A. P(x)) \<longleftrightarrow> (\<forall>x\<in>A. P(f`x))"
  apply safe
   apply (blast intro: apply_Pair)
  apply (drule bspec) apply assumption
  apply (simp add: apply_equality)
  done

end
