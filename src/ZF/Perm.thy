(*  Title:      ZF/Perm.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

The theory underlying permutation groups
  -- Composition of relations, the identity relation
  -- Injections, surjections, bijections
  -- Lemmas for the Schroeder-Bernstein Theorem
*)

section\<open>Injections, Surjections, Bijections, Composition\<close>

theory Perm imports func begin

definition
  (*composition of relations and functions; NOT Suppes's relative product*)
  comp     :: "[i,i]\<Rightarrow>i"      (infixr \<open>O\<close> 60)  where
    "r O s \<equiv> {xz \<in> domain(s)*range(r) .
               \<exists>x y z. xz=\<langle>x,z\<rangle> \<and> \<langle>x,y\<rangle>:s \<and> \<langle>y,z\<rangle>:r}"

definition
  (*the identity function for A*)
  id    :: "i\<Rightarrow>i"  where
    "id(A) \<equiv> (\<lambda>x\<in>A. x)"

definition
  (*one-to-one functions from A to B*)
  inj   :: "[i,i]\<Rightarrow>i"  where
    "inj(A,B) \<equiv> { f \<in> A->B. \<forall>w\<in>A. \<forall>x\<in>A. f`w=f`x \<longrightarrow> w=x}"

definition
  (*onto functions from A to B*)
  surj  :: "[i,i]\<Rightarrow>i"  where
    "surj(A,B) \<equiv> { f \<in> A->B . \<forall>y\<in>B. \<exists>x\<in>A. f`x=y}"

definition
  (*one-to-one and onto functions*)
  bij   :: "[i,i]\<Rightarrow>i"  where
    "bij(A,B) \<equiv> inj(A,B) \<inter> surj(A,B)"


subsection\<open>Surjective Function Space\<close>

lemma surj_is_fun: "f \<in> surj(A,B) \<Longrightarrow> f \<in> A->B"
  unfolding surj_def
apply (erule CollectD1)
done

lemma fun_is_surj: "f \<in> Pi(A,B) \<Longrightarrow> f \<in> surj(A,range(f))"
  unfolding surj_def
apply (blast intro: apply_equality range_of_fun domain_type)
done

lemma surj_range: "f \<in> surj(A,B) \<Longrightarrow> range(f)=B"
  unfolding surj_def
apply (best intro: apply_Pair elim: range_type)
done

text\<open>A function with a right inverse is a surjection\<close>

lemma f_imp_surjective:
    "\<lbrakk>f \<in> A->B;  \<And>y. y \<in> B \<Longrightarrow> d(y): A;  \<And>y. y \<in> B \<Longrightarrow> f`d(y) = y\<rbrakk>
     \<Longrightarrow> f \<in> surj(A,B)"
  by (simp add: surj_def, blast)

lemma lam_surjective:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> c(x): B;
        \<And>y. y \<in> B \<Longrightarrow> d(y): A;
        \<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y
\<rbrakk> \<Longrightarrow> (\<lambda>x\<in>A. c(x)) \<in> surj(A,B)"
apply (rule_tac d = d in f_imp_surjective)
apply (simp_all add: lam_type)
done

text\<open>Cantor's theorem revisited\<close>
lemma cantor_surj: "f \<notin> surj(A,Pow(A))"
apply (unfold surj_def, safe)
apply (cut_tac cantor)
apply (best del: subsetI)
done


subsection\<open>Injective Function Space\<close>

lemma inj_is_fun: "f \<in> inj(A,B) \<Longrightarrow> f \<in> A->B"
  unfolding inj_def
apply (erule CollectD1)
done

text\<open>Good for dealing with sets of pairs, but a bit ugly in use [used in AC]\<close>
lemma inj_equality:
    "\<lbrakk>\<langle>a,b\<rangle>:f;  \<langle>c,b\<rangle>:f;  f \<in> inj(A,B)\<rbrakk> \<Longrightarrow> a=c"
  unfolding inj_def
apply (blast dest: Pair_mem_PiD)
done

lemma inj_apply_equality: "\<lbrakk>f \<in> inj(A,B);  f`a=f`b;  a \<in> A;  b \<in> A\<rbrakk> \<Longrightarrow> a=b"
by (unfold inj_def, blast)

text\<open>A function with a left inverse is an injection\<close>

lemma f_imp_injective: "\<lbrakk>f \<in> A->B;  \<forall>x\<in>A. d(f`x)=x\<rbrakk> \<Longrightarrow> f \<in> inj(A,B)"
apply (simp (no_asm_simp) add: inj_def)
apply (blast intro: subst_context [THEN box_equals])
done

lemma lam_injective:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> c(x): B;
        \<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x\<rbrakk>
     \<Longrightarrow> (\<lambda>x\<in>A. c(x)) \<in> inj(A,B)"
apply (rule_tac d = d in f_imp_injective)
apply (simp_all add: lam_type)
done

subsection\<open>Bijections\<close>

lemma bij_is_inj: "f \<in> bij(A,B) \<Longrightarrow> f \<in> inj(A,B)"
  unfolding bij_def
apply (erule IntD1)
done

lemma bij_is_surj: "f \<in> bij(A,B) \<Longrightarrow> f \<in> surj(A,B)"
  unfolding bij_def
apply (erule IntD2)
done

lemma bij_is_fun: "f \<in> bij(A,B) \<Longrightarrow> f \<in> A->B"
  by (rule bij_is_inj [THEN inj_is_fun])

lemma lam_bijective:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> c(x): B;
        \<And>y. y \<in> B \<Longrightarrow> d(y): A;
        \<And>x. x \<in> A \<Longrightarrow> d(c(x)) = x;
        \<And>y. y \<in> B \<Longrightarrow> c(d(y)) = y
\<rbrakk> \<Longrightarrow> (\<lambda>x\<in>A. c(x)) \<in> bij(A,B)"
  unfolding bij_def
apply (blast intro!: lam_injective lam_surjective)
done

lemma RepFun_bijective: "(\<forall>y\<in>x. \<exists>!y'. f(y') = f(y))
      \<Longrightarrow> (\<lambda>z\<in>{f(y). y \<in> x}. THE y. f(y) = z) \<in> bij({f(y). y \<in> x}, x)"
apply (rule_tac d = f in lam_bijective)
apply (auto simp add: the_equality2)
done


subsection\<open>Identity Function\<close>

lemma idI [intro!]: "a \<in> A \<Longrightarrow> \<langle>a,a\<rangle> \<in> id(A)"
  unfolding id_def
apply (erule lamI)
done

lemma idE [elim!]: "\<lbrakk>p \<in> id(A);  \<And>x.\<lbrakk>x \<in> A; p=\<langle>x,x\<rangle>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>  P"
by (simp add: id_def lam_def, blast)

lemma id_type: "id(A) \<in> A->A"
  unfolding id_def
apply (rule lam_type, assumption)
done

lemma id_conv [simp]: "x \<in> A \<Longrightarrow> id(A)`x = x"
  unfolding id_def
apply (simp (no_asm_simp))
done

lemma id_mono: "A<=B \<Longrightarrow> id(A) \<subseteq> id(B)"
  unfolding id_def
apply (erule lam_mono)
done

lemma id_subset_inj: "A<=B \<Longrightarrow> id(A): inj(A,B)"
apply (simp add: inj_def id_def)
apply (blast intro: lam_type)
done

lemmas id_inj = subset_refl [THEN id_subset_inj]

lemma id_surj: "id(A): surj(A,A)"
apply (unfold id_def surj_def)
apply (simp (no_asm_simp))
done

lemma id_bij: "id(A): bij(A,A)"
  unfolding bij_def
apply (blast intro: id_inj id_surj)
done

lemma subset_iff_id: "A \<subseteq> B \<longleftrightarrow> id(A) \<in> A->B"
  unfolding id_def
apply (force intro!: lam_type dest: apply_type)
done

text\<open>\<^term>\<open>id\<close> as the identity relation\<close>
lemma id_iff [simp]: "\<langle>x,y\<rangle> \<in> id(A) \<longleftrightarrow> x=y \<and> y \<in> A"
by auto


subsection\<open>Converse of a Function\<close>

lemma inj_converse_fun: "f \<in> inj(A,B) \<Longrightarrow> converse(f) \<in> range(f)->A"
  unfolding inj_def
apply (simp (no_asm_simp) add: Pi_iff function_def)
apply (erule CollectE)
apply (simp (no_asm_simp) add: apply_iff)
apply (blast dest: fun_is_rel)
done

text\<open>Equations for converse(f)\<close>

text\<open>The premises are equivalent to saying that f is injective...\<close>
lemma left_inverse_lemma:
     "\<lbrakk>f \<in> A->B;  converse(f): C->A;  a \<in> A\<rbrakk> \<Longrightarrow> converse(f)`(f`a) = a"
by (blast intro: apply_Pair apply_equality converseI)

lemma left_inverse [simp]: "\<lbrakk>f \<in> inj(A,B);  a \<in> A\<rbrakk> \<Longrightarrow> converse(f)`(f`a) = a"
by (blast intro: left_inverse_lemma inj_converse_fun inj_is_fun)

lemma left_inverse_eq:
     "\<lbrakk>f \<in> inj(A,B); f ` x = y; x \<in> A\<rbrakk> \<Longrightarrow> converse(f) ` y = x"
by auto

lemmas left_inverse_bij = bij_is_inj [THEN left_inverse]

lemma right_inverse_lemma:
     "\<lbrakk>f \<in> A->B;  converse(f): C->A;  b \<in> C\<rbrakk> \<Longrightarrow> f`(converse(f)`b) = b"
by (rule apply_Pair [THEN converseD [THEN apply_equality]], auto)

(*Should the premises be f \<in> surj(A,B), b \<in> B for symmetry with left_inverse?
  No: they would not imply that converse(f) was a function! *)
lemma right_inverse [simp]:
     "\<lbrakk>f \<in> inj(A,B);  b \<in> range(f)\<rbrakk> \<Longrightarrow> f`(converse(f)`b) = b"
by (blast intro: right_inverse_lemma inj_converse_fun inj_is_fun)

lemma right_inverse_bij: "\<lbrakk>f \<in> bij(A,B);  b \<in> B\<rbrakk> \<Longrightarrow> f`(converse(f)`b) = b"
by (force simp add: bij_def surj_range)

subsection\<open>Converses of Injections, Surjections, Bijections\<close>

lemma inj_converse_inj: "f \<in> inj(A,B) \<Longrightarrow> converse(f): inj(range(f), A)"
apply (rule f_imp_injective)
apply (erule inj_converse_fun, clarify)
apply (rule right_inverse)
 apply assumption
apply blast
done

lemma inj_converse_surj: "f \<in> inj(A,B) \<Longrightarrow> converse(f): surj(range(f), A)"
by (blast intro: f_imp_surjective inj_converse_fun left_inverse inj_is_fun
                 range_of_fun [THEN apply_type])

text\<open>Adding this as an intro! rule seems to cause looping\<close>
lemma bij_converse_bij [TC]: "f \<in> bij(A,B) \<Longrightarrow> converse(f): bij(B,A)"
  unfolding bij_def
apply (fast elim: surj_range [THEN subst] inj_converse_inj inj_converse_surj)
done



subsection\<open>Composition of Two Relations\<close>

text\<open>The inductive definition package could derive these theorems for \<^term>\<open>r O s\<close>\<close>

lemma compI [intro]: "\<lbrakk>\<langle>a,b\<rangle>:s; \<langle>b,c\<rangle>:r\<rbrakk> \<Longrightarrow> \<langle>a,c\<rangle> \<in> r O s"
by (unfold comp_def, blast)

lemma compE [elim!]:
    "\<lbrakk>xz \<in> r O s;
        \<And>x y z. \<lbrakk>xz=\<langle>x,z\<rangle>;  \<langle>x,y\<rangle>:s;  \<langle>y,z\<rangle>:r\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
by (unfold comp_def, blast)

lemma compEpair:
    "\<lbrakk>\<langle>a,c\<rangle> \<in> r O s;
        \<And>y. \<lbrakk>\<langle>a,y\<rangle>:s;  \<langle>y,c\<rangle>:r\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
by (erule compE, simp)

lemma converse_comp: "converse(R O S) = converse(S) O converse(R)"
by blast


subsection\<open>Domain and Range -- see Suppes, Section 3.1\<close>

text\<open>Boyer et al., Set Theory in First-Order Logic, JAR 2 (1986), 287-327\<close>
lemma range_comp: "range(r O s) \<subseteq> range(r)"
by blast

lemma range_comp_eq: "domain(r) \<subseteq> range(s) \<Longrightarrow> range(r O s) = range(r)"
by (rule range_comp [THEN equalityI], blast)

lemma domain_comp: "domain(r O s) \<subseteq> domain(s)"
by blast

lemma domain_comp_eq: "range(s) \<subseteq> domain(r) \<Longrightarrow> domain(r O s) = domain(s)"
by (rule domain_comp [THEN equalityI], blast)

lemma image_comp: "(r O s)``A = r``(s``A)"
by blast

lemma inj_inj_range: "f \<in> inj(A,B) \<Longrightarrow> f \<in> inj(A,range(f))"
  by (auto simp add: inj_def Pi_iff function_def)

lemma inj_bij_range: "f \<in> inj(A,B) \<Longrightarrow> f \<in> bij(A,range(f))"
  by (auto simp add: bij_def intro: inj_inj_range inj_is_fun fun_is_surj)


subsection\<open>Other Results\<close>

lemma comp_mono: "\<lbrakk>r'<=r; s'<=s\<rbrakk> \<Longrightarrow> (r' O s') \<subseteq> (r O s)"
by blast

text\<open>composition preserves relations\<close>
lemma comp_rel: "\<lbrakk>s<=A*B;  r<=B*C\<rbrakk> \<Longrightarrow> (r O s) \<subseteq> A*C"
by blast

text\<open>associative law for composition\<close>
lemma comp_assoc: "(r O s) O t = r O (s O t)"
by blast

(*left identity of composition; provable inclusions are
        id(A) O r \<subseteq> r
  and   \<lbrakk>r<=A*B; B<=C\<rbrakk> \<Longrightarrow> r \<subseteq> id(C) O r *)
lemma left_comp_id: "r<=A*B \<Longrightarrow> id(B) O r = r"
by blast

(*right identity of composition; provable inclusions are
        r O id(A) \<subseteq> r
  and   \<lbrakk>r<=A*B; A<=C\<rbrakk> \<Longrightarrow> r \<subseteq> r O id(C) *)
lemma right_comp_id: "r<=A*B \<Longrightarrow> r O id(A) = r"
by blast


subsection\<open>Composition Preserves Functions, Injections, and Surjections\<close>

lemma comp_function: "\<lbrakk>function(g);  function(f)\<rbrakk> \<Longrightarrow> function(f O g)"
by (unfold function_def, blast)

text\<open>Don't think the premises can be weakened much\<close>
lemma comp_fun: "\<lbrakk>g \<in> A->B;  f \<in> B->C\<rbrakk> \<Longrightarrow> (f O g) \<in> A->C"
apply (auto simp add: Pi_def comp_function Pow_iff comp_rel)
apply (subst range_rel_subset [THEN domain_comp_eq], auto)
done

(*Thanks to the new definition of "apply", the premise f \<in> B->C is gone!*)
lemma comp_fun_apply [simp]:
     "\<lbrakk>g \<in> A->B;  a \<in> A\<rbrakk> \<Longrightarrow> (f O g)`a = f`(g`a)"
apply (frule apply_Pair, assumption)
apply (simp add: apply_def image_comp)
apply (blast dest: apply_equality)
done

text\<open>Simplifies compositions of lambda-abstractions\<close>
lemma comp_lam:
    "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> b(x): B\<rbrakk>
     \<Longrightarrow> (\<lambda>y\<in>B. c(y)) O (\<lambda>x\<in>A. b(x)) = (\<lambda>x\<in>A. c(b(x)))"
apply (subgoal_tac "(\<lambda>x\<in>A. b(x)) \<in> A -> B")
 apply (rule fun_extension)
   apply (blast intro: comp_fun lam_funtype)
  apply (rule lam_funtype)
 apply simp
apply (simp add: lam_type)
done

lemma comp_inj:
     "\<lbrakk>g \<in> inj(A,B);  f \<in> inj(B,C)\<rbrakk> \<Longrightarrow> (f O g) \<in> inj(A,C)"
apply (frule inj_is_fun [of g])
apply (frule inj_is_fun [of f])
apply (rule_tac d = "\<lambda>y. converse (g) ` (converse (f) ` y)" in f_imp_injective)
 apply (blast intro: comp_fun, simp)
done

lemma comp_surj:
    "\<lbrakk>g \<in> surj(A,B);  f \<in> surj(B,C)\<rbrakk> \<Longrightarrow> (f O g) \<in> surj(A,C)"
  unfolding surj_def
apply (blast intro!: comp_fun comp_fun_apply)
done

lemma comp_bij:
    "\<lbrakk>g \<in> bij(A,B);  f \<in> bij(B,C)\<rbrakk> \<Longrightarrow> (f O g) \<in> bij(A,C)"
  unfolding bij_def
apply (blast intro: comp_inj comp_surj)
done


subsection\<open>Dual Properties of \<^term>\<open>inj\<close> and \<^term>\<open>surj\<close>\<close>

text\<open>Useful for proofs from
    D Pastre.  Automatic theorem proving in set theory.
    Artificial Intelligence, 10:1--27, 1978.\<close>

lemma comp_mem_injD1:
    "\<lbrakk>(f O g): inj(A,C);  g \<in> A->B;  f \<in> B->C\<rbrakk> \<Longrightarrow> g \<in> inj(A,B)"
by (unfold inj_def, force)

lemma comp_mem_injD2:
    "\<lbrakk>(f O g): inj(A,C);  g \<in> surj(A,B);  f \<in> B->C\<rbrakk> \<Longrightarrow> f \<in> inj(B,C)"
apply (unfold inj_def surj_def, safe)
apply (rule_tac x1 = x in bspec [THEN bexE])
apply (erule_tac [3] x1 = w in bspec [THEN bexE], assumption+, safe)
apply (rule_tac t = "(`) (g) " in subst_context)
apply (erule asm_rl bspec [THEN bspec, THEN mp])+
apply (simp (no_asm_simp))
done

lemma comp_mem_surjD1:
    "\<lbrakk>(f O g): surj(A,C);  g \<in> A->B;  f \<in> B->C\<rbrakk> \<Longrightarrow> f \<in> surj(B,C)"
  unfolding surj_def
apply (blast intro!: comp_fun_apply [symmetric] apply_funtype)
done


lemma comp_mem_surjD2:
    "\<lbrakk>(f O g): surj(A,C);  g \<in> A->B;  f \<in> inj(B,C)\<rbrakk> \<Longrightarrow> g \<in> surj(A,B)"
apply (unfold inj_def surj_def, safe)
apply (drule_tac x = "f`y" in bspec, auto)
apply (blast intro: apply_funtype)
done

subsubsection\<open>Inverses of Composition\<close>

text\<open>left inverse of composition; one inclusion is
        \<^term>\<open>f \<in> A->B \<Longrightarrow> id(A) \<subseteq> converse(f) O f\<close>\<close>
lemma left_comp_inverse: "f \<in> inj(A,B) \<Longrightarrow> converse(f) O f = id(A)"
apply (unfold inj_def, clarify)
apply (rule equalityI)
 apply (auto simp add: apply_iff, blast)
done

text\<open>right inverse of composition; one inclusion is
                \<^term>\<open>f \<in> A->B \<Longrightarrow> f O converse(f) \<subseteq> id(B)\<close>\<close>
lemma right_comp_inverse:
    "f \<in> surj(A,B) \<Longrightarrow> f O converse(f) = id(B)"
apply (simp add: surj_def, clarify)
apply (rule equalityI)
apply (best elim: domain_type range_type dest: apply_equality2)
apply (blast intro: apply_Pair)
done


subsubsection\<open>Proving that a Function is a Bijection\<close>

lemma comp_eq_id_iff:
    "\<lbrakk>f \<in> A->B;  g \<in> B->A\<rbrakk> \<Longrightarrow> f O g = id(B) \<longleftrightarrow> (\<forall>y\<in>B. f`(g`y)=y)"
apply (unfold id_def, safe)
 apply (drule_tac t = "\<lambda>h. h`y " in subst_context)
 apply simp
apply (rule fun_extension)
  apply (blast intro: comp_fun lam_type)
 apply auto
done

lemma fg_imp_bijective:
    "\<lbrakk>f \<in> A->B;  g \<in> B->A;  f O g = id(B);  g O f = id(A)\<rbrakk> \<Longrightarrow> f \<in> bij(A,B)"
  unfolding bij_def
apply (simp add: comp_eq_id_iff)
apply (blast intro: f_imp_injective f_imp_surjective apply_funtype)
done

lemma nilpotent_imp_bijective: "\<lbrakk>f \<in> A->A;  f O f = id(A)\<rbrakk> \<Longrightarrow> f \<in> bij(A,A)"
by (blast intro: fg_imp_bijective)

lemma invertible_imp_bijective:
     "\<lbrakk>converse(f): B->A;  f \<in> A->B\<rbrakk> \<Longrightarrow> f \<in> bij(A,B)"
by (simp add: fg_imp_bijective comp_eq_id_iff
              left_inverse_lemma right_inverse_lemma)

subsubsection\<open>Unions of Functions\<close>

text\<open>See similar theorems in func.thy\<close>

text\<open>Theorem by KG, proof by LCP\<close>
lemma inj_disjoint_Un:
     "\<lbrakk>f \<in> inj(A,B);  g \<in> inj(C,D);  B \<inter> D = 0\<rbrakk>
      \<Longrightarrow> (\<lambda>a\<in>A \<union> C. if a \<in> A then f`a else g`a) \<in> inj(A \<union> C, B \<union> D)"
apply (rule_tac d = "\<lambda>z. if z \<in> B then converse (f) `z else converse (g) `z"
       in lam_injective)
apply (auto simp add: inj_is_fun [THEN apply_type])
done

lemma surj_disjoint_Un:
    "\<lbrakk>f \<in> surj(A,B);  g \<in> surj(C,D);  A \<inter> C = 0\<rbrakk>
     \<Longrightarrow> (f \<union> g) \<in> surj(A \<union> C, B \<union> D)"
apply (simp add: surj_def fun_disjoint_Un)
apply (blast dest!: domain_of_fun
             intro!: fun_disjoint_apply1 fun_disjoint_apply2)
done

text\<open>A simple, high-level proof; the version for injections follows from it,
  using  \<^term>\<open>f \<in> inj(A,B) \<longleftrightarrow> f \<in> bij(A,range(f))\<close>\<close>
lemma bij_disjoint_Un:
     "\<lbrakk>f \<in> bij(A,B);  g \<in> bij(C,D);  A \<inter> C = 0;  B \<inter> D = 0\<rbrakk>
      \<Longrightarrow> (f \<union> g) \<in> bij(A \<union> C, B \<union> D)"
apply (rule invertible_imp_bijective)
apply (subst converse_Un)
apply (auto intro: fun_disjoint_Un bij_is_fun bij_converse_bij)
done


subsubsection\<open>Restrictions as Surjections and Bijections\<close>

lemma surj_image:
    "f \<in> Pi(A,B) \<Longrightarrow> f \<in> surj(A, f``A)"
apply (simp add: surj_def)
apply (blast intro: apply_equality apply_Pair Pi_type)
done

lemma surj_image_eq: "f \<in> surj(A, B) \<Longrightarrow> f``A = B"
  by (auto simp add: surj_def image_fun) (blast dest: apply_type) 

lemma restrict_image [simp]: "restrict(f,A) `` B = f `` (A \<inter> B)"
by (auto simp add: restrict_def)

lemma restrict_inj:
    "\<lbrakk>f \<in> inj(A,B);  C<=A\<rbrakk> \<Longrightarrow> restrict(f,C): inj(C,B)"
  unfolding inj_def
apply (safe elim!: restrict_type2, auto)
done

lemma restrict_surj: "\<lbrakk>f \<in> Pi(A,B);  C<=A\<rbrakk> \<Longrightarrow> restrict(f,C): surj(C, f``C)"
apply (insert restrict_type2 [THEN surj_image])
apply (simp add: restrict_image)
done

lemma restrict_bij:
    "\<lbrakk>f \<in> inj(A,B);  C<=A\<rbrakk> \<Longrightarrow> restrict(f,C): bij(C, f``C)"
apply (simp add: inj_def bij_def)
apply (blast intro: restrict_surj surj_is_fun)
done


subsubsection\<open>Lemmas for Ramsey's Theorem\<close>

lemma inj_weaken_type: "\<lbrakk>f \<in> inj(A,B);  B<=D\<rbrakk> \<Longrightarrow> f \<in> inj(A,D)"
  unfolding inj_def
apply (blast intro: fun_weaken_type)
done

lemma inj_succ_restrict:
     "\<lbrakk>f \<in> inj(succ(m), A)\<rbrakk> \<Longrightarrow> restrict(f,m) \<in> inj(m, A-{f`m})"
apply (rule restrict_bij [THEN bij_is_inj, THEN inj_weaken_type], assumption, blast)
  unfolding inj_def
apply (fast elim: range_type mem_irrefl dest: apply_equality)
done


lemma inj_extend:
    "\<lbrakk>f \<in> inj(A,B);  a\<notin>A;  b\<notin>B\<rbrakk>
     \<Longrightarrow> cons(\<langle>a,b\<rangle>,f) \<in> inj(cons(a,A), cons(b,B))"
  unfolding inj_def
apply (force intro: apply_type  simp add: fun_extend)
done

end
