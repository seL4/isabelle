(*  Title:      HOL/Proofs/Lambda/Commutation.thy
    Author:     Tobias Nipkow
    Copyright   1995  TU Muenchen
*)

header {* Abstract commutation and confluence notions *}

theory Commutation imports Main begin

declare [[syntax_ambiguity = ignore]]


subsection {* Basic definitions *}

definition
  square :: "['a => 'a => bool, 'a => 'a => bool, 'a => 'a => bool, 'a => 'a => bool] => bool" where
  "square R S T U =
    (\<forall>x y. R x y --> (\<forall>z. S x z --> (\<exists>u. T y u \<and> U z u)))"

definition
  commute :: "['a => 'a => bool, 'a => 'a => bool] => bool" where
  "commute R S = square R S S R"

definition
  diamond :: "('a => 'a => bool) => bool" where
  "diamond R = commute R R"

definition
  Church_Rosser :: "('a => 'a => bool) => bool" where
  "Church_Rosser R =
    (\<forall>x y. (sup R (R^--1))^** x y --> (\<exists>z. R^** x z \<and> R^** y z))"

abbreviation
  confluent :: "('a => 'a => bool) => bool" where
  "confluent R == diamond (R^**)"


subsection {* Basic lemmas *}

subsubsection {* @{text "square"} *}

lemma square_sym: "square R S T U ==> square S R U T"
  apply (unfold square_def)
  apply blast
  done

lemma square_subset:
    "[| square R S T U; T \<le> T' |] ==> square R S T' U"
  apply (unfold square_def)
  apply (blast dest: predicate2D)
  done

lemma square_reflcl:
    "[| square R S T (R^==); S \<le> T |] ==> square (R^==) S T (R^==)"
  apply (unfold square_def)
  apply (blast dest: predicate2D)
  done

lemma square_rtrancl:
    "square R S S T ==> square (R^**) S S (T^**)"
  apply (unfold square_def)
  apply (intro strip)
  apply (erule rtranclp_induct)
   apply blast
  apply (blast intro: rtranclp.rtrancl_into_rtrancl)
  done

lemma square_rtrancl_reflcl_commute:
    "square R S (S^**) (R^==) ==> commute (R^**) (S^**)"
  apply (unfold commute_def)
  apply (fastforce dest: square_reflcl square_sym [THEN square_rtrancl])
  done


subsubsection {* @{text "commute"} *}

lemma commute_sym: "commute R S ==> commute S R"
  apply (unfold commute_def)
  apply (blast intro: square_sym)
  done

lemma commute_rtrancl: "commute R S ==> commute (R^**) (S^**)"
  apply (unfold commute_def)
  apply (blast intro: square_rtrancl square_sym)
  done

lemma commute_Un:
    "[| commute R T; commute S T |] ==> commute (sup R S) T"
  apply (unfold commute_def square_def)
  apply blast
  done


subsubsection {* @{text "diamond"}, @{text "confluence"}, and @{text "union"} *}

lemma diamond_Un:
    "[| diamond R; diamond S; commute R S |] ==> diamond (sup R S)"
  apply (unfold diamond_def)
  apply (blast intro: commute_Un commute_sym) 
  done

lemma diamond_confluent: "diamond R ==> confluent R"
  apply (unfold diamond_def)
  apply (erule commute_rtrancl)
  done

lemma square_reflcl_confluent:
    "square R R (R^==) (R^==) ==> confluent R"
  apply (unfold diamond_def)
  apply (fast intro: square_rtrancl_reflcl_commute elim: square_subset)
  done

lemma confluent_Un:
    "[| confluent R; confluent S; commute (R^**) (S^**) |] ==> confluent (sup R S)"
  apply (rule rtranclp_sup_rtranclp [THEN subst])
  apply (blast dest: diamond_Un intro: diamond_confluent)
  done

lemma diamond_to_confluence:
    "[| diamond R; T \<le> R; R \<le> T^** |] ==> confluent T"
  apply (force intro: diamond_confluent
    dest: rtranclp_subset [symmetric])
  done


subsection {* Church-Rosser *}

lemma Church_Rosser_confluent: "Church_Rosser R = confluent R"
  apply (unfold square_def commute_def diamond_def Church_Rosser_def)
  apply (tactic {* safe_tac (put_claset HOL_cs @{context}) *})
   apply (tactic {*
     blast_tac (put_claset HOL_cs @{context} addIs
       [@{thm sup_ge2} RS @{thm rtranclp_mono} RS @{thm predicate2D} RS @{thm rtranclp_trans},
        @{thm rtranclp_converseI}, @{thm conversepI},
        @{thm sup_ge1} RS @{thm rtranclp_mono} RS @{thm predicate2D}]) 1 *})
  apply (erule rtranclp_induct)
   apply blast
  apply (blast del: rtranclp.rtrancl_refl intro: rtranclp_trans)
  done


subsection {* Newman's lemma *}

text {* Proof by Stefan Berghofer *}

theorem newman:
  assumes wf: "wfP (R\<inverse>\<inverse>)"
  and lc: "\<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  shows "\<And>b c. R\<^sup>*\<^sup>* a b \<Longrightarrow> R\<^sup>*\<^sup>* a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  using wf
proof induct
  case (less x b c)
  have xc: "R\<^sup>*\<^sup>* x c" by fact
  have xb: "R\<^sup>*\<^sup>* x b" by fact thus ?case
  proof (rule converse_rtranclpE)
    assume "x = b"
    with xc have "R\<^sup>*\<^sup>* b c" by simp
    thus ?thesis by iprover
  next
    fix y
    assume xy: "R x y"
    assume yb: "R\<^sup>*\<^sup>* y b"
    from xc show ?thesis
    proof (rule converse_rtranclpE)
      assume "x = c"
      with xb have "R\<^sup>*\<^sup>* c b" by simp
      thus ?thesis by iprover
    next
      fix y'
      assume y'c: "R\<^sup>*\<^sup>* y' c"
      assume xy': "R x y'"
      with xy have "\<exists>u. R\<^sup>*\<^sup>* y u \<and> R\<^sup>*\<^sup>* y' u" by (rule lc)
      then obtain u where yu: "R\<^sup>*\<^sup>* y u" and y'u: "R\<^sup>*\<^sup>* y' u" by iprover
      from xy have "R\<inverse>\<inverse> y x" ..
      from this and yb yu have "\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* u d" by (rule less)
      then obtain v where bv: "R\<^sup>*\<^sup>* b v" and uv: "R\<^sup>*\<^sup>* u v" by iprover
      from xy' have "R\<inverse>\<inverse> y' x" ..
      moreover from y'u and uv have "R\<^sup>*\<^sup>* y' v" by (rule rtranclp_trans)
      moreover note y'c
      ultimately have "\<exists>d. R\<^sup>*\<^sup>* v d \<and> R\<^sup>*\<^sup>* c d" by (rule less)
      then obtain w where vw: "R\<^sup>*\<^sup>* v w" and cw: "R\<^sup>*\<^sup>* c w" by iprover
      from bv vw have "R\<^sup>*\<^sup>* b w" by (rule rtranclp_trans)
      with cw show ?thesis by iprover
    qed
  qed
qed

text {*
  Alternative version.  Partly automated by Tobias
  Nipkow. Takes 2 minutes (2002).

  This is the maximal amount of automation possible using @{text blast}.
*}

theorem newman':
  assumes wf: "wfP (R\<inverse>\<inverse>)"
  and lc: "\<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  shows "\<And>b c. R\<^sup>*\<^sup>* a b \<Longrightarrow> R\<^sup>*\<^sup>* a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  using wf
proof induct
  case (less x b c)
  note IH = `\<And>y b c. \<lbrakk>R\<inverse>\<inverse> y x; R\<^sup>*\<^sup>* y b; R\<^sup>*\<^sup>* y c\<rbrakk>
                     \<Longrightarrow> \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d`
  have xc: "R\<^sup>*\<^sup>* x c" by fact
  have xb: "R\<^sup>*\<^sup>* x b" by fact
  thus ?case
  proof (rule converse_rtranclpE)
    assume "x = b"
    with xc have "R\<^sup>*\<^sup>* b c" by simp
    thus ?thesis by iprover
  next
    fix y
    assume xy: "R x y"
    assume yb: "R\<^sup>*\<^sup>* y b"
    from xc show ?thesis
    proof (rule converse_rtranclpE)
      assume "x = c"
      with xb have "R\<^sup>*\<^sup>* c b" by simp
      thus ?thesis by iprover
    next
      fix y'
      assume y'c: "R\<^sup>*\<^sup>* y' c"
      assume xy': "R x y'"
      with xy obtain u where u: "R\<^sup>*\<^sup>* y u" "R\<^sup>*\<^sup>* y' u"
        by (blast dest: lc)
      from yb u y'c show ?thesis
        by (blast del: rtranclp.rtrancl_refl
            intro: rtranclp_trans
            dest: IH [OF conversepI, OF xy] IH [OF conversepI, OF xy'])
    qed
  qed
qed

text {*
  Using the coherent logic prover, the proof of the induction step
  is completely automatic.
*}

lemma eq_imp_rtranclp: "x = y \<Longrightarrow> r\<^sup>*\<^sup>* x y"
  by simp

theorem newman'':
  assumes wf: "wfP (R\<inverse>\<inverse>)"
  and lc: "\<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  shows "\<And>b c. R\<^sup>*\<^sup>* a b \<Longrightarrow> R\<^sup>*\<^sup>* a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  using wf
proof induct
  case (less x b c)
  note IH = `\<And>y b c. \<lbrakk>R\<inverse>\<inverse> y x; R\<^sup>*\<^sup>* y b; R\<^sup>*\<^sup>* y c\<rbrakk>
                     \<Longrightarrow> \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d`
  show ?case
    by (coherent
      `R\<^sup>*\<^sup>* x c` `R\<^sup>*\<^sup>* x b`
      refl [where 'a='a] sym
      eq_imp_rtranclp
      r_into_rtranclp [of R]
      rtranclp_trans
      lc IH [OF conversepI]
      converse_rtranclpE)
qed

end
