(*  Title:      HOL/Real/HahnBanach/HahnBanach.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The Hahn-Banach Theorem *}

theory HahnBanach = HahnBanachLemmas:

text {*
  We present the proof of two different versions of the Hahn-Banach
  Theorem, closely following \cite[\S36]{Heuser:1986}.
*}

subsection {* The Hahn-Banach Theorem for vector spaces *}

text {*
  \textbf{Hahn-Banach Theorem.} Let @{text F} be a subspace of a real
  vector space @{text E}, let @{text p} be a semi-norm on @{text E},
  and @{text f} be a linear form defined on @{text F} such that @{text
  f} is bounded by @{text p}, i.e.  @{text "\<forall>x \<in> F. f x \<le> p x"}.  Then
  @{text f} can be extended to a linear form @{text h} on @{text E}
  such that @{text h} is norm-preserving, i.e. @{text h} is also
  bounded by @{text p}.

  \bigskip
  \textbf{Proof Sketch.}
  \begin{enumerate}

  \item Define @{text M} as the set of norm-preserving extensions of
  @{text f} to subspaces of @{text E}. The linear forms in @{text M}
  are ordered by domain extension.

  \item We show that every non-empty chain in @{text M} has an upper
  bound in @{text M}.

  \item With Zorn's Lemma we conclude that there is a maximal function
  @{text g} in @{text M}.

  \item The domain @{text H} of @{text g} is the whole space @{text
  E}, as shown by classical contradiction:

  \begin{itemize}

  \item Assuming @{text g} is not defined on whole @{text E}, it can
  still be extended in a norm-preserving way to a super-space @{text
  H'} of @{text H}.

  \item Thus @{text g} can not be maximal. Contradiction!

  \end{itemize}

  \end{enumerate}
*}

theorem HahnBanach:
  "is_vectorspace E \<Longrightarrow> is_subspace F E \<Longrightarrow> is_seminorm E p
  \<Longrightarrow> is_linearform F f \<Longrightarrow> \<forall>x \<in> F. f x \<le> p x
  \<Longrightarrow> \<exists>h. is_linearform E h \<and> (\<forall>x \<in> F. h x = f x) \<and> (\<forall>x \<in> E. h x \<le> p x)"
    -- {* Let @{text E} be a vector space, @{text F} a subspace of @{text E}, @{text p} a seminorm on @{text E}, *}
    -- {* and @{text f} a linear form on @{text F} such that @{text f} is bounded by @{text p}, *}
    -- {* then @{text f} can be extended to a linear form @{text h} on @{text E} in a norm-preserving way. \skp *}
proof -
  assume "is_vectorspace E"  "is_subspace F E"  "is_seminorm E p"
   and "is_linearform F f"  "\<forall>x \<in> F. f x \<le> p x"
  -- {* Assume the context of the theorem. \skp *}
  def M \<equiv> "norm_pres_extensions E p F f"
  -- {* Define @{text M} as the set of all norm-preserving extensions of @{text F}. \skp *}
  {
    fix c assume "c \<in> chain M"  "\<exists>x. x \<in> c"
    have "\<Union>c \<in> M"
    -- {* Show that every non-empty chain @{text c} of @{text M} has an upper bound in @{text M}: *}
    -- {* @{text "\<Union>c"} is greater than any element of the chain @{text c}, so it suffices to show @{text "\<Union>c \<in> M"}. *}
    proof (unfold M_def, rule norm_pres_extensionI)
      show "\<exists>H h. graph H h = \<Union>c
              \<and> is_linearform H h
              \<and> is_subspace H E
              \<and> is_subspace F H
              \<and> graph F f \<subseteq> graph H h
              \<and> (\<forall>x \<in> H. h x \<le> p x)"
      proof (intro exI conjI)
        let ?H = "domain (\<Union>c)"
        let ?h = "funct (\<Union>c)"

        show a: "graph ?H ?h = \<Union>c"
        proof (rule graph_domain_funct)
          fix x y z assume "(x, y) \<in> \<Union>c"  "(x, z) \<in> \<Union>c"
          show "z = y" by (rule sup_definite)
        qed
        show "is_linearform ?H ?h"
          by (simp! add: sup_lf a)
        show "is_subspace ?H E"
          by (rule sup_subE, rule a) (simp!)+
        show "is_subspace F ?H"
          by (rule sup_supF, rule a) (simp!)+
        show "graph F f \<subseteq> graph ?H ?h"
          by (rule sup_ext, rule a) (simp!)+
        show "\<forall>x \<in> ?H. ?h x \<le> p x"
          by (rule sup_norm_pres, rule a) (simp!)+
      qed
    qed

  }
  hence "\<exists>g \<in> M. \<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x"
  -- {* With Zorn's Lemma we can conclude that there is a maximal element in @{text M}. \skp *}
  proof (rule Zorn's_Lemma)
    -- {* We show that @{text M} is non-empty: *}
    have "graph F f \<in> norm_pres_extensions E p F f"
    proof (rule norm_pres_extensionI2)
      have "is_vectorspace F" ..
      thus "is_subspace F F" ..
    qed (blast!)+
    thus "graph F f \<in> M" by (simp!)
  qed
  thus ?thesis
  proof
    fix g assume "g \<in> M"  "\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x"
    -- {* We consider such a maximal element @{text "g \<in> M"}. \skp *}
    obtain H h where "graph H h = g"  "is_linearform H h"
      "is_subspace H E"  "is_subspace F H"  "graph F f \<subseteq> graph H h"
      "\<forall>x \<in> H. h x \<le> p x"
      -- {* @{text g} is a norm-preserving extension of @{text f}, in other words: *}
      -- {* @{text g} is the graph of some linear form @{text h} defined on a subspace @{text H} of @{text E}, *}
      -- {* and @{text h} is an extension of @{text f} that is again bounded by @{text p}. \skp *}
    proof -
      have "\<exists>H h. graph H h = g \<and> is_linearform H h
        \<and> is_subspace H E \<and> is_subspace F H
        \<and> graph F f \<subseteq> graph H h
        \<and> (\<forall>x \<in> H. h x \<le> p x)"
        by (simp! add: norm_pres_extension_D)
      with that show ?thesis by blast
    qed
    have h: "is_vectorspace H" ..
    have "H = E"
    -- {* We show that @{text h} is defined on whole @{text E} by classical contradiction. \skp *}
    proof (rule classical)
      assume "H \<noteq> E"
      -- {* Assume @{text h} is not defined on whole @{text E}. Then show that @{text h} can be extended *}
      -- {* in a norm-preserving way to a function @{text h'} with the graph @{text g'}. \skp *}
      have "\<exists>g' \<in> M. g \<subseteq> g' \<and> g \<noteq> g'"
      proof -
        obtain x' where "x' \<in> E"  "x' \<notin> H"
        -- {* Pick @{text "x' \<in> E - H"}. \skp *}
        proof -
          have "\<exists>x' \<in> E. x' \<notin> H"
          proof (rule set_less_imp_diff_not_empty)
            have "H \<subseteq> E" ..
            thus "H \<subset> E" ..
          qed
          with that show ?thesis by blast
        qed
        have x': "x' \<noteq> 0"
        proof (rule classical)
          presume "x' = 0"
          with h have "x' \<in> H" by simp
          thus ?thesis by contradiction
        qed blast
        def H' \<equiv> "H + lin x'"
        -- {* Define @{text H'} as the direct sum of @{text H} and the linear closure of @{text x'}. \skp *}
        obtain xi where "\<forall>y \<in> H. - p (y + x') - h y \<le> xi
                          \<and> xi \<le> p (y + x') - h y"
        -- {* Pick a real number @{text \<xi>} that fulfills certain inequations; this will *}
        -- {* be used to establish that @{text h'} is a norm-preserving extension of @{text h}.
           \label{ex-xi-use}\skp *}
        proof -
          from h have "\<exists>xi. \<forall>y \<in> H. - p (y + x') - h y \<le> xi
                          \<and> xi \<le> p (y + x') - h y"
          proof (rule ex_xi)
            fix u v assume "u \<in> H"  "v \<in> H"
            from h have "h v - h u = h (v - u)"
              by (simp! add: linearform_diff)
            also have "... \<le> p (v - u)"
              by (simp!)
            also have "v - u = x' + - x' + v + - u"
              by (simp! add: diff_eq1)
            also have "... = v + x' + - (u + x')"
              by (simp!)
            also have "... = (v + x') - (u + x')"
              by (simp! add: diff_eq1)
            also have "p ... \<le> p (v + x') + p (u + x')"
              by (rule seminorm_diff_subadditive) (simp_all!)
            finally have "h v - h u \<le> p (v + x') + p (u + x')" .

            thus "- p (u + x') - h u \<le> p (v + x') - h v"
              by (rule real_diff_ineq_swap)
          qed
          thus ?thesis ..
        qed

        def h' \<equiv> "\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H
                       in h y + a * xi"
        -- {* Define the extension @{text h'} of @{text h} to @{text H'} using @{text \<xi>}. \skp *}
        show ?thesis
        proof
          show "g \<subseteq> graph H' h' \<and> g \<noteq> graph H' h'"
          -- {* Show that @{text h'} is an extension of @{text h} \dots \skp *}
          proof
            show "g \<subseteq> graph H' h'"
            proof -
              have  "graph H h \<subseteq> graph H' h'"
              proof (rule graph_extI)
                fix t assume "t \<in> H"
                have "(SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H)
                     = (t, Numeral0)"
                  by (rule decomp_H'_H) (assumption+, rule x')
                thus "h t = h' t" by (simp! add: Let_def)
              next
                show "H \<subseteq> H'"
                proof (rule subspace_subset)
                  show "is_subspace H H'"
                  proof (unfold H'_def, rule subspace_vs_sum1)
                    show "is_vectorspace H" ..
                    show "is_vectorspace (lin x')" ..
                  qed
                qed
              qed
              thus ?thesis by (simp!)
            qed
            show "g \<noteq> graph H' h'"
            proof -
              have "graph H h \<noteq> graph H' h'"
              proof
                assume e: "graph H h = graph H' h'"
                have "x' \<in> H'"
                proof (unfold H'_def, rule vs_sumI)
                  show "x' = 0 + x'" by (simp!)
                  from h show "0 \<in> H" ..
                  show "x' \<in> lin x'" by (rule x_lin_x)
                qed
                hence "(x', h' x') \<in> graph H' h'" ..
                with e have "(x', h' x') \<in> graph H h" by simp
                hence "x' \<in> H" ..
                thus False by contradiction
              qed
              thus ?thesis by (simp!)
            qed
          qed
          show "graph H' h' \<in> M"
          -- {* and @{text h'} is norm-preserving. \skp *}
          proof -
            have "graph H' h' \<in> norm_pres_extensions E p F f"
            proof (rule norm_pres_extensionI2)
              show "is_linearform H' h'"
                by (rule h'_lf) (simp! add: x')+
              show "is_subspace H' E"
                by (unfold H'_def)
                  (rule vs_sum_subspace [OF _ lin_subspace])
              have "is_subspace F H" .
              also from h lin_vs
              have [folded H'_def]: "is_subspace H (H + lin x')" ..
              finally (subspace_trans [OF _ h])
              show f_h': "is_subspace F H'" .

              show "graph F f \<subseteq> graph H' h'"
              proof (rule graph_extI)
                fix x assume "x \<in> F"
                have "f x = h x" ..
                also have " ... = h x + Numeral0 * xi" by simp
                also
                have "... = (let (y, a) = (x, Numeral0) in h y + a * xi)"
                  by (simp add: Let_def)
                also have
                  "(x, Numeral0) = (SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H)"
                  by (rule decomp_H'_H [symmetric]) (simp! add: x')+
                also have
                  "(let (y, a) = (SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H)
                    in h y + a * xi) = h' x" by (simp!)
                finally show "f x = h' x" .
              next
                from f_h' show "F \<subseteq> H'" ..
              qed

              show "\<forall>x \<in> H'. h' x \<le> p x"
                by (rule h'_norm_pres) (assumption+, rule x')
            qed
            thus "graph H' h' \<in> M" by (simp!)
          qed
        qed
      qed
      hence "\<not> (\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x)" by simp
        -- {* So the graph @{text g} of @{text h} cannot be maximal. Contradiction! \skp *}
      thus "H = E" by contradiction
    qed
    thus "\<exists>h. is_linearform E h \<and> (\<forall>x \<in> F. h x = f x)
      \<and> (\<forall>x \<in> E. h x \<le> p x)"
    proof (intro exI conjI)
      assume eq: "H = E"
      from eq show "is_linearform E h" by (simp!)
      show "\<forall>x \<in> F. h x = f x"
      proof
        fix x assume "x \<in> F" have "f x = h x " ..
        thus "h x = f x" ..
      qed
      from eq show "\<forall>x \<in> E. h x \<le> p x" by (blast!)
    qed
  qed
qed


subsection  {* Alternative formulation *}

text {*
  The following alternative formulation of the Hahn-Banach
  Theorem\label{abs-HahnBanach} uses the fact that for a real linear
  form @{text f} and a seminorm @{text p} the following inequations
  are equivalent:\footnote{This was shown in lemma @{thm [source]
  abs_ineq_iff} (see page \pageref{abs-ineq-iff}).}
  \begin{center}
  \begin{tabular}{lll}
  @{text "\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x"} & and &
  @{text "\<forall>x \<in> H. h x \<le> p x"} \\
  \end{tabular}
  \end{center}
*}

theorem abs_HahnBanach:
  "is_vectorspace E \<Longrightarrow> is_subspace F E \<Longrightarrow> is_linearform F f
  \<Longrightarrow> is_seminorm E p \<Longrightarrow> \<forall>x \<in> F. \<bar>f x\<bar> \<le> p x
  \<Longrightarrow> \<exists>g. is_linearform E g \<and> (\<forall>x \<in> F. g x = f x)
    \<and> (\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x)"
proof -
assume "is_vectorspace E"  "is_subspace F E"  "is_seminorm E p"
"is_linearform F f"  "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
have "\<forall>x \<in> F. f x \<le> p x"  by (rule abs_ineq_iff [THEN iffD1])
hence "\<exists>g. is_linearform E g \<and> (\<forall>x \<in> F. g x = f x)
          \<and> (\<forall>x \<in> E. g x \<le> p x)"
by (simp! only: HahnBanach)
thus ?thesis
proof (elim exE conjE)
fix g assume "is_linearform E g"  "\<forall>x \<in> F. g x = f x"
              "\<forall>x \<in> E. g x \<le> p x"
hence "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"
  by (simp! add: abs_ineq_iff [OF subspace_refl])
thus ?thesis by (intro exI conjI)
qed
qed

subsection {* The Hahn-Banach Theorem for normed spaces *}

text {*
  Every continuous linear form @{text f} on a subspace @{text F} of a
  norm space @{text E}, can be extended to a continuous linear form
  @{text g} on @{text E} such that @{text "\<parallel>f\<parallel> = \<parallel>g\<parallel>"}.
*}

theorem norm_HahnBanach:
  "is_normed_vectorspace E norm \<Longrightarrow> is_subspace F E
  \<Longrightarrow> is_linearform F f \<Longrightarrow> is_continuous F norm f
  \<Longrightarrow> \<exists>g. is_linearform E g
     \<and> is_continuous E norm g
     \<and> (\<forall>x \<in> F. g x = f x)
     \<and> \<parallel>g\<parallel>E,norm = \<parallel>f\<parallel>F,norm"
proof -
assume e_norm: "is_normed_vectorspace E norm"
assume f: "is_subspace F E"  "is_linearform F f"
assume f_cont: "is_continuous F norm f"
have e: "is_vectorspace E" ..
hence f_norm: "is_normed_vectorspace F norm" ..

txt{*
  We define a function @{text p} on @{text E} as follows:
  @{text "p x = \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"}
*}

def p \<equiv> "\<lambda>x. \<parallel>f\<parallel>F,norm * norm x"

txt {* @{text p} is a seminorm on @{text E}: *}

have q: "is_seminorm E p"
proof
fix x y a assume "x \<in> E"  "y \<in> E"

txt {* @{text p} is positive definite: *}

show "Numeral0 \<le> p x"
proof (unfold p_def, rule real_le_mult_order1a)
  from f_cont f_norm show "Numeral0 \<le> \<parallel>f\<parallel>F,norm" ..
  show "Numeral0 \<le> norm x" ..
qed

txt {* @{text p} is absolutely homogenous: *}

show "p (a \<cdot> x) = \<bar>a\<bar> * p x"
proof -
  have "p (a \<cdot> x) = \<parallel>f\<parallel>F,norm * norm (a \<cdot> x)"
    by (simp!)
  also have "norm (a \<cdot> x) = \<bar>a\<bar> * norm x"
    by (rule normed_vs_norm_abs_homogenous)
  also have "\<parallel>f\<parallel>F,norm * (\<bar>a\<bar> * norm x )
    = \<bar>a\<bar> * (\<parallel>f\<parallel>F,norm * norm x)"
    by (simp! only: real_mult_left_commute)
  also have "... = \<bar>a\<bar> * p x" by (simp!)
  finally show ?thesis .
qed

txt {* Furthermore, @{text p} is subadditive: *}

show "p (x + y) \<le> p x + p y"
proof -
  have "p (x + y) = \<parallel>f\<parallel>F,norm * norm (x + y)"
    by (simp!)
  also
  have "... \<le> \<parallel>f\<parallel>F,norm * (norm x + norm y)"
  proof (rule real_mult_le_le_mono1a)
    from f_cont f_norm show "Numeral0 \<le> \<parallel>f\<parallel>F,norm" ..
    show "norm (x + y) \<le> norm x + norm y" ..
  qed
  also have "... = \<parallel>f\<parallel>F,norm * norm x
                    + \<parallel>f\<parallel>F,norm * norm y"
    by (simp! only: real_add_mult_distrib2)
  finally show ?thesis by (simp!)
qed
qed

txt {* @{text f} is bounded by @{text p}. *}

have "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
proof
fix x assume "x \<in> F"
 from f_norm show "\<bar>f x\<bar> \<le> p x"
   by (simp! add: norm_fx_le_norm_f_norm_x)
qed

txt {*
  Using the fact that @{text p} is a seminorm and @{text f} is bounded
  by @{text p} we can apply the Hahn-Banach Theorem for real vector
  spaces. So @{text f} can be extended in a norm-preserving way to
  some function @{text g} on the whole vector space @{text E}.
*}

with e f q
have "\<exists>g. is_linearform E g \<and> (\<forall>x \<in> F. g x = f x)
        \<and> (\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x)"
by (simp! add: abs_HahnBanach)

thus ?thesis
proof (elim exE conjE)
fix g
assume "is_linearform E g" and a: "\<forall>x \<in> F. g x = f x"
   and b: "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"

show "\<exists>g. is_linearform E g
        \<and> is_continuous E norm g
        \<and> (\<forall>x \<in> F. g x = f x)
        \<and> \<parallel>g\<parallel>E,norm = \<parallel>f\<parallel>F,norm"
proof (intro exI conjI)

txt {*
  We furthermore have to show that @{text g} is also continuous:
*}

  show g_cont: "is_continuous E norm g"
  proof
    fix x assume "x \<in> E"
    with b show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>F,norm * norm x"
      by (simp add: p_def)
  qed

  txt {*
    To complete the proof, we show that
    @{text "\<parallel>g\<parallel> = \<parallel>f\<parallel>"}. \label{order_antisym} *}

  show "\<parallel>g\<parallel>E,norm = \<parallel>f\<parallel>F,norm"
    (is "?L = ?R")
  proof (rule order_antisym)

    txt {*
      First we show @{text "\<parallel>g\<parallel> \<le> \<parallel>f\<parallel>"}.  The function norm @{text
      "\<parallel>g\<parallel>"} is defined as the smallest @{text "c \<in> \<real>"} such that
      \begin{center}
      \begin{tabular}{l}
      @{text "\<forall>x \<in> E. \<bar>g x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
      \end{tabular}
      \end{center}
      \noindent Furthermore holds
      \begin{center}
      \begin{tabular}{l}
      @{text "\<forall>x \<in> E. \<bar>g x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"}
      \end{tabular}
      \end{center}
    *}

    have "\<forall>x \<in> E. \<bar>g x\<bar> \<le> \<parallel>f\<parallel>F,norm * norm x"
    proof
      fix x assume "x \<in> E"
      show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>F,norm * norm x"
        by (simp!)
    qed

    with g_cont e_norm show "?L \<le> ?R"
    proof (rule fnorm_le_ub)
      from f_cont f_norm show "Numeral0 \<le> \<parallel>f\<parallel>F,norm" ..
    qed

    txt{* The other direction is achieved by a similar
    argument. *}

    have "\<forall>x \<in> F. \<bar>f x\<bar> \<le> \<parallel>g\<parallel>E,norm * norm x"
    proof
      fix x assume "x \<in> F"
      from a have "g x = f x" ..
      hence "\<bar>f x\<bar> = \<bar>g x\<bar>" by simp
      also from g_cont
      have "... \<le> \<parallel>g\<parallel>E,norm * norm x"
      proof (rule norm_fx_le_norm_f_norm_x)
        show "x \<in> E" ..
      qed
      finally show "\<bar>f x\<bar> \<le> \<parallel>g\<parallel>E,norm * norm x" .
    qed
    thus "?R \<le> ?L"
    proof (rule fnorm_le_ub [OF f_cont f_norm])
      from g_cont show "Numeral0 \<le> \<parallel>g\<parallel>E,norm" ..
    qed
  qed
qed
qed
qed

end
