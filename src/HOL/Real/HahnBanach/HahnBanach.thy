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
{\bf Hahn-Banach Theorem.}\quad
  Let $F$ be a subspace of a real vector space $E$, let $p$ be a semi-norm on
  $E$, and $f$ be a linear form defined on $F$ such that $f$ is bounded by
  $p$, i.e. $\All {x\in F} f\ap x \leq p\ap x$.  Then $f$ can be extended to
  a linear form $h$ on $E$ such that $h$ is norm-preserving, i.e. $h$ is also
  bounded by $p$.

\bigskip
{\bf Proof Sketch.}
\begin{enumerate}
\item Define $M$ as the set of norm-preserving extensions of $f$ to subspaces
  of $E$. The linear forms in $M$ are ordered by domain extension.
\item We show that every non-empty chain in $M$ has an upper bound in $M$.
\item With Zorn's Lemma we conclude that there is a maximal function $g$ in
  $M$.
\item The domain $H$ of $g$ is the whole space $E$, as shown by classical
  contradiction:
\begin{itemize}
\item Assuming $g$ is not defined on whole $E$, it can still be extended in a
  norm-preserving way to a super-space $H'$ of $H$.
\item Thus $g$ can not be maximal. Contradiction!
\end{itemize}
\end{enumerate}
\bigskip
*}

(*
text {* {\bf Theorem.} Let $f$ be a linear form defined on a subspace 
 $F$ of a real vector space $E$, such that $f$ is bounded by a seminorm 
 $p$. 

 Then $f$ can be extended  to a linear form $h$  on $E$ that is again
 bounded by $p$.

 \bigskip{\bf Proof Outline.}
 First we define the set $M$ of all norm-preserving extensions of $f$.
 We show that every chain in $M$ has an upper bound in $M$.
 With Zorn's lemma we can conclude that $M$ has a maximal element $g$.
 We further show by contradiction that the domain $H$ of $g$ is the whole
 vector space $E$. 
 If $H \neq E$, then $g$ can be extended in 
 a norm-preserving way to a greater vector space $H_0$. 
 So $g$ cannot be maximal in $M$.
 \bigskip
*}
*)

theorem HahnBanach:
  "[| is_vectorspace E; is_subspace F E; is_seminorm E p;
  is_linearform F f; \\<forall>x \\<in> F. f x <= p x |] 
  ==> \\<exists>h. is_linearform E h \\<and> (\\<forall>x \\<in> F. h x = f x)
        \\<and> (\\<forall>x \\<in> E. h x <= p x)"   
    -- {* Let $E$ be a vector space, $F$ a subspace of $E$, $p$ a seminorm on $E$, *}
    -- {* and $f$ a linear form on $F$ such that $f$ is bounded by $p$, *}
    -- {* then $f$ can be extended to a linear form $h$ on $E$ in a norm-preserving way. \skp *}
proof -
  assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p" 
   and "is_linearform F f" "\\<forall>x \\<in> F. f x <= p x"
  -- {* Assume the context of the theorem. \skp *}
  def M == "norm_pres_extensions E p F f"
  -- {* Define $M$ as the set of all norm-preserving extensions of $F$. \skp *}
  {
    fix c assume "c \\<in> chain M" "\\<exists>x. x \\<in> c"
    have "\\<Union>c \\<in> M"
    -- {* Show that every non-empty chain $c$ of $M$ has an upper bound in $M$: *}
    -- {* $\Union c$ is greater than any element of the chain $c$, so it suffices to show $\Union c \in M$. *}
    proof (unfold M_def, rule norm_pres_extensionI)
      show "\\<exists>H h. graph H h = \\<Union>c
              \\<and> is_linearform H h 
              \\<and> is_subspace H E 
              \\<and> is_subspace F H 
              \\<and> graph F f \\<subseteq> graph H h
              \\<and> (\\<forall>x \\<in> H. h x <= p x)"
      proof (intro exI conjI)
        let ?H = "domain (\\<Union>c)"
        let ?h = "funct (\\<Union>c)"

        show a: "graph ?H ?h = \\<Union>c" 
        proof (rule graph_domain_funct)
          fix x y z assume "(x, y) \\<in> \\<Union>c" "(x, z) \\<in> \\<Union>c"
          show "z = y" by (rule sup_definite)
        qed
        show "is_linearform ?H ?h" 
          by (simp! add: sup_lf a)
        show "is_subspace ?H E" 
          by (rule sup_subE, rule a) (simp!)+
        show "is_subspace F ?H" 
          by (rule sup_supF, rule a) (simp!)+
        show "graph F f \\<subseteq> graph ?H ?h" 
          by (rule sup_ext, rule a) (simp!)+
        show "\\<forall>x \\<in> ?H. ?h x <= p x" 
          by (rule sup_norm_pres, rule a) (simp!)+
      qed
    qed

  }
  hence "\\<exists>g \\<in> M. \\<forall>x \\<in> M. g \\<subseteq> x --> g = x" 
  -- {* With Zorn's Lemma we can conclude that there is a maximal element in $M$.\skp *}
  proof (rule Zorn's_Lemma)
    -- {* We show that $M$ is non-empty: *}
    have "graph F f \\<in> norm_pres_extensions E p F f"
    proof (rule norm_pres_extensionI2)
      have "is_vectorspace F" ..
      thus "is_subspace F F" ..
    qed (blast!)+ 
    thus "graph F f \\<in> M" by (simp!)
  qed
  thus ?thesis
  proof
    fix g assume "g \\<in> M" "\\<forall>x \\<in> M. g \\<subseteq> x --> g = x"
    -- {* We consider such a maximal element $g \in M$. \skp *}
    obtain H h where "graph H h = g" "is_linearform H h" 
      "is_subspace H E" "is_subspace F H" "graph F f \\<subseteq> graph H h" 
      "\\<forall>x \\<in> H. h x <= p x" 
      -- {* $g$ is a norm-preserving extension of $f$, in other words: *}
      -- {* $g$ is the graph of some linear form $h$ defined on a subspace $H$ of $E$, *}
      -- {* and $h$ is an extension of $f$ that is again bounded by $p$. \skp *}
    proof -
      have "\\<exists>H h. graph H h = g \\<and> is_linearform H h 
        \\<and> is_subspace H E \\<and> is_subspace F H
        \\<and> graph F f \\<subseteq> graph H h
        \\<and> (\\<forall>x \\<in> H. h x <= p x)" 
        by (simp! add: norm_pres_extension_D)
      thus ?thesis by (elim exE conjE) rule
    qed
    have h: "is_vectorspace H" ..
    have "H = E"
    -- {* We show that $h$ is defined on whole $E$ by classical contradiction. \skp *} 
    proof (rule classical)
      assume "H \\<noteq> E"
      -- {* Assume $h$ is not defined on whole $E$. Then show that $h$ can be extended *}
      -- {* in a norm-preserving way to a function $h'$ with the graph $g'$. \skp *}
      have "\\<exists>g' \\<in> M. g \\<subseteq> g' \\<and> g \\<noteq> g'"
      proof -
        obtain x' where "x' \\<in> E" "x' \\<notin> H" 
        -- {* Pick $x' \in E \setminus H$. \skp *}
        proof -
          have "\\<exists>x' \\<in> E. x' \\<notin> H"
          proof (rule set_less_imp_diff_not_empty)
            have "H \\<subseteq> E" ..
            thus "H \\<subset> E" ..
          qed
          thus ?thesis by blast
        qed
        have x': "x' \\<noteq> 0"
        proof (rule classical)
          presume "x' = 0"
          with h have "x' \\<in> H" by simp
          thus ?thesis by contradiction
        qed blast
        def H' == "H + lin x'"
        -- {* Define $H'$ as the direct sum of $H$ and the linear closure of $x'$. \skp *}
        obtain xi where "\\<forall>y \\<in> H. - p (y + x') - h y <= xi 
                          \\<and> xi <= p (y + x') - h y" 
        -- {* Pick a real number $\xi$ that fulfills certain inequations; this will *}
        -- {* be used to establish that $h'$ is a norm-preserving extension of $h$. 
           \label{ex-xi-use}\skp *}
        proof -
          from h have "\\<exists>xi. \\<forall>y \\<in> H. - p (y + x') - h y <= xi 
                          \\<and> xi <= p (y + x') - h y" 
          proof (rule ex_xi)
            fix u v assume "u \\<in> H" "v \\<in> H"
            from h have "h v - h u = h (v - u)"
              by (simp! add: linearform_diff)
            also have "... <= p (v - u)"
              by (simp!)
            also have "v - u = x' + - x' + v + - u"
              by (simp! add: diff_eq1)
            also have "... = v + x' + - (u + x')"
              by (simp!)
            also have "... = (v + x') - (u + x')"
              by (simp! add: diff_eq1)
            also have "p ... <= p (v + x') + p (u + x')"
              by (rule seminorm_diff_subadditive) (simp_all!)
            finally have "h v - h u <= p (v + x') + p (u + x')" .

            thus "- p (u + x') - h u <= p (v + x') - h v" 
              by (rule real_diff_ineq_swap)
          qed
          thus ?thesis by rule rule
        qed

        def h' == "\\<lambda>x. let (y,a) = SOME (y,a). x = y + a \\<cdot> x' \\<and> y \\<in> H
                       in (h y) + a * xi"
        -- {* Define the extension $h'$ of $h$ to $H'$ using $\xi$. \skp *}
        show ?thesis
        proof
          show "g \\<subseteq> graph H' h' \\<and> g \\<noteq> graph H' h'" 
          -- {* Show that $h'$ is an extension of $h$ \dots \skp *}
          proof
            show "g \\<subseteq> graph H' h'"
            proof -
              have  "graph H h \\<subseteq> graph H' h'"
              proof (rule graph_extI)
                fix t assume "t \\<in> H" 
                have "(SOME (y, a). t = y + a \\<cdot> x' \\<and> y \\<in> H)
                     = (t, #0)"
                  by (rule decomp_H'_H) (assumption+, rule x')
                thus "h t = h' t" by (simp! add: Let_def)
              next
                show "H \\<subseteq> H'"
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
            show "g \\<noteq> graph H' h'"
            proof -
              have "graph H h \\<noteq> graph H' h'"
              proof
                assume e: "graph H h = graph H' h'"
                have "x' \\<in> H'" 
                proof (unfold H'_def, rule vs_sumI)
                  show "x' = 0 + x'" by (simp!)
                  from h show "0 \\<in> H" ..
                  show "x' \\<in> lin x'" by (rule x_lin_x)
                qed
                hence "(x', h' x') \\<in> graph H' h'" ..
                with e have "(x', h' x') \\<in> graph H h" by simp
                hence "x' \\<in> H" ..
                thus False by contradiction
              qed
              thus ?thesis by (simp!)
            qed
          qed
          show "graph H' h' \\<in> M" 
          -- {* and $h'$ is norm-preserving. \skp *}
          proof -
            have "graph H' h' \\<in> norm_pres_extensions E p F f"
            proof (rule norm_pres_extensionI2)
              show "is_linearform H' h'"
                by (rule h'_lf) (simp! add: x')+
              show "is_subspace H' E" 
                by (unfold H'_def) 
                  (rule vs_sum_subspace [OF _ lin_subspace])
              have "is_subspace F H" .
              also from h lin_vs 
              have [fold H'_def]: "is_subspace H (H + lin x')" ..
              finally (subspace_trans [OF _ h]) 
              show f_h': "is_subspace F H'" .
            
              show "graph F f \\<subseteq> graph H' h'"
              proof (rule graph_extI)
                fix x assume "x \\<in> F"
                have "f x = h x" ..
                also have " ... = h x + #0 * xi" by simp
                also 
                have "... = (let (y,a) = (x, #0) in h y + a * xi)"
                  by (simp add: Let_def)
                also have 
                  "(x, #0) = (SOME (y, a). x = y + a \\<cdot> x' \\<and> y \\<in> H)"
                  by (rule decomp_H'_H [RS sym]) (simp! add: x')+
                also have 
                  "(let (y,a) = (SOME (y,a). x = y + a \\<cdot> x' \\<and> y \\<in> H)
                    in h y + a * xi) = h' x" by (simp!)
                finally show "f x = h' x" .
              next
                from f_h' show "F \\<subseteq> H'" ..
              qed
            
              show "\\<forall>x \\<in> H'. h' x <= p x"
                by (rule h'_norm_pres) (assumption+, rule x')
            qed
            thus "graph H' h' \\<in> M" by (simp!)
          qed
        qed
      qed
      hence "\\<not> (\\<forall>x \\<in> M. g \\<subseteq> x --> g = x)" by simp
	-- {* So the graph $g$ of $h$ cannot be maximal. Contradiction! \skp *}
      thus "H = E" by contradiction
    qed
    thus "\\<exists>h. is_linearform E h \\<and> (\\<forall>x \\<in> F. h x = f x) 
      \\<and> (\\<forall>x \\<in> E. h x <= p x)" 
    proof (intro exI conjI)
      assume eq: "H = E"
      from eq show "is_linearform E h" by (simp!)
      show "\\<forall>x \\<in> F. h x = f x"
      proof
	fix x assume "x \\<in> F" have "f x = h x " ..
	thus "h x = f x" ..
      qed
      from eq show "\\<forall>x \\<in> E. h x <= p x" by (force!)
    qed
  qed
qed


subsection  {* Alternative formulation *}

text {* The following alternative formulation of the Hahn-Banach
Theorem\label{abs-HahnBanach} uses the fact that for a real linear form
$f$ and a seminorm $p$ the
following inequations are equivalent:\footnote{This was shown in lemma
$\idt{abs{\dsh}ineq{\dsh}iff}$ (see page \pageref{abs-ineq-iff}).}
\begin{matharray}{ll}
\forall x\in H.\ap |h\ap x|\leq p\ap x& {\rm and}\\
\forall x\in H.\ap h\ap x\leq p\ap x\\
\end{matharray}
*}

theorem abs_HahnBanach:
"[| is_vectorspace E; is_subspace F E; is_linearform F f; 
is_seminorm E p; \\<forall>x \\<in> F. |f x| <= p x |]
==> \\<exists>g. is_linearform E g \\<and> (\\<forall>x \\<in> F. g x = f x)
 \\<and> (\\<forall>x \\<in> E. |g x| <= p x)"
proof -
assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p" 
"is_linearform F f"  "\\<forall>x \\<in> F. |f x| <= p x"
have "\\<forall>x \\<in> F. f x <= p x"  by (rule abs_ineq_iff [RS iffD1])
hence "\\<exists>g. is_linearform E g \\<and> (\\<forall>x \\<in> F. g x = f x) 
          \\<and> (\\<forall>x \\<in> E. g x <= p x)"
by (simp! only: HahnBanach)
thus ?thesis 
proof (elim exE conjE)
fix g assume "is_linearform E g" "\\<forall>x \\<in> F. g x = f x" 
              "\\<forall>x \\<in> E. g x <= p x"
hence "\\<forall>x \\<in> E. |g x| <= p x"
  by (simp! add: abs_ineq_iff [OF subspace_refl])
thus ?thesis by (intro exI conjI)
qed
qed

subsection {* The Hahn-Banach Theorem for normed spaces *}

text {* Every continuous linear form $f$ on a subspace $F$ of a
norm space $E$, can be extended to a continuous linear form $g$ on
$E$ such that $\fnorm{f} = \fnorm {g}$. *}

theorem norm_HahnBanach:
"[| is_normed_vectorspace E norm; is_subspace F E; 
is_linearform F f; is_continuous F norm f |] 
==> \\<exists>g. is_linearform E g
     \\<and> is_continuous E norm g 
     \\<and> (\\<forall>x \\<in> F. g x = f x) 
     \\<and> \\<parallel>g\\<parallel>E,norm = \\<parallel>f\\<parallel>F,norm"
proof -
assume e_norm: "is_normed_vectorspace E norm"
assume f: "is_subspace F E" "is_linearform F f"
assume f_cont: "is_continuous F norm f"
have e: "is_vectorspace E" ..
hence f_norm: "is_normed_vectorspace F norm" ..

txt{* We define a function $p$ on $E$ as follows:
\begin{matharray}{l}
p \: x = \fnorm f \cdot \norm x\\
\end{matharray}
*}

def p == "\\<lambda>x. \\<parallel>f\\<parallel>F,norm * norm x"

txt{* $p$ is a seminorm on $E$: *}

have q: "is_seminorm E p"
proof
fix x y a assume "x \\<in> E" "y \\<in> E"

txt{* $p$ is positive definite: *}

show "#0 <= p x"
proof (unfold p_def, rule real_le_mult_order1a)
  from f_cont f_norm show "#0 <= \\<parallel>f\\<parallel>F,norm" ..
  show "#0 <= norm x" ..
qed

txt{* $p$ is absolutely homogenous: *}

show "p (a \\<cdot> x) = |a| * p x"
proof - 
  have "p (a \\<cdot> x) = \\<parallel>f\\<parallel>F,norm * norm (a \\<cdot> x)"
    by (simp!)
  also have "norm (a \\<cdot> x) = |a| * norm x" 
    by (rule normed_vs_norm_abs_homogenous)
  also have "\\<parallel>f\\<parallel>F,norm * ( |a| * norm x ) 
    = |a| * (\\<parallel>f\\<parallel>F,norm * norm x)"
    by (simp! only: real_mult_left_commute)
  also have "... = |a| * p x" by (simp!)
  finally show ?thesis .
qed

txt{* Furthermore, $p$ is subadditive: *}

show "p (x + y) <= p x + p y"
proof -
  have "p (x + y) = \\<parallel>f\\<parallel>F,norm * norm (x + y)"
    by (simp!)
  also 
  have "... <= \\<parallel>f\\<parallel>F,norm * (norm x + norm y)"
  proof (rule real_mult_le_le_mono1a)
    from f_cont f_norm show "#0 <= \\<parallel>f\\<parallel>F,norm" ..
    show "norm (x + y) <= norm x + norm y" ..
  qed
  also have "... = \\<parallel>f\\<parallel>F,norm * norm x 
                    + \\<parallel>f\\<parallel>F,norm * norm y"
    by (simp! only: real_add_mult_distrib2)
  finally show ?thesis by (simp!)
qed
qed

txt{* $f$ is bounded by $p$. *} 

have "\\<forall>x \\<in> F. |f x| <= p x"
proof
fix x assume "x \\<in> F"
 from f_norm show "|f x| <= p x" 
   by (simp! add: norm_fx_le_norm_f_norm_x)
qed

txt{* Using the fact that $p$ is a seminorm and 
$f$ is bounded by $p$ we can apply the Hahn-Banach Theorem 
for real vector spaces. 
So $f$ can be extended in a norm-preserving way to some function
$g$ on the whole vector space $E$. *}

with e f q 
have "\\<exists>g. is_linearform E g \\<and> (\\<forall>x \\<in> F. g x = f x) 
        \\<and> (\\<forall>x \\<in> E. |g x| <= p x)"
by (simp! add: abs_HahnBanach)

thus ?thesis
proof (elim exE conjE) 
fix g
assume "is_linearform E g" and a: "\\<forall>x \\<in> F. g x = f x" 
   and b: "\\<forall>x \\<in> E. |g x| <= p x"

show "\\<exists>g. is_linearform E g 
        \\<and> is_continuous E norm g 
        \\<and> (\\<forall>x \\<in> F. g x = f x) 
        \\<and> \\<parallel>g\\<parallel>E,norm = \\<parallel>f\\<parallel>F,norm"
proof (intro exI conjI)

txt{* We furthermore have to show that 
$g$ is also continuous: *}

  show g_cont: "is_continuous E norm g"
  proof
    fix x assume "x \\<in> E"
    with b show "|g x| <= \\<parallel>f\\<parallel>F,norm * norm x"
      by (simp add: p_def) 
  qed 

  txt {* To complete the proof, we show that 
  $\fnorm g = \fnorm f$. \label{order_antisym} *}

  show "\\<parallel>g\\<parallel>E,norm = \\<parallel>f\\<parallel>F,norm"
    (is "?L = ?R")
  proof (rule order_antisym)

    txt{* First we show $\fnorm g \leq \fnorm f$.  The function norm
    $\fnorm g$ is defined as the smallest $c\in\bbbR$ such that
    \begin{matharray}{l}
    \All {x\in E} {|g\ap x| \leq c \cdot \norm x}
    \end{matharray}
    Furthermore holds
    \begin{matharray}{l}
    \All {x\in E} {|g\ap x| \leq \fnorm f \cdot \norm x}
    \end{matharray}
    *}
 
    have "\\<forall>x \\<in> E. |g x| <= \\<parallel>f\\<parallel>F,norm * norm x"
    proof
      fix x assume "x \\<in> E" 
      show "|g x| <= \\<parallel>f\\<parallel>F,norm * norm x"
        by (simp!)
    qed

    with g_cont e_norm show "?L <= ?R"
    proof (rule fnorm_le_ub)
      from f_cont f_norm show "#0 <= \\<parallel>f\\<parallel>F,norm" ..
    qed

    txt{* The other direction is achieved by a similar 
    argument. *}

    have "\\<forall>x \\<in> F. |f x| <= \\<parallel>g\\<parallel>E,norm * norm x"
    proof
      fix x assume "x \\<in> F" 
      from a have "g x = f x" ..
      hence "|f x| = |g x|" by simp
      also from g_cont
      have "... <= \\<parallel>g\\<parallel>E,norm * norm x"
      proof (rule norm_fx_le_norm_f_norm_x)
        show "x \\<in> E" ..
      qed
      finally show "|f x| <= \\<parallel>g\\<parallel>E,norm * norm x" .
    qed 
    thus "?R <= ?L" 
    proof (rule fnorm_le_ub [OF f_cont f_norm])
      from g_cont show "#0 <= \\<parallel>g\\<parallel>E,norm" ..
    qed
  qed
qed
qed
qed

end
