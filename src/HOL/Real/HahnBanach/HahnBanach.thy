theory HahnBanach = HahnBanachLemmas: text_raw {* \smallskip\\ *} (* from ~/Pub/TYPES99/HB/HahnBanach.thy *)

theorem HahnBanach:
  "is_vectorspace E \\<Longrightarrow> is_subspace F E \\<Longrightarrow> is_seminorm E p
  \\<Longrightarrow> is_linearform F f \\<Longrightarrow> \\<forall>x \\<in> F. f x \\<le> p x
  \\<Longrightarrow> \\<exists>h. is_linearform E h \\<and> (\\<forall>x \\<in> F. h x = f x) \\<and> (\\<forall>x \\<in> E. h x \\<le> p x)"   
    -- {* Let $E$ be a vector space, $F$ a subspace of $E$, $p$ a seminorm on $E$, *}
    -- {* and $f$ a linear form on $F$ such that $f$ is bounded by $p$, *}
    -- {* then $f$ can be extended to a linear form $h$ on $E$ in a norm-preserving way. \skp *}
proof -
  assume "is_vectorspace E" "is_subspace F E" "is_seminorm E p" 
   and "is_linearform F f" "\\<forall>x \\<in> F. f x \\<le> p x"
  -- {* Assume the context of the theorem. \skp *}
  def M == "norm_pres_extensions E p F f"
  -- {* Define $M$ as the set of all norm-preserving extensions of $F$. \skp *}
  {
    fix c assume "c \\<in> chain M" "\\<exists>x. x \\<in> c"
    have "\\<Union>c \\<in> M"
    txt {* Show that every non-empty chain $c$ of $M$ has an upper bound in $M$: *}
    txt {* $\Union c$ is greater than any element of the chain $c$, so it suffices to show $\Union c \in M$. *}
    proof (unfold M_def, rule norm_pres_extensionI)
      show "EX (H::'a set) h::'a => real. graph H h = Union c
              & is_linearform H h 
              & is_subspace H E 
              & is_subspace F H 
              & graph F f <= graph H h
              & (ALL x::'a:H. h x <= p x)"
      proof (intro exI conjI)
        let ?H = "domain (Union c)"
        let ?h = "funct (Union c)"

        show a: "graph ?H ?h = Union c" 
        proof (rule graph_domain_funct)
          fix x y z assume "(x, y) : Union c" "(x, z) : Union c"
          show "z = y" by (rule sup_definite)
        qed
        show "is_linearform ?H ?h" 
          by (simp! add: sup_lf a)
        show "is_subspace ?H E" thm sup_subE [OF _ _ _ a]
          by (rule sup_subE [OF _ _ _ a]) (simp !)+
  (*  FIXME       by (rule sup_subE, rule a) (simp!)+; *)
        show "is_subspace F ?H" 
          by (rule sup_supF [OF _ _ _ a]) (simp!)+
  (* FIXME        by (rule sup_supF, rule a) (simp!)+ *)
        show "graph F f <= graph ?H ?h" 
          by (rule sup_ext [OF _ _ _ a]) (simp!)+
  (*  FIXME      by (rule sup_ext, rule a) (simp!)+*)
        show "ALL x::'a:?H. ?h x <= p x" 
          by (rule sup_norm_pres [OF _ _ a]) (simp!)+
  (* FIXME        by (rule sup_norm_pres, rule a) (simp!)+ *)
      qed
    qed

  }
  hence "\\<exists>g \\<in> M. \\<forall>x \\<in> M. g \\<subseteq> x \\<longrightarrow> g = x" 
  txt {* With Zorn's Lemma we can conclude that there is a maximal element in $M$.\skp *}
  proof (rule Zorn's_Lemma)
    txt {* We show that $M$ is non-empty: *}
    have "graph F f : norm_pres_extensions E p F f"
    proof (rule norm_pres_extensionI2)
      have "is_vectorspace F" ..
      thus "is_subspace F F" ..
    qed (blast!)+ 
    thus "graph F f : M" by (simp!)
  qed
  thus ?thesis
  proof
    fix g assume "g \\<in> M" "\\<forall>x \\<in> M. g \\<subseteq> x \\<longrightarrow> g = x"
    -- {* We consider such a maximal element $g \in M$. \skp *}
    show ?thesis
      obtain H h where "graph H h = g" "is_linearform H h" 
        "is_subspace H E" "is_subspace F H" "graph F f \\<subseteq> graph H h" 
        "\\<forall>x \\<in> H. h x \\<le> p x" 
        txt {* $g$ is a norm-preserving extension of $f$, in other words: *}
        txt {* $g$ is the graph of some linear form $h$ defined on a subspace $H$ of $E$, *}
        txt {* and $h$ is an extension of $f$ that is again bounded by $p$. \skp *}
      proof -
        have "EX H h. graph H h = g & is_linearform H h 
          & is_subspace H E & is_subspace F H
          & graph F f <= graph H h
          & (ALL x:H. h x <= p x)" by (simp! add: norm_pres_extension_D)
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
          obtain x' where "x' \\<in> E" "x' \\<notin> H" 
          txt {* Pick $x' \in E \setminus H$. \skp *}
          proof -
            have "EX x':E. x'~:H"
            proof (rule set_less_imp_diff_not_empty)
              have "H <= E" ..
              thus "H < E" ..
            qed
            thus ?thesis by blast
          qed
          have x': "x' ~= \<zero>"
          proof (rule classical)
            presume "x' = \<zero>"
            with h have "x':H" by simp
            thus ?thesis by contradiction
          qed blast
          def H' == "H + lin x'"
          -- {* Define $H'$ as the direct sum of $H$ and the linear closure of $x'$. \skp *}
          show ?thesis
            obtain xi where "\\<forall>y \\<in> H. - p (y + x') - h y \\<le> xi 
                              \\<and> xi \\<le> p (y + x') - h y" sorry
            -- {* Pick a real number $\xi$ that fulfills certain inequations; this will *}
            -- {* be used to establish that $h'$ is a norm-preserving extension of $h$. \skp *}
            def h' == "\\<lambda>x. let (y,a) = \\<epsilon>(y,a). x = y + a \<prod> x' \\<and> y \\<in> H
                           in (h y) + a * xi"
            -- {* Define the extension $h'$ of $h$ to $H'$ using $\xi$. \skp *}
            show ?thesis
            proof
              show "g \\<subseteq> graph H' h' \\<and> g \\<noteq> graph H' h'" 
              txt {* Show that $h'$ is an extension of $h$ \dots \skp *}
proof
		show "g <= graph H' h'"
		proof -
		  have  "graph H h <= graph H' h'"
                  proof (rule graph_extI)
		    fix t assume "t:H" 
		    have "(SOME (y, a). t = y + a \<prod> x' & y : H)
                         = (t, #0)" 
		      by (rule decomp_H0_H [OF _ _ _ _ _ x'])
		    thus "h t = h' t" by (simp! add: Let_def)
		  next
		    show "H <= H'"
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
                show "g ~= graph H' h'"
		proof -
		  have "graph H h ~= graph H' h'"
		  proof
		    assume e: "graph H h = graph H' h'"
		    have "x' : H'" 
		    proof (unfold H'_def, rule vs_sumI)
		      show "x' = \<zero> + x'" by (simp!)
		      from h show "\<zero> : H" ..
		      show "x' : lin x'" by (rule x_lin_x)
		    qed
		    hence "(x', h' x') : graph H' h'" ..
		    with e have "(x', h' x') : graph H h" by simp
		    hence "x' : H" ..
		    thus False by contradiction
		  qed
		  thus ?thesis by (simp!)
		qed
              qed
	      show "graph H' h' \\<in> M" 
              txt {* and $h'$ is norm-preserving. \skp *} 
              proof -
		have "graph H' h' : norm_pres_extensions E p F f"
		proof (rule norm_pres_extensionI2)
		  show "is_linearform H' h'"
		    by (rule h0_lf [OF _ _ _ _ _ _ x']) (simp!)+
		  show "is_subspace H' E"
		    by (unfold H'_def) (rule vs_sum_subspace [OF _ lin_subspace])
		  have "is_subspace F H" .
		  also from h lin_vs 
		  have [fold H'_def]: "is_subspace H (H + lin x')" ..
		  finally (subspace_trans [OF _ h]) 
		  show f_h': "is_subspace F H'" .
		
		  show "graph F f <= graph H' h'"
		  proof (rule graph_extI)
		    fix x assume "x:F"
		    have "f x = h x" ..
		    also have " ... = h x + #0 * xi" by simp
		    also have "... = (let (y,a) = (x, #0) in h y + a * xi)"
		      by (simp add: Let_def)
		    also have 
		      "(x, #0) = (SOME (y, a). x = y + a (*) x' & y : H)"
		      by (rule decomp_H0_H [RS sym, OF _ _ _ _ _ x']) (simp!)+
		    also have 
		      "(let (y,a) = (SOME (y,a). x = y + a (*) x' & y : H)
                        in h y + a * xi) 
                      = h' x" by (simp!)
		    finally show "f x = h' x" .
		  next
		    from f_h' show "F <= H'" ..
		  qed
		
		  show "ALL x:H'. h' x <= p x"
		    by (rule h0_norm_pres [OF _ _ _ _ x'])
		qed
		thus "graph H' h' : M" by (simp!)
	      qed
            qed
          qed
        qed
        hence "\\<not>(\\<forall>x \\<in> M. g \\<subseteq> x \\<longrightarrow> g = x)" by simp
        -- {* So the graph $g$ of $h$ cannot be maximal. Contradiction! \skp *}
        thus "H = E" by contradiction
      qed
      thus "\\<exists>h. is_linearform E h \\<and> (\\<forall>x \\<in> F. h x = f x) 
          \\<and> (\\<forall>x \\<in> E. h x \\<le> p x)" 
      proof (intro exI conjI)
        assume eq: "H = E"
	from eq show "is_linearform E h" by (simp!)
	show "ALL x:F. h x = f x" 
	proof (intro ballI, rule sym)
	  fix x assume "x:F" show "f x = h x " ..
	qed
	from eq show "ALL x:E. h x <= p x" by (force!)
      qed
    qed
  qed
qed text_raw {* \smallskip\\ *}
end