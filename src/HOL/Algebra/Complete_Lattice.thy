(*  Title:      HOL/Algebra/Complete_Lattice.thy
    Author:     Clemens Ballarin, started 7 November 2003
    Copyright:  Clemens Ballarin

Most congruence rules by Stephan Hohe.
With additional contributions from Alasdair Armstrong and Simon Foster.
*)

theory Complete_Lattice
imports Lattice
begin

section \<open>Complete Lattices\<close>

locale weak_complete_lattice = weak_partial_order +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

sublocale weak_complete_lattice \<subseteq> weak_lattice
proof
  fix x y
  assume a: "x \<in> carrier L" "y \<in> carrier L"
  thus "\<exists>s. is_lub L s {x, y}"
    by (rule_tac sup_exists[of "{x, y}"], auto)
  from a show "\<exists>s. is_glb L s {x, y}"
    by (rule_tac inf_exists[of "{x, y}"], auto)
qed

text \<open>Introduction rule: the usual definition of complete lattice\<close>

lemma (in weak_partial_order) weak_complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
  by standard (auto intro: sup_exists inf_exists)

lemma (in weak_complete_lattice) dual_weak_complete_lattice:
  "weak_complete_lattice (inv_gorder L)"
proof -
  interpret dual: weak_lattice "inv_gorder L"
    by (metis dual_weak_lattice)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add:inf_exists sup_exists)
  done
qed

lemma (in weak_complete_lattice) supI:
  "[| !!l. least L l (Upper L A) ==> P l; A \<subseteq> carrier L |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L A) ==> P l"
  with sup_exists obtain s where "least L s (Upper L A)" by blast
  with L show "P (SOME l. least L l (Upper L A))"
  by (fast intro: someI2 weak_least_unique P)
qed

lemma (in weak_complete_lattice) sup_closed [simp]:
  "A \<subseteq> carrier L ==> \<Squnion>A \<in> carrier L"
  by (rule supI) simp_all

lemma (in weak_complete_lattice) sup_cong:
  assumes "A \<subseteq> carrier L" "B \<subseteq> carrier L" "A {.=} B"
  shows "\<Squnion> A .= \<Squnion> B"
proof -
  have "\<And> x. is_lub L x A \<longleftrightarrow> is_lub L x B"
    by (rule least_Upper_cong_r, simp_all add: assms)
  moreover have "\<Squnion> B \<in> carrier L"
    by (simp add: assms(2))
  ultimately show ?thesis
    by (simp add: sup_def)
qed

sublocale weak_complete_lattice \<subseteq> weak_bounded_lattice
  apply (unfold_locales)
  apply (metis Upper_empty empty_subsetI sup_exists)
  apply (metis Lower_empty empty_subsetI inf_exists)
done

lemma (in weak_complete_lattice) infI:
  "[| !!i. greatest L i (Lower L A) ==> P i; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. greatest L l (Lower L A) ==> P l"
  with inf_exists obtain s where "greatest L s (Lower L A)" by blast
  with L show "P (SOME l. greatest L l (Lower L A))"
  by (fast intro: someI2 weak_greatest_unique P)
qed

lemma (in weak_complete_lattice) inf_closed [simp]:
  "A \<subseteq> carrier L ==> \<Sqinter>A \<in> carrier L"
  by (rule infI) simp_all

lemma (in weak_complete_lattice) inf_cong:
  assumes "A \<subseteq> carrier L" "B \<subseteq> carrier L" "A {.=} B"
  shows "\<Sqinter> A .= \<Sqinter> B"
proof -
  have "\<And> x. is_glb L x A \<longleftrightarrow> is_glb L x B"
    by (rule greatest_Lower_cong_r, simp_all add: assms)
  moreover have "\<Sqinter> B \<in> carrier L"
    by (simp add: assms(2))
  ultimately show ?thesis
    by (simp add: inf_def)
qed

theorem (in weak_partial_order) weak_complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
proof (rule weak_complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed


text \<open>Supremum\<close>

declare (in partial_order) weak_sup_of_singleton [simp del]

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} = x"
  using weak_sup_of_singleton unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) = \<Squnion>{x, y, z}"
  using weak_join_assoc_lemma L unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  using weak_join_assoc L unfolding eq_is_equal .


text \<open>Infimum\<close>

declare (in partial_order) weak_inf_of_singleton [simp del]

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} = x"
  using weak_inf_of_singleton unfolding eq_is_equal .

text \<open>Condition on \<open>A\<close>: infimum exists.\<close>

lemma (in lower_semilattice) meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) = \<Sqinter>{x, y, z}"
  using weak_meet_assoc_lemma L unfolding eq_is_equal .

lemma (in lower_semilattice) meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  using weak_meet_assoc L unfolding eq_is_equal .


subsection \<open>Infimum Laws\<close>

context weak_complete_lattice
begin

lemma inf_glb: 
  assumes "A \<subseteq> carrier L"
  shows "greatest L (\<Sqinter>A) (Lower L A)"
proof -
  obtain i where "greatest L i (Lower L A)"
    by (metis assms inf_exists)

  thus ?thesis
    apply (simp add: inf_def)
    apply (rule someI2[of _ "i"])
    apply (auto)
  done
qed

lemma inf_lower:
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "\<Sqinter>A \<sqsubseteq> x"
  by (metis assms greatest_Lower_below inf_glb)

lemma inf_greatest: 
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x)"
  shows "z \<sqsubseteq> \<Sqinter>A"
  by (metis Lower_memI assms greatest_le inf_glb)

lemma weak_inf_empty [simp]: "\<Sqinter>{} .= \<top>"
  by (metis Lower_empty empty_subsetI inf_glb top_greatest weak_greatest_unique)

lemma weak_inf_carrier [simp]: "\<Sqinter>carrier L .= \<bottom>"
  by (metis bottom_weak_eq inf_closed inf_lower subset_refl)

lemma weak_inf_insert [simp]: 
  "\<lbrakk> a \<in> carrier L; A \<subseteq> carrier L \<rbrakk> \<Longrightarrow> \<Sqinter>insert a A .= a \<sqinter> \<Sqinter>A"
  apply (rule weak_le_antisym)
  apply (force intro: meet_le inf_greatest inf_lower inf_closed)
  apply (rule inf_greatest)
  apply (force)
  apply (force intro: inf_closed)
  apply (auto)
  apply (metis inf_closed meet_left)
  apply (force intro: le_trans inf_closed meet_right meet_left inf_lower)
done


subsection \<open>Supremum Laws\<close>

lemma sup_lub: 
  assumes "A \<subseteq> carrier L"
  shows "least L (\<Squnion>A) (Upper L A)"
    by (metis Upper_is_closed assms least_closed least_cong supI sup_closed sup_exists weak_least_unique)

lemma sup_upper: 
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "x \<sqsubseteq> \<Squnion>A"
  by (metis assms least_Upper_above supI)

lemma sup_least:
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z)" 
  shows "\<Squnion>A \<sqsubseteq> z"
  by (metis Upper_memI assms least_le sup_lub)

lemma weak_sup_empty [simp]: "\<Squnion>{} .= \<bottom>"
  by (metis Upper_empty bottom_least empty_subsetI sup_lub weak_least_unique)

lemma weak_sup_carrier [simp]: "\<Squnion>carrier L .= \<top>"
  by (metis Lower_closed Lower_empty sup_closed sup_upper top_closed top_higher weak_le_antisym)

lemma weak_sup_insert [simp]: 
  "\<lbrakk> a \<in> carrier L; A \<subseteq> carrier L \<rbrakk> \<Longrightarrow> \<Squnion>insert a A .= a \<squnion> \<Squnion>A"
  apply (rule weak_le_antisym)
  apply (rule sup_least)
  apply (auto)
  apply (metis join_left sup_closed)
  apply (rule le_trans) defer
  apply (rule join_right)
  apply (auto)
  apply (rule join_le)
  apply (auto intro: sup_upper sup_least sup_closed)
done

end


subsection \<open>Fixed points of a lattice\<close>

definition "fps L f = {x \<in> carrier L. f x .=\<^bsub>L\<^esub> x}"

abbreviation "fpl L f \<equiv> L\<lparr>carrier := fps L f\<rparr>"

lemma (in weak_partial_order) 
  use_fps: "x \<in> fps L f \<Longrightarrow> f x .= x"
  by (simp add: fps_def)

lemma fps_carrier [simp]:
  "fps L f \<subseteq> carrier L"
  by (auto simp add: fps_def)

lemma (in weak_complete_lattice) fps_sup_image: 
  assumes "f \<in> carrier L \<rightarrow> carrier L" "A \<subseteq> fps L f" 
  shows "\<Squnion> (f ` A) .= \<Squnion> A"
proof -
  from assms(2) have AL: "A \<subseteq> carrier L"
    by (auto simp add: fps_def)
  
  show ?thesis
  proof (rule sup_cong, simp_all add: AL)
    from assms(1) AL show "f ` A \<subseteq> carrier L"
      by (auto)
    from assms(2) show "f ` A {.=} A"
      apply (auto simp add: fps_def)
      apply (rule set_eqI2)
      apply blast
      apply (rename_tac b)
      apply (rule_tac x="f b" in bexI)
      apply (metis (mono_tags, lifting) Ball_Collect assms(1) Pi_iff local.sym)
      apply (auto)
    done
  qed
qed

lemma (in weak_complete_lattice) fps_idem:
  "\<lbrakk> f \<in> carrier L \<rightarrow> carrier L; Idem f \<rbrakk> \<Longrightarrow> fps L f {.=} f ` carrier L"
  apply (rule set_eqI2)
  apply (auto simp add: idempotent_def fps_def)
  apply (metis Pi_iff local.sym)
  apply force
done

context weak_complete_lattice
begin

lemma weak_sup_pre_fixed_point: 
  assumes "f \<in> carrier L \<rightarrow> carrier L" "isotone L L f" "A \<subseteq> fps L f"
  shows "(\<Squnion>\<^bsub>L\<^esub> A) \<sqsubseteq>\<^bsub>L\<^esub> f (\<Squnion>\<^bsub>L\<^esub> A)"
proof (rule sup_least)
  from assms(3) show AL: "A \<subseteq> carrier L"
    by (auto simp add: fps_def)
  thus fA: "f (\<Squnion>A) \<in> carrier L"
    by (simp add: assms funcset_carrier[of f L L])
  fix x
  assume xA: "x \<in> A"
  hence "x \<in> fps L f"
    using assms subsetCE by blast
  hence "f x .=\<^bsub>L\<^esub> x"
    by (auto simp add: fps_def)
  moreover have "f x \<sqsubseteq>\<^bsub>L\<^esub> f (\<Squnion>\<^bsub>L\<^esub>A)"
    by (meson AL assms(2) subsetCE sup_closed sup_upper use_iso1 xA)
  ultimately show "x \<sqsubseteq>\<^bsub>L\<^esub> f (\<Squnion>\<^bsub>L\<^esub>A)"
    by (meson AL fA assms(1) funcset_carrier le_cong local.refl subsetCE xA)
qed

lemma weak_sup_post_fixed_point: 
  assumes "f \<in> carrier L \<rightarrow> carrier L" "isotone L L f" "A \<subseteq> fps L f"
  shows "f (\<Sqinter>\<^bsub>L\<^esub> A) \<sqsubseteq>\<^bsub>L\<^esub> (\<Sqinter>\<^bsub>L\<^esub> A)"
proof (rule inf_greatest)
  from assms(3) show AL: "A \<subseteq> carrier L"
    by (auto simp add: fps_def)
  thus fA: "f (\<Sqinter>A) \<in> carrier L"
    by (simp add: assms funcset_carrier[of f L L])
  fix x
  assume xA: "x \<in> A"
  hence "x \<in> fps L f"
    using assms subsetCE by blast
  hence "f x .=\<^bsub>L\<^esub> x"
    by (auto simp add: fps_def)
  moreover have "f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> f x"
    by (meson AL assms(2) inf_closed inf_lower subsetCE use_iso1 xA)   
  ultimately show "f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> x"
    by (meson AL assms(1) fA funcset_carrier le_cong_r subsetCE xA)
qed


subsubsection \<open>Least fixed points\<close>

lemma LFP_closed [intro, simp]:
  "LFP f \<in> carrier L"
  by (metis (lifting) LEAST_FP_def inf_closed mem_Collect_eq subsetI)

lemma LFP_lowerbound: 
  assumes "x \<in> carrier L" "f x \<sqsubseteq> x" 
  shows "LFP f \<sqsubseteq> x"
  by (auto intro:inf_lower assms simp add:LEAST_FP_def)

lemma LFP_greatest: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; f u \<sqsubseteq> u \<rbrakk> \<Longrightarrow> x \<sqsubseteq> u)"
  shows "x \<sqsubseteq> LFP f"
  by (auto simp add:LEAST_FP_def intro:inf_greatest assms)

lemma LFP_lemma2: 
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "f (LFP f) \<sqsubseteq> LFP f"
  using assms
  apply (auto simp add:Pi_def)
  apply (rule LFP_greatest)
  apply (metis LFP_closed)
  apply (metis LFP_closed LFP_lowerbound le_trans use_iso1)
done

lemma LFP_lemma3: 
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "LFP f \<sqsubseteq> f (LFP f)"
  using assms
  apply (auto simp add:Pi_def)
  apply (metis LFP_closed LFP_lemma2 LFP_lowerbound assms(2) use_iso2)
done

lemma LFP_weak_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> LFP f .= f (LFP f)"
  by (auto intro: LFP_lemma2 LFP_lemma3 funcset_mem)

lemma LFP_fixed_point [intro]:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "LFP f \<in> fps L f"
proof -
  have "f (LFP f) \<in> carrier L"
    using assms(2) by blast
  with assms show ?thesis
    by (simp add: LFP_weak_unfold fps_def local.sym)
qed

lemma LFP_least_fixed_point:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L" "x \<in> fps L f"
  shows "LFP f \<sqsubseteq> x"
  using assms by (force intro: LFP_lowerbound simp add: fps_def)
  
lemma LFP_idem: 
  assumes "f \<in> carrier L \<rightarrow> carrier L" "Mono f" "Idem f"
  shows "LFP f .= (f \<bottom>)"
proof (rule weak_le_antisym)
  from assms(1) show fb: "f \<bottom> \<in> carrier L"
    by (rule funcset_mem, simp)
  from assms show mf: "LFP f \<in> carrier L"
    by blast
  show "LFP f \<sqsubseteq> f \<bottom>"
  proof -
    have "f (f \<bottom>) .= f \<bottom>"
      by (auto simp add: fps_def fb assms(3) idempotent)
    moreover have "f (f \<bottom>) \<in> carrier L"
      by (rule funcset_mem[of f "carrier L"], simp_all add: assms fb)
    ultimately show ?thesis
      by (auto intro: LFP_lowerbound simp add: fb)
  qed
  show "f \<bottom> \<sqsubseteq> LFP f"
  proof -
    have "f \<bottom> \<sqsubseteq> f (LFP f)"
      by (auto intro: use_iso1[of _ f] simp add: assms)
    moreover have "... .= LFP f"
      using assms(1) assms(2) fps_def by force
    moreover from assms(1) have "f (LFP f) \<in> carrier L"
      by (auto)
    ultimately show ?thesis
      using fb by blast
  qed
qed


subsubsection \<open>Greatest fixed points\<close>
  
lemma GFP_closed [intro, simp]:
  "GFP f \<in> carrier L"
  by (auto intro:sup_closed simp add:GREATEST_FP_def)
  
lemma GFP_upperbound:
  assumes "x \<in> carrier L" "x \<sqsubseteq> f x"
  shows "x \<sqsubseteq> GFP f"
  by (auto intro:sup_upper assms simp add:GREATEST_FP_def)

lemma GFP_least: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; u \<sqsubseteq> f u \<rbrakk> \<Longrightarrow> u \<sqsubseteq> x)"
  shows "GFP f \<sqsubseteq> x"
  by (auto simp add:GREATEST_FP_def intro:sup_least assms)

lemma GFP_lemma2:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "GFP f \<sqsubseteq> f (GFP f)"
  using assms
  apply (auto simp add:Pi_def)
  apply (rule GFP_least)
  apply (metis GFP_closed)
  apply (metis GFP_closed GFP_upperbound le_trans use_iso2)
done

lemma GFP_lemma3:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "f (GFP f) \<sqsubseteq> GFP f"
  by (metis GFP_closed GFP_lemma2 GFP_upperbound assms funcset_mem use_iso2)
  
lemma GFP_weak_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> GFP f .= f (GFP f)"
  by (auto intro: GFP_lemma2 GFP_lemma3 funcset_mem)

lemma (in weak_complete_lattice) GFP_fixed_point [intro]:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "GFP f \<in> fps L f"
  using assms
proof -
  have "f (GFP f) \<in> carrier L"
    using assms(2) by blast
  with assms show ?thesis
    by (simp add: GFP_weak_unfold fps_def local.sym)
qed

lemma GFP_greatest_fixed_point:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L" "x \<in> fps L f"
  shows "x \<sqsubseteq> GFP f"
  using assms 
  by (rule_tac GFP_upperbound, auto simp add: fps_def, meson PiE local.sym weak_refl)
    
lemma GFP_idem: 
  assumes "f \<in> carrier L \<rightarrow> carrier L" "Mono f" "Idem f"
  shows "GFP f .= (f \<top>)"
proof (rule weak_le_antisym)
  from assms(1) show fb: "f \<top> \<in> carrier L"
    by (rule funcset_mem, simp)
  from assms show mf: "GFP f \<in> carrier L"
    by blast
  show "f \<top> \<sqsubseteq> GFP f"
  proof -
    have "f (f \<top>) .= f \<top>"
      by (auto simp add: fps_def fb assms(3) idempotent)
    moreover have "f (f \<top>) \<in> carrier L"
      by (rule funcset_mem[of f "carrier L"], simp_all add: assms fb)
    ultimately show ?thesis
      by (rule_tac GFP_upperbound, simp_all add: fb local.sym)
  qed
  show "GFP f \<sqsubseteq> f \<top>"
  proof -
    have "GFP f \<sqsubseteq> f (GFP f)"
      by (simp add: GFP_lemma2 assms(1) assms(2))
    moreover have "... \<sqsubseteq> f \<top>"
      by (auto intro: use_iso1[of _ f] simp add: assms)
    moreover from assms(1) have "f (GFP f) \<in> carrier L"
      by (auto)
    ultimately show ?thesis
      using fb local.le_trans by blast
  qed
qed

end


subsection \<open>Complete lattices where @{text eq} is the Equality\<close>

locale complete_lattice = partial_order +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

sublocale complete_lattice \<subseteq> lattice
proof
  fix x y
  assume a: "x \<in> carrier L" "y \<in> carrier L"
  thus "\<exists>s. is_lub L s {x, y}"
    by (rule_tac sup_exists[of "{x, y}"], auto)
  from a show "\<exists>s. is_glb L s {x, y}"
    by (rule_tac inf_exists[of "{x, y}"], auto)
qed

sublocale complete_lattice \<subseteq> weak?: weak_complete_lattice
  by standard (auto intro: sup_exists inf_exists)

lemma complete_lattice_lattice [simp]: 
  assumes "complete_lattice X"
  shows "lattice X"
proof -
  interpret c: complete_lattice X
    by (simp add: assms)
  show ?thesis
    by (unfold_locales)
qed

text \<open>Introduction rule: the usual definition of complete lattice\<close>

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
  by standard (auto intro: sup_exists inf_exists)

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)

subsection \<open>Fixed points\<close>

context complete_lattice
begin

lemma LFP_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> LFP f = f (LFP f)"
  using eq_is_equal weak.LFP_weak_unfold by auto

lemma LFP_const:
  "t \<in> carrier L \<Longrightarrow> LFP (\<lambda> x. t) = t"
  by (simp add: local.le_antisym weak.LFP_greatest weak.LFP_lowerbound)

lemma LFP_id:
  "LFP id = \<bottom>"
  by (simp add: local.le_antisym weak.LFP_lowerbound)

lemma GFP_unfold:
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> GFP f = f (GFP f)"
  using eq_is_equal weak.GFP_weak_unfold by auto

lemma GFP_const:
  "t \<in> carrier L \<Longrightarrow> GFP (\<lambda> x. t) = t"
  by (simp add: local.le_antisym weak.GFP_least weak.GFP_upperbound)

lemma GFP_id:
  "GFP id = \<top>"
  using weak.GFP_upperbound by auto

end


subsection \<open>Interval complete lattices\<close>
  
context weak_complete_lattice
begin

  lemma at_least_at_most_Sup:
    "\<lbrakk> a \<in> carrier L; b \<in> carrier L; a \<sqsubseteq> b \<rbrakk> \<Longrightarrow> \<Squnion> \<lbrace>a..b\<rbrace> .= b"
    apply (rule weak_le_antisym)
    apply (rule sup_least)
    apply (auto simp add: at_least_at_most_closed)
    apply (rule sup_upper)
    apply (auto simp add: at_least_at_most_closed)
  done

  lemma at_least_at_most_Inf:
    "\<lbrakk> a \<in> carrier L; b \<in> carrier L; a \<sqsubseteq> b \<rbrakk> \<Longrightarrow> \<Sqinter> \<lbrace>a..b\<rbrace> .= a"
    apply (rule weak_le_antisym)
    apply (rule inf_lower)
    apply (auto simp add: at_least_at_most_closed)
    apply (rule inf_greatest)
    apply (auto simp add: at_least_at_most_closed)
  done

end

lemma weak_complete_lattice_interval:
  assumes "weak_complete_lattice L" "a \<in> carrier L" "b \<in> carrier L" "a \<sqsubseteq>\<^bsub>L\<^esub> b"
  shows "weak_complete_lattice (L \<lparr> carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub> \<rparr>)"
proof -
  interpret L: weak_complete_lattice L
    by (simp add: assms)
  interpret weak_partial_order "L \<lparr> carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub> \<rparr>"
  proof -
    have "\<lbrace>a..b\<rbrace>\<^bsub>L\<^esub> \<subseteq> carrier L"
      by (auto, simp add: at_least_at_most_def)
    thus "weak_partial_order (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>)"
      by (simp add: L.weak_partial_order_axioms weak_partial_order_subset)
  qed

  show ?thesis
  proof
    fix A
    assume a: "A \<subseteq> carrier (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>)"
    show "\<exists>s. is_lub (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>) s A"
    proof (cases "A = {}")
      case True
      thus ?thesis
        by (rule_tac x="a" in exI, auto simp add: least_def assms)
    next
      case False
      show ?thesis
      proof (rule_tac x="\<Squnion>\<^bsub>L\<^esub> A" in exI, rule least_UpperI, simp_all)
        show b:"\<And> x. x \<in> A \<Longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> \<Squnion>\<^bsub>L\<^esub>A"
          using a by (auto intro: L.sup_upper, meson L.at_least_at_most_closed L.sup_upper subset_trans)
        show "\<And>y. y \<in> Upper (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>) A \<Longrightarrow> \<Squnion>\<^bsub>L\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> y"
          using a L.at_least_at_most_closed by (rule_tac L.sup_least, auto intro: funcset_mem simp add: Upper_def)
        from a show "A \<subseteq> \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>"
          by (auto)
        from a show "\<Squnion>\<^bsub>L\<^esub>A \<in> \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>"
          apply (rule_tac L.at_least_at_most_member)
          apply (auto)
          apply (meson L.at_least_at_most_closed L.sup_closed subset_trans)
          apply (meson False L.at_least_at_most_closed L.at_least_at_most_lower L.le_trans L.sup_closed b all_not_in_conv assms(2) contra_subsetD subset_trans)
          apply (rule L.sup_least)
          apply (auto simp add: assms)
          using L.at_least_at_most_closed apply blast
        done
      qed
    qed
    show "\<exists>s. is_glb (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>) s A"
    proof (cases "A = {}")
      case True
      thus ?thesis
        by (rule_tac x="b" in exI, auto simp add: greatest_def assms)
    next
      case False
      show ?thesis
      proof (rule_tac x="\<Sqinter>\<^bsub>L\<^esub> A" in exI, rule greatest_LowerI, simp_all)
        show b:"\<And>x. x \<in> A \<Longrightarrow> \<Sqinter>\<^bsub>L\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> x"
          using a L.at_least_at_most_closed by (force intro!: L.inf_lower)
        show "\<And>y. y \<in> Lower (L\<lparr>carrier := \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>\<rparr>) A \<Longrightarrow> y \<sqsubseteq>\<^bsub>L\<^esub> \<Sqinter>\<^bsub>L\<^esub>A"
           using a L.at_least_at_most_closed by (rule_tac L.inf_greatest, auto intro: funcset_carrier' simp add: Lower_def)
        from a show "A \<subseteq> \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>"
          by (auto)
        from a show "\<Sqinter>\<^bsub>L\<^esub>A \<in> \<lbrace>a..b\<rbrace>\<^bsub>L\<^esub>"
          apply (rule_tac L.at_least_at_most_member)
          apply (auto)
          apply (meson L.at_least_at_most_closed L.inf_closed subset_trans)
          apply (meson L.at_least_at_most_closed L.at_least_at_most_lower L.inf_greatest assms(2) set_rev_mp subset_trans)
          apply (meson False L.at_least_at_most_closed L.at_least_at_most_upper L.inf_closed L.le_trans b all_not_in_conv assms(3) contra_subsetD subset_trans)            
        done
      qed
    qed
  qed
qed


subsection \<open>Knaster-Tarski theorem and variants\<close>
  
text \<open>The set of fixed points of a complete lattice is itself a complete lattice\<close>

theorem Knaster_Tarski:
  assumes "weak_complete_lattice L" "f \<in> carrier L \<rightarrow> carrier L" "isotone L L f"
  shows "weak_complete_lattice (fpl L f)" (is "weak_complete_lattice ?L'")
proof -
  interpret L: weak_complete_lattice L
    by (simp add: assms)
  interpret weak_partial_order ?L'
  proof -
    have "{x \<in> carrier L. f x .=\<^bsub>L\<^esub> x} \<subseteq> carrier L"
      by (auto)
    thus "weak_partial_order ?L'"
      by (simp add: L.weak_partial_order_axioms weak_partial_order_subset)
  qed
  show ?thesis
  proof (unfold_locales, simp_all)
    fix A
    assume A: "A \<subseteq> fps L f"
    show "\<exists>s. is_lub (fpl L f) s A"
    proof
      from A have AL: "A \<subseteq> carrier L"
        by (meson fps_carrier subset_eq)

      let ?w = "\<Squnion>\<^bsub>L\<^esub> A"
      have w: "f (\<Squnion>\<^bsub>L\<^esub>A) \<in> carrier L"
        by (rule funcset_mem[of f "carrier L"], simp_all add: AL assms(2))

      have pf_w: "(\<Squnion>\<^bsub>L\<^esub> A) \<sqsubseteq>\<^bsub>L\<^esub> f (\<Squnion>\<^bsub>L\<^esub> A)"
        by (simp add: A L.weak_sup_pre_fixed_point assms(2) assms(3))

      have f_top_chain: "f ` \<lbrace>?w..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub> \<subseteq> \<lbrace>?w..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub>"
      proof (auto simp add: at_least_at_most_def)
        fix x
        assume b: "x \<in> carrier L" "\<Squnion>\<^bsub>L\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> x"
        from b show fx: "f x \<in> carrier L"
          using assms(2) by blast
        show "\<Squnion>\<^bsub>L\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> f x"
        proof -
          have "?w \<sqsubseteq>\<^bsub>L\<^esub> f ?w"
          proof (rule_tac L.sup_least, simp_all add: AL w)
            fix y
            assume c: "y \<in> A" 
            hence y: "y \<in> fps L f"
              using A subsetCE by blast
            with assms have "y .=\<^bsub>L\<^esub> f y"
            proof -
              from y have "y \<in> carrier L"
                by (simp add: fps_def)
              moreover hence "f y \<in> carrier L"
                by (rule_tac funcset_mem[of f "carrier L"], simp_all add: assms)
              ultimately show ?thesis using y
                by (rule_tac L.sym, simp_all add: L.use_fps)
            qed              
            moreover have "y \<sqsubseteq>\<^bsub>L\<^esub> \<Squnion>\<^bsub>L\<^esub>A"
              by (simp add: AL L.sup_upper c(1))
            ultimately show "y \<sqsubseteq>\<^bsub>L\<^esub> f (\<Squnion>\<^bsub>L\<^esub>A)"
              by (meson fps_def AL funcset_mem L.refl L.weak_complete_lattice_axioms assms(2) assms(3) c(1) isotone_def rev_subsetD weak_complete_lattice.sup_closed weak_partial_order.le_cong)
          qed
          thus ?thesis
            by (meson AL funcset_mem L.le_trans L.sup_closed assms(2) assms(3) b(1) b(2) use_iso2)
        qed
   
        show "f x \<sqsubseteq>\<^bsub>L\<^esub> \<top>\<^bsub>L\<^esub>"
          by (simp add: fx)
      qed
  
      let ?L' = "L\<lparr> carrier := \<lbrace>?w..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub> \<rparr>"

      interpret L': weak_complete_lattice ?L'
        by (auto intro: weak_complete_lattice_interval simp add: L.weak_complete_lattice_axioms AL)

      let ?L'' = "L\<lparr> carrier := fps L f \<rparr>"

      show "is_lub ?L'' (LFP\<^bsub>?L'\<^esub> f) A"
      proof (rule least_UpperI, simp_all)
        fix x
        assume "x \<in> Upper ?L'' A"
        hence "LFP\<^bsub>?L'\<^esub> f \<sqsubseteq>\<^bsub>?L'\<^esub> x"
          apply (rule_tac L'.LFP_lowerbound)
          apply (auto simp add: Upper_def)
          apply (simp add: A AL L.at_least_at_most_member L.sup_least set_rev_mp)          
          apply (simp add: Pi_iff assms(2) fps_def, rule_tac L.weak_refl)
          apply (auto)
          apply (rule funcset_mem[of f "carrier L"], simp_all add: assms(2))
        done
        thus " LFP\<^bsub>?L'\<^esub> f \<sqsubseteq>\<^bsub>L\<^esub> x"
          by (simp)
      next
        fix x
        assume xA: "x \<in> A"
        show "x \<sqsubseteq>\<^bsub>L\<^esub> LFP\<^bsub>?L'\<^esub> f"
        proof -
          have "LFP\<^bsub>?L'\<^esub> f \<in> carrier ?L'"
            by blast
          thus ?thesis
            by (simp, meson AL L.at_least_at_most_closed L.at_least_at_most_lower L.le_trans L.sup_closed L.sup_upper xA subsetCE)
        qed
      next
        show "A \<subseteq> fps L f"
          by (simp add: A)
      next
        show "LFP\<^bsub>?L'\<^esub> f \<in> fps L f"
        proof (auto simp add: fps_def)
          have "LFP\<^bsub>?L'\<^esub> f \<in> carrier ?L'"
            by (rule L'.LFP_closed)
          thus c:"LFP\<^bsub>?L'\<^esub> f \<in> carrier L"
             by (auto simp add: at_least_at_most_def)
          have "LFP\<^bsub>?L'\<^esub> f .=\<^bsub>?L'\<^esub> f (LFP\<^bsub>?L'\<^esub> f)"
          proof (rule "L'.LFP_weak_unfold", simp_all)
            show "f \<in> \<lbrace>\<Squnion>\<^bsub>L\<^esub>A..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub> \<rightarrow> \<lbrace>\<Squnion>\<^bsub>L\<^esub>A..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub>"
              apply (auto simp add: Pi_def at_least_at_most_def)
              using assms(2) apply blast
              apply (meson AL funcset_mem L.le_trans L.sup_closed assms(2) assms(3) pf_w use_iso2)
              using assms(2) apply blast
            done
            from assms(3) show "Mono\<^bsub>L\<lparr>carrier := \<lbrace>\<Squnion>\<^bsub>L\<^esub>A..\<top>\<^bsub>L\<^esub>\<rbrace>\<^bsub>L\<^esub>\<rparr>\<^esub> f"
              apply (auto simp add: isotone_def)
              using L'.weak_partial_order_axioms apply blast
              apply (meson L.at_least_at_most_closed subsetCE)
            done
          qed
          thus "f (LFP\<^bsub>?L'\<^esub> f) .=\<^bsub>L\<^esub> LFP\<^bsub>?L'\<^esub> f"
            by (simp add: L.equivalence_axioms funcset_carrier' c assms(2) equivalence.sym) 
        qed
      qed
    qed
    show "\<exists>i. is_glb (L\<lparr>carrier := fps L f\<rparr>) i A"
    proof
      from A have AL: "A \<subseteq> carrier L"
        by (meson fps_carrier subset_eq)

      let ?w = "\<Sqinter>\<^bsub>L\<^esub> A"
      have w: "f (\<Sqinter>\<^bsub>L\<^esub>A) \<in> carrier L"
        by (simp add: AL funcset_carrier' assms(2))

      have pf_w: "f (\<Sqinter>\<^bsub>L\<^esub> A) \<sqsubseteq>\<^bsub>L\<^esub> (\<Sqinter>\<^bsub>L\<^esub> A)"
        by (simp add: A L.weak_sup_post_fixed_point assms(2) assms(3))

      have f_bot_chain: "f ` \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub> \<subseteq> \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub>"
      proof (auto simp add: at_least_at_most_def)
        fix x
        assume b: "x \<in> carrier L" "x \<sqsubseteq>\<^bsub>L\<^esub> \<Sqinter>\<^bsub>L\<^esub>A"
        from b show fx: "f x \<in> carrier L"
          using assms(2) by blast
        show "f x \<sqsubseteq>\<^bsub>L\<^esub> \<Sqinter>\<^bsub>L\<^esub>A"
        proof -
          have "f ?w \<sqsubseteq>\<^bsub>L\<^esub> ?w"
          proof (rule_tac L.inf_greatest, simp_all add: AL w)
            fix y
            assume c: "y \<in> A" 
            with assms have "y .=\<^bsub>L\<^esub> f y"
              by (metis (no_types, lifting) A funcset_carrier'[OF assms(2)] L.sym fps_def mem_Collect_eq subset_eq)
            moreover have "\<Sqinter>\<^bsub>L\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> y"
              by (simp add: AL L.inf_lower c)
            ultimately show "f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> y"
              by (meson AL L.inf_closed L.le_trans c pf_w set_rev_mp w)
          qed
          thus ?thesis
            by (meson AL L.inf_closed L.le_trans assms(3) b(1) b(2) fx use_iso2 w)
        qed
   
        show "\<bottom>\<^bsub>L\<^esub> \<sqsubseteq>\<^bsub>L\<^esub> f x"
          by (simp add: fx)
      qed
  
      let ?L' = "L\<lparr> carrier := \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub> \<rparr>"

      interpret L': weak_complete_lattice ?L'
        by (auto intro!: weak_complete_lattice_interval simp add: L.weak_complete_lattice_axioms AL)

      let ?L'' = "L\<lparr> carrier := fps L f \<rparr>"

      show "is_glb ?L'' (GFP\<^bsub>?L'\<^esub> f) A"
      proof (rule greatest_LowerI, simp_all)
        fix x
        assume "x \<in> Lower ?L'' A"
        hence "x \<sqsubseteq>\<^bsub>?L'\<^esub> GFP\<^bsub>?L'\<^esub> f"
          apply (rule_tac L'.GFP_upperbound)
          apply (auto simp add: Lower_def)
          apply (meson A AL L.at_least_at_most_member L.bottom_lower L.weak_complete_lattice_axioms fps_carrier subsetCE weak_complete_lattice.inf_greatest)
          apply (simp add: funcset_carrier' L.sym assms(2) fps_def)          
        done
        thus "x \<sqsubseteq>\<^bsub>L\<^esub> GFP\<^bsub>?L'\<^esub> f"
          by (simp)
      next
        fix x
        assume xA: "x \<in> A"
        show "GFP\<^bsub>?L'\<^esub> f \<sqsubseteq>\<^bsub>L\<^esub> x"
        proof -
          have "GFP\<^bsub>?L'\<^esub> f \<in> carrier ?L'"
            by blast
          thus ?thesis
            by (simp, meson AL L.at_least_at_most_closed L.at_least_at_most_upper L.inf_closed L.inf_lower L.le_trans subsetCE xA)     
        qed
      next
        show "A \<subseteq> fps L f"
          by (simp add: A)
      next
        show "GFP\<^bsub>?L'\<^esub> f \<in> fps L f"
        proof (auto simp add: fps_def)
          have "GFP\<^bsub>?L'\<^esub> f \<in> carrier ?L'"
            by (rule L'.GFP_closed)
          thus c:"GFP\<^bsub>?L'\<^esub> f \<in> carrier L"
             by (auto simp add: at_least_at_most_def)
          have "GFP\<^bsub>?L'\<^esub> f .=\<^bsub>?L'\<^esub> f (GFP\<^bsub>?L'\<^esub> f)"
          proof (rule "L'.GFP_weak_unfold", simp_all)
            show "f \<in> \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub> \<rightarrow> \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub>"
              apply (auto simp add: Pi_def at_least_at_most_def)
              using assms(2) apply blast
              apply (simp add: funcset_carrier' assms(2))
              apply (meson AL funcset_carrier L.inf_closed L.le_trans assms(2) assms(3) pf_w use_iso2)
            done
            from assms(3) show "Mono\<^bsub>L\<lparr>carrier := \<lbrace>\<bottom>\<^bsub>L\<^esub>..?w\<rbrace>\<^bsub>L\<^esub>\<rparr>\<^esub> f"
              apply (auto simp add: isotone_def)
              using L'.weak_partial_order_axioms apply blast
              using L.at_least_at_most_closed apply (blast intro: funcset_carrier')
            done
          qed
          thus "f (GFP\<^bsub>?L'\<^esub> f) .=\<^bsub>L\<^esub> GFP\<^bsub>?L'\<^esub> f"
            by (simp add: L.equivalence_axioms funcset_carrier' c assms(2) equivalence.sym) 
        qed
      qed
    qed
  qed
qed

theorem Knaster_Tarski_top:
  assumes "weak_complete_lattice L" "isotone L L f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "\<top>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> GFP\<^bsub>L\<^esub> f"
proof -
  interpret L: weak_complete_lattice L
    by (simp add: assms)
  interpret L': weak_complete_lattice "fpl L f"
    by (rule Knaster_Tarski, simp_all add: assms)
  show ?thesis
  proof (rule L.weak_le_antisym, simp_all)
    show "\<top>\<^bsub>fpl L f\<^esub> \<sqsubseteq>\<^bsub>L\<^esub> GFP\<^bsub>L\<^esub> f"
      by (rule L.GFP_greatest_fixed_point, simp_all add: assms L'.top_closed[simplified])
    show "GFP\<^bsub>L\<^esub> f \<sqsubseteq>\<^bsub>L\<^esub> \<top>\<^bsub>fpl L f\<^esub>"
    proof -
      have "GFP\<^bsub>L\<^esub> f \<in> fps L f"
        by (rule L.GFP_fixed_point, simp_all add: assms)
      hence "GFP\<^bsub>L\<^esub> f \<in> carrier (fpl L f)"
        by simp
      hence "GFP\<^bsub>L\<^esub> f \<sqsubseteq>\<^bsub>fpl L f\<^esub> \<top>\<^bsub>fpl L f\<^esub>"
        by (rule L'.top_higher)
      thus ?thesis
        by simp
    qed
    show "\<top>\<^bsub>fpl L f\<^esub> \<in> carrier L"
    proof -
      have "carrier (fpl L f) \<subseteq> carrier L"
        by (auto simp add: fps_def)
      with L'.top_closed show ?thesis
        by blast
    qed
  qed
qed

theorem Knaster_Tarski_bottom:
  assumes "weak_complete_lattice L" "isotone L L f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "\<bottom>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> LFP\<^bsub>L\<^esub> f"
proof -
  interpret L: weak_complete_lattice L
    by (simp add: assms)
  interpret L': weak_complete_lattice "fpl L f"
    by (rule Knaster_Tarski, simp_all add: assms)
  show ?thesis
  proof (rule L.weak_le_antisym, simp_all)
    show "LFP\<^bsub>L\<^esub> f \<sqsubseteq>\<^bsub>L\<^esub> \<bottom>\<^bsub>fpl L f\<^esub>"
      by (rule L.LFP_least_fixed_point, simp_all add: assms L'.bottom_closed[simplified])
    show "\<bottom>\<^bsub>fpl L f\<^esub> \<sqsubseteq>\<^bsub>L\<^esub> LFP\<^bsub>L\<^esub> f"
    proof -
      have "LFP\<^bsub>L\<^esub> f \<in> fps L f"
        by (rule L.LFP_fixed_point, simp_all add: assms)
      hence "LFP\<^bsub>L\<^esub> f \<in> carrier (fpl L f)"
        by simp
      hence "\<bottom>\<^bsub>fpl L f\<^esub> \<sqsubseteq>\<^bsub>fpl L f\<^esub> LFP\<^bsub>L\<^esub> f"
        by (rule L'.bottom_lower)
      thus ?thesis
        by simp
    qed
    show "\<bottom>\<^bsub>fpl L f\<^esub> \<in> carrier L"
    proof -
      have "carrier (fpl L f) \<subseteq> carrier L"
        by (auto simp add: fps_def)
      with L'.bottom_closed show ?thesis
        by blast
    qed
  qed
qed

text \<open>If a function is both idempotent and isotone then the image of the function forms a complete lattice\<close>
  
theorem Knaster_Tarski_idem:
  assumes "complete_lattice L" "f \<in> carrier L \<rightarrow> carrier L" "isotone L L f" "idempotent L f"
  shows "complete_lattice (L\<lparr>carrier := f ` carrier L\<rparr>)"
proof -
  interpret L: complete_lattice L
    by (simp add: assms)
  have "fps L f = f ` carrier L"
    using L.weak.fps_idem[OF assms(2) assms(4)]
    by (simp add: L.set_eq_is_eq)
  then interpret L': weak_complete_lattice "(L\<lparr>carrier := f ` carrier L\<rparr>)"
    by (metis Knaster_Tarski L.weak.weak_complete_lattice_axioms assms(2) assms(3))
  show ?thesis
    using L'.sup_exists L'.inf_exists
    by (unfold_locales, auto simp add: L.eq_is_equal)
qed

theorem Knaster_Tarski_idem_extremes:
  assumes "weak_complete_lattice L" "isotone L L f" "idempotent L f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "\<top>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> f (\<top>\<^bsub>L\<^esub>)" "\<bottom>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> f (\<bottom>\<^bsub>L\<^esub>)"
proof -
  interpret L: weak_complete_lattice "L"
    by (simp_all add: assms)
  interpret L': weak_complete_lattice "fpl L f"
    by (rule Knaster_Tarski, simp_all add: assms)
  have FA: "fps L f \<subseteq> carrier L"
    by (auto simp add: fps_def)
  show "\<top>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> f (\<top>\<^bsub>L\<^esub>)"
  proof -
    from FA have "\<top>\<^bsub>fpl L f\<^esub> \<in> carrier L"
    proof -
      have "\<top>\<^bsub>fpl L f\<^esub> \<in> fps L f"
        using L'.top_closed by auto
      thus ?thesis
        using FA by blast
    qed
    moreover with assms have "f \<top>\<^bsub>L\<^esub> \<in> carrier L"
      by (auto)

    ultimately show ?thesis
      using L.trans[OF Knaster_Tarski_top[of L f] L.GFP_idem[of f]]
      by (simp_all add: assms)
  qed
  show "\<bottom>\<^bsub>fpl L f\<^esub> .=\<^bsub>L\<^esub> f (\<bottom>\<^bsub>L\<^esub>)"
  proof -
    from FA have "\<bottom>\<^bsub>fpl L f\<^esub> \<in> carrier L"
    proof -
      have "\<bottom>\<^bsub>fpl L f\<^esub> \<in> fps L f"
        using L'.bottom_closed by auto
      thus ?thesis
        using FA by blast
    qed
    moreover with assms have "f \<bottom>\<^bsub>L\<^esub> \<in> carrier L"
      by (auto)

    ultimately show ?thesis
      using L.trans[OF Knaster_Tarski_bottom[of L f] L.LFP_idem[of f]]
      by (simp_all add: assms)
  qed
qed

theorem Knaster_Tarski_idem_inf_eq:
  assumes "weak_complete_lattice L" "isotone L L f" "idempotent L f" "f \<in> carrier L \<rightarrow> carrier L"
          "A \<subseteq> fps L f"
  shows "\<Sqinter>\<^bsub>fpl L f\<^esub> A .=\<^bsub>L\<^esub> f (\<Sqinter>\<^bsub>L\<^esub> A)"
proof -
  interpret L: weak_complete_lattice "L"
    by (simp_all add: assms)
  interpret L': weak_complete_lattice "fpl L f"
    by (rule Knaster_Tarski, simp_all add: assms)
  have FA: "fps L f \<subseteq> carrier L"
    by (auto simp add: fps_def)
  have A: "A \<subseteq> carrier L"
    using FA assms(5) by blast
  have fA: "f (\<Sqinter>\<^bsub>L\<^esub>A) \<in> fps L f"
    by (metis (no_types, lifting) A L.idempotent L.inf_closed PiE assms(3) assms(4) fps_def mem_Collect_eq)
  have infA: "\<Sqinter>\<^bsub>fpl L f\<^esub>A \<in> fps L f"
    by (rule L'.inf_closed[simplified], simp add: assms)
  show ?thesis
  proof (rule L.weak_le_antisym)
    show ic: "\<Sqinter>\<^bsub>fpl L f\<^esub>A \<in> carrier L"
      using FA infA by blast
    show fc: "f (\<Sqinter>\<^bsub>L\<^esub>A) \<in> carrier L"
      using FA fA by blast
    show "f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> \<Sqinter>\<^bsub>fpl L f\<^esub>A"
    proof -
      have "\<And>x. x \<in> A \<Longrightarrow> f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> x"
        by (meson A FA L.inf_closed L.inf_lower L.le_trans L.weak_sup_post_fixed_point assms(2) assms(4) assms(5) fA subsetCE)
      hence "f (\<Sqinter>\<^bsub>L\<^esub>A) \<sqsubseteq>\<^bsub>fpl L f\<^esub> \<Sqinter>\<^bsub>fpl L f\<^esub>A"
        by (rule_tac L'.inf_greatest, simp_all add: fA assms(3,5))
      thus ?thesis
        by (simp)
    qed
    show "\<Sqinter>\<^bsub>fpl L f\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> f (\<Sqinter>\<^bsub>L\<^esub>A)"
    proof -
      have "\<And>x. x \<in> A \<Longrightarrow> \<Sqinter>\<^bsub>fpl L f\<^esub>A \<sqsubseteq>\<^bsub>fpl L f\<^esub> x"
        by (rule L'.inf_lower, simp_all add: assms)
      hence "\<Sqinter>\<^bsub>fpl L f\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> (\<Sqinter>\<^bsub>L\<^esub>A)"
        apply (rule_tac L.inf_greatest, simp_all add: A)
        using FA infA apply blast
        done
      hence 1:"f(\<Sqinter>\<^bsub>fpl L f\<^esub>A) \<sqsubseteq>\<^bsub>L\<^esub> f(\<Sqinter>\<^bsub>L\<^esub>A)"
        by (metis (no_types, lifting) A FA L.inf_closed assms(2) infA subsetCE use_iso1)
      have 2:"\<Sqinter>\<^bsub>fpl L f\<^esub>A \<sqsubseteq>\<^bsub>L\<^esub> f (\<Sqinter>\<^bsub>fpl L f\<^esub>A)"
        by (metis (no_types, lifting) FA L.sym L.use_fps L.weak_complete_lattice_axioms PiE assms(4) infA subsetCE weak_complete_lattice_def weak_partial_order.weak_refl)
        
      show ?thesis  
        using FA fA infA by (auto intro!: L.le_trans[OF 2 1] ic fc, metis FA PiE assms(4) subsetCE)
    qed
  qed
qed  

subsection \<open>Examples\<close>

subsubsection \<open>The Powerset of a Set is a Complete Lattice\<close>

theorem powerset_is_complete_lattice:
  "complete_lattice \<lparr>carrier = Pow A, eq = op =, le = op \<subseteq>\<rparr>"
  (is "complete_lattice ?L")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?L"
    by standard auto
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "least ?L (\<Union> B) (Upper ?L B)"
    by (fastforce intro!: least_UpperI simp: Upper_def)
  then show "EX s. least ?L s (Upper ?L B)" ..
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "greatest ?L (\<Inter> B \<inter> A) (Lower ?L B)"
    txt \<open>@{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! \<close>
    by (fastforce intro!: greatest_LowerI simp: Lower_def)
  then show "EX i. greatest ?L i (Lower ?L B)" ..
qed

text \<open>Another example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}).\<close>


subsection \<open>Limit preserving functions\<close>

definition weak_sup_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"weak_sup_pres X Y f \<equiv> complete_lattice X \<and> complete_lattice Y \<and> (\<forall> A \<subseteq> carrier X. A \<noteq> {} \<longrightarrow> f (\<Squnion>\<^bsub>X\<^esub> A) = (\<Squnion>\<^bsub>Y\<^esub> (f ` A)))"

definition sup_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"sup_pres X Y f \<equiv> complete_lattice X \<and> complete_lattice Y \<and> (\<forall> A \<subseteq> carrier X. f (\<Squnion>\<^bsub>X\<^esub> A) = (\<Squnion>\<^bsub>Y\<^esub> (f ` A)))"

definition weak_inf_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"weak_inf_pres X Y f \<equiv> complete_lattice X \<and> complete_lattice Y \<and> (\<forall> A \<subseteq> carrier X. A \<noteq> {} \<longrightarrow> f (\<Sqinter>\<^bsub>X\<^esub> A) = (\<Sqinter>\<^bsub>Y\<^esub> (f ` A)))"

definition inf_pres :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
"inf_pres X Y f \<equiv> complete_lattice X \<and> complete_lattice Y \<and> (\<forall> A \<subseteq> carrier X. f (\<Sqinter>\<^bsub>X\<^esub> A) = (\<Sqinter>\<^bsub>Y\<^esub> (f ` A)))"

lemma weak_sup_pres:
  "sup_pres X Y f \<Longrightarrow> weak_sup_pres X Y f"
  by (simp add: sup_pres_def weak_sup_pres_def)

lemma weak_inf_pres:
  "inf_pres X Y f \<Longrightarrow> weak_inf_pres X Y f"
  by (simp add: inf_pres_def weak_inf_pres_def)

lemma sup_pres_is_join_pres:
  assumes "weak_sup_pres X Y f"
  shows "join_pres X Y f"
  using assms
  apply (simp add: join_pres_def weak_sup_pres_def, safe)
  apply (rename_tac x y)
  apply (drule_tac x="{x, y}" in spec)
  apply (auto simp add: join_def)
done

lemma inf_pres_is_meet_pres:
  assumes "weak_inf_pres X Y f"
  shows "meet_pres X Y f"
  using assms
  apply (simp add: meet_pres_def weak_inf_pres_def, safe)
  apply (rename_tac x y)
  apply (drule_tac x="{x, y}" in spec)
  apply (auto simp add: meet_def)
done

end
