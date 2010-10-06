(*  Title:      HOLCF/Library/Strict_Fun.thy
    Author:     Brian Huffman
*)

header {* The Strict Function Type *}

theory Strict_Fun
imports HOLCF
begin

pcpodef (open) ('a, 'b) sfun (infixr "->!" 0)
  = "{f :: 'a \<rightarrow> 'b. f\<cdot>\<bottom> = \<bottom>}"
by simp_all

type_notation (xsymbols)
  sfun  (infixr "\<rightarrow>!" 0)

text {* TODO: Define nice syntax for abstraction, application. *}

definition
  sfun_abs :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow>! 'b)"
where
  "sfun_abs = (\<Lambda> f. Abs_sfun (strictify\<cdot>f))"

definition
  sfun_rep :: "('a \<rightarrow>! 'b) \<rightarrow> 'a \<rightarrow> 'b"
where
  "sfun_rep = (\<Lambda> f. Rep_sfun f)"

lemma sfun_rep_beta: "sfun_rep\<cdot>f = Rep_sfun f"
  unfolding sfun_rep_def by (simp add: cont_Rep_sfun)

lemma sfun_rep_strict1 [simp]: "sfun_rep\<cdot>\<bottom> = \<bottom>"
  unfolding sfun_rep_beta by (rule Rep_sfun_strict)

lemma sfun_rep_strict2 [simp]: "sfun_rep\<cdot>f\<cdot>\<bottom> = \<bottom>"
  unfolding sfun_rep_beta by (rule Rep_sfun [simplified])

lemma strictify_cancel: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> strictify\<cdot>f = f"
  by (simp add: expand_cfun_eq strictify_conv_if)

lemma sfun_abs_sfun_rep: "sfun_abs\<cdot>(sfun_rep\<cdot>f) = f"
  unfolding sfun_abs_def sfun_rep_def
  apply (simp add: cont_Abs_sfun cont_Rep_sfun)
  apply (simp add: Rep_sfun_inject [symmetric] Abs_sfun_inverse)
  apply (simp add: expand_cfun_eq strictify_conv_if)
  apply (simp add: Rep_sfun [simplified])
  done

lemma sfun_rep_sfun_abs [simp]: "sfun_rep\<cdot>(sfun_abs\<cdot>f) = strictify\<cdot>f"
  unfolding sfun_abs_def sfun_rep_def
  apply (simp add: cont_Abs_sfun cont_Rep_sfun)
  apply (simp add: Abs_sfun_inverse)
  done

lemma ep_pair_sfun: "ep_pair sfun_rep sfun_abs"
apply default
apply (rule sfun_abs_sfun_rep)
apply (simp add: expand_cfun_below strictify_conv_if)
done

interpretation sfun: ep_pair sfun_rep sfun_abs
  by (rule ep_pair_sfun)

subsection {* Map functional for strict function space *}

definition
  sfun_map :: "('b \<rightarrow> 'a) \<rightarrow> ('c \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow>! 'c) \<rightarrow> ('b \<rightarrow>! 'd)"
where
  "sfun_map = (\<Lambda> a b. sfun_abs oo cfun_map\<cdot>a\<cdot>b oo sfun_rep)"

lemma sfun_map_ID: "sfun_map\<cdot>ID\<cdot>ID = ID"
  unfolding sfun_map_def
  by (simp add: cfun_map_ID expand_cfun_eq)

lemma sfun_map_map:
  assumes "f2\<cdot>\<bottom> = \<bottom>" and "g2\<cdot>\<bottom> = \<bottom>" shows
  "sfun_map\<cdot>f1\<cdot>g1\<cdot>(sfun_map\<cdot>f2\<cdot>g2\<cdot>p) =
    sfun_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>(\<Lambda> x. g1\<cdot>(g2\<cdot>x))\<cdot>p"
unfolding sfun_map_def
by (simp add: expand_cfun_eq strictify_cancel assms cfun_map_map)

lemma ep_pair_sfun_map:
  assumes 1: "ep_pair e1 p1"
  assumes 2: "ep_pair e2 p2"
  shows "ep_pair (sfun_map\<cdot>p1\<cdot>e2) (sfun_map\<cdot>e1\<cdot>p2)"
proof
  interpret e1p1: pcpo_ep_pair e1 p1
    unfolding pcpo_ep_pair_def by fact
  interpret e2p2: pcpo_ep_pair e2 p2
    unfolding pcpo_ep_pair_def by fact
  fix f show "sfun_map\<cdot>e1\<cdot>p2\<cdot>(sfun_map\<cdot>p1\<cdot>e2\<cdot>f) = f"
    unfolding sfun_map_def
    apply (simp add: sfun.e_eq_iff [symmetric] strictify_cancel)
    apply (rule ep_pair.e_inverse)
    apply (rule ep_pair_cfun_map [OF 1 2])
    done
  fix g show "sfun_map\<cdot>p1\<cdot>e2\<cdot>(sfun_map\<cdot>e1\<cdot>p2\<cdot>g) \<sqsubseteq> g"
    unfolding sfun_map_def
    apply (simp add: sfun.e_below_iff [symmetric] strictify_cancel)
    apply (rule ep_pair.e_p_below)
    apply (rule ep_pair_cfun_map [OF 1 2])
    done
qed

lemma deflation_sfun_map:
  assumes 1: "deflation d1"
  assumes 2: "deflation d2"
  shows "deflation (sfun_map\<cdot>d1\<cdot>d2)"
apply (simp add: sfun_map_def)
apply (rule deflation.intro)
apply simp
apply (subst strictify_cancel)
apply (simp add: cfun_map_def deflation_strict 1 2)
apply (simp add: cfun_map_def deflation.idem 1 2)
apply (simp add: sfun.e_below_iff [symmetric])
apply (subst strictify_cancel)
apply (simp add: cfun_map_def deflation_strict 1 2)
apply (rule deflation.below)
apply (rule deflation_cfun_map [OF 1 2])
done

lemma finite_deflation_sfun_map:
  assumes 1: "finite_deflation d1"
  assumes 2: "finite_deflation d2"
  shows "finite_deflation (sfun_map\<cdot>d1\<cdot>d2)"
proof (intro finite_deflation.intro finite_deflation_axioms.intro)
  interpret d1: finite_deflation d1 by fact
  interpret d2: finite_deflation d2 by fact
  have "deflation d1" and "deflation d2" by fact+
  thus "deflation (sfun_map\<cdot>d1\<cdot>d2)" by (rule deflation_sfun_map)
  from 1 2 have "finite_deflation (cfun_map\<cdot>d1\<cdot>d2)"
    by (rule finite_deflation_cfun_map)
  then have "finite {f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f = f}"
    by (rule finite_deflation.finite_fixes)
  moreover have "inj (\<lambda>f. sfun_rep\<cdot>f)"
    by (rule inj_onI, simp)
  ultimately have "finite ((\<lambda>f. sfun_rep\<cdot>f) -` {f. cfun_map\<cdot>d1\<cdot>d2\<cdot>f = f})"
    by (rule finite_vimageI)
  then show "finite {f. sfun_map\<cdot>d1\<cdot>d2\<cdot>f = f}"
    unfolding sfun_map_def sfun.e_eq_iff [symmetric]
    by (simp add: strictify_cancel
         deflation_strict `deflation d1` `deflation d2`)
qed

subsection {* Strict function space is an SFP domain *}

definition
  sfun_approx :: "nat \<Rightarrow> (udom \<rightarrow>! udom) \<rightarrow> (udom \<rightarrow>! udom)"
where
  "sfun_approx = (\<lambda>i. sfun_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma sfun_approx: "approx_chain sfun_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. sfun_approx i)"
    unfolding sfun_approx_def by simp
  show "(\<Squnion>i. sfun_approx i) = ID"
    unfolding sfun_approx_def
    by (simp add: lub_distribs sfun_map_ID)
  show "\<And>i. finite_deflation (sfun_approx i)"
    unfolding sfun_approx_def
    by (intro finite_deflation_sfun_map finite_deflation_udom_approx)
qed

definition sfun_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "sfun_sfp = sfp_fun2 sfun_approx sfun_map"

lemma cast_sfun_sfp:
  "cast\<cdot>(sfun_sfp\<cdot>A\<cdot>B) =
    udom_emb sfun_approx oo sfun_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj sfun_approx"
unfolding sfun_sfp_def
apply (rule cast_sfp_fun2 [OF sfun_approx])
apply (erule (1) finite_deflation_sfun_map)
done

instantiation sfun :: (sfp, sfp) sfp
begin

definition
  "emb = udom_emb sfun_approx oo sfun_map\<cdot>prj\<cdot>emb"

definition
  "prj = sfun_map\<cdot>emb\<cdot>prj oo udom_prj sfun_approx"

definition
  "sfp (t::('a \<rightarrow>! 'b) itself) = sfun_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def
    using ep_pair_udom [OF sfun_approx]
    by (intro ep_pair_comp ep_pair_sfun_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<rightarrow>! 'b) = emb oo (prj :: udom \<rightarrow> 'a \<rightarrow>! 'b)"
    unfolding emb_sfun_def prj_sfun_def sfp_sfun_def cast_sfun_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq sfun_map_map)
qed

end

text {* SFP of type constructor = type combinator *}

lemma SFP_sfun: "SFP('a::sfp \<rightarrow>! 'b::sfp) = sfun_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_sfun_def)

lemma isodefl_sfun:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sfun_map\<cdot>d1\<cdot>d2) (sfun_sfp\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sfun_sfp cast_isodefl)
apply (simp add: emb_sfun_def prj_sfun_def)
apply (simp add: sfun_map_map deflation_strict [OF isodefl_imp_deflation])
done

setup {*
  Domain_Isomorphism.add_type_constructor
    (@{type_name "sfun"}, @{term sfun_sfp}, @{const_name sfun_map}, @{thm SFP_sfun},
       @{thm isodefl_sfun}, @{thm sfun_map_ID}, @{thm deflation_sfun_map})
*}

end
