(*  Title:      HOLCF/Cprod.thy
    Author:     Franz Regensburger
*)

header {* The cpo of cartesian products *}

theory Cprod
imports Algebraic
begin

default_sort cpo

subsection {* Continuous case function for unit type *}

definition
  unit_when :: "'a \<rightarrow> unit \<rightarrow> 'a" where
  "unit_when = (\<Lambda> a _. a)"

translations
  "\<Lambda>(). t" == "CONST unit_when\<cdot>t"

lemma unit_when [simp]: "unit_when\<cdot>a\<cdot>u = a"
by (simp add: unit_when_def)

subsection {* Continuous version of split function *}

definition
  csplit :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> ('a * 'b) \<rightarrow> 'c" where
  "csplit = (\<Lambda> f p. f\<cdot>(fst p)\<cdot>(snd p))"

translations
  "\<Lambda>(CONST Pair x y). t" == "CONST csplit\<cdot>(\<Lambda> x y. t)"


subsection {* Convert all lemmas to the continuous versions *}

lemma csplit1 [simp]: "csplit\<cdot>f\<cdot>\<bottom> = f\<cdot>\<bottom>\<cdot>\<bottom>"
by (simp add: csplit_def)

lemma csplit_Pair [simp]: "csplit\<cdot>f\<cdot>(x, y) = f\<cdot>x\<cdot>y"
by (simp add: csplit_def)

subsection {* Cartesian product is an SFP domain *}

definition
  prod_approx :: "nat \<Rightarrow> udom \<times> udom \<rightarrow> udom \<times> udom"
where
  "prod_approx = (\<lambda>i. cprod_map\<cdot>(udom_approx i)\<cdot>(udom_approx i))"

lemma prod_approx: "approx_chain prod_approx"
proof (rule approx_chain.intro)
  show "chain (\<lambda>i. prod_approx i)"
    unfolding prod_approx_def by simp
  show "(\<Squnion>i. prod_approx i) = ID"
    unfolding prod_approx_def
    by (simp add: lub_distribs cprod_map_ID)
  show "\<And>i. finite_deflation (prod_approx i)"
    unfolding prod_approx_def
    by (intro finite_deflation_cprod_map finite_deflation_udom_approx)
qed

definition prod_sfp :: "sfp \<rightarrow> sfp \<rightarrow> sfp"
where "prod_sfp = sfp_fun2 prod_approx cprod_map"

lemma cast_prod_sfp:
  "cast\<cdot>(prod_sfp\<cdot>A\<cdot>B) = udom_emb prod_approx oo
    cprod_map\<cdot>(cast\<cdot>A)\<cdot>(cast\<cdot>B) oo udom_prj prod_approx"
unfolding prod_sfp_def
apply (rule cast_sfp_fun2 [OF prod_approx])
apply (erule (1) finite_deflation_cprod_map)
done

instantiation prod :: (sfp, sfp) sfp
begin

definition
  "emb = udom_emb prod_approx oo cprod_map\<cdot>emb\<cdot>emb"

definition
  "prj = cprod_map\<cdot>prj\<cdot>prj oo udom_prj prod_approx"

definition
  "sfp (t::('a \<times> 'b) itself) = prod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def
    using ep_pair_udom [OF prod_approx]
    by (intro ep_pair_comp ep_pair_cprod_map ep_pair_emb_prj)
next
  show "cast\<cdot>SFP('a \<times> 'b) = emb oo (prj :: udom \<rightarrow> 'a \<times> 'b)"
    unfolding emb_prod_def prj_prod_def sfp_prod_def cast_prod_sfp
    by (simp add: cast_SFP oo_def expand_cfun_eq cprod_map_map)
qed

end

lemma SFP_prod: "SFP('a::sfp \<times> 'b::sfp) = prod_sfp\<cdot>SFP('a)\<cdot>SFP('b)"
by (rule sfp_prod_def)

end
