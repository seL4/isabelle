(*  Title:      HOLCF/Powerdomains.thy
    Author:     Brian Huffman
*)

header {* Powerdomains *}

theory Powerdomains
imports ConvexPD Domain
begin

subsection {* Universal domain embeddings *}

definition upper_approx :: "nat \<Rightarrow> udom upper_pd \<rightarrow> udom upper_pd"
  where "upper_approx = (\<lambda>i. upper_map\<cdot>(udom_approx i))"

definition lower_approx :: "nat \<Rightarrow> udom lower_pd \<rightarrow> udom lower_pd"
  where "lower_approx = (\<lambda>i. lower_map\<cdot>(udom_approx i))"

definition convex_approx :: "nat \<Rightarrow> udom convex_pd \<rightarrow> udom convex_pd"
  where "convex_approx = (\<lambda>i. convex_map\<cdot>(udom_approx i))"

lemma upper_approx: "approx_chain upper_approx"
  using upper_map_ID finite_deflation_upper_map
  unfolding upper_approx_def by (rule approx_chain_lemma1)

lemma lower_approx: "approx_chain lower_approx"
  using lower_map_ID finite_deflation_lower_map
  unfolding lower_approx_def by (rule approx_chain_lemma1)

lemma convex_approx: "approx_chain convex_approx"
  using convex_map_ID finite_deflation_convex_map
  unfolding convex_approx_def by (rule approx_chain_lemma1)

subsection {* Deflation combinators *}

definition upper_defl :: "udom defl \<rightarrow> udom defl"
  where "upper_defl = defl_fun1 upper_approx upper_map"

definition lower_defl :: "udom defl \<rightarrow> udom defl"
  where "lower_defl = defl_fun1 lower_approx lower_map"

definition convex_defl :: "udom defl \<rightarrow> udom defl"
  where "convex_defl = defl_fun1 convex_approx convex_map"

lemma cast_upper_defl:
  "cast\<cdot>(upper_defl\<cdot>A) =
    udom_emb upper_approx oo upper_map\<cdot>(cast\<cdot>A) oo udom_prj upper_approx"
using upper_approx finite_deflation_upper_map
unfolding upper_defl_def by (rule cast_defl_fun1)

lemma cast_lower_defl:
  "cast\<cdot>(lower_defl\<cdot>A) =
    udom_emb lower_approx oo lower_map\<cdot>(cast\<cdot>A) oo udom_prj lower_approx"
using lower_approx finite_deflation_lower_map
unfolding lower_defl_def by (rule cast_defl_fun1)

lemma cast_convex_defl:
  "cast\<cdot>(convex_defl\<cdot>A) =
    udom_emb convex_approx oo convex_map\<cdot>(cast\<cdot>A) oo udom_prj convex_approx"
using convex_approx finite_deflation_convex_map
unfolding convex_defl_def by (rule cast_defl_fun1)

subsection {* Domain class instances *}

instantiation upper_pd :: ("domain") liftdomain
begin

definition
  "emb = udom_emb upper_approx oo upper_map\<cdot>emb"

definition
  "prj = upper_map\<cdot>prj oo udom_prj upper_approx"

definition
  "defl (t::'a upper_pd itself) = upper_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a upper_pd u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a upper_pd u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::'a upper_pd itself) = u_defl\<cdot>DEFL('a upper_pd)"

instance
using liftemb_upper_pd_def liftprj_upper_pd_def liftdefl_upper_pd_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a upper_pd)"
    unfolding emb_upper_pd_def prj_upper_pd_def
    using ep_pair_udom [OF upper_approx]
    by (intro ep_pair_comp ep_pair_upper_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a upper_pd) = emb oo (prj :: udom \<rightarrow> 'a upper_pd)"
    unfolding emb_upper_pd_def prj_upper_pd_def defl_upper_pd_def cast_upper_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff upper_map_map)
qed

end

instantiation lower_pd :: ("domain") liftdomain
begin

definition
  "emb = udom_emb lower_approx oo lower_map\<cdot>emb"

definition
  "prj = lower_map\<cdot>prj oo udom_prj lower_approx"

definition
  "defl (t::'a lower_pd itself) = lower_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a lower_pd u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a lower_pd u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::'a lower_pd itself) = u_defl\<cdot>DEFL('a lower_pd)"

instance
using liftemb_lower_pd_def liftprj_lower_pd_def liftdefl_lower_pd_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def
    using ep_pair_udom [OF lower_approx]
    by (intro ep_pair_comp ep_pair_lower_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a lower_pd) = emb oo (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def defl_lower_pd_def cast_lower_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff lower_map_map)
qed

end

instantiation convex_pd :: ("domain") liftdomain
begin

definition
  "emb = udom_emb convex_approx oo convex_map\<cdot>emb"

definition
  "prj = convex_map\<cdot>prj oo udom_prj convex_approx"

definition
  "defl (t::'a convex_pd itself) = convex_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a convex_pd u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"

definition
  "(liftprj :: udom \<rightarrow> 'a convex_pd u) = u_map\<cdot>prj oo udom_prj u_approx"

definition
  "liftdefl (t::'a convex_pd itself) = u_defl\<cdot>DEFL('a convex_pd)"

instance
using liftemb_convex_pd_def liftprj_convex_pd_def liftdefl_convex_pd_def
proof (rule liftdomain_class_intro)
  show "ep_pair emb (prj :: udom \<rightarrow> 'a convex_pd)"
    unfolding emb_convex_pd_def prj_convex_pd_def
    using ep_pair_udom [OF convex_approx]
    by (intro ep_pair_comp ep_pair_convex_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a convex_pd) = emb oo (prj :: udom \<rightarrow> 'a convex_pd)"
    unfolding emb_convex_pd_def prj_convex_pd_def defl_convex_pd_def cast_convex_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff convex_map_map)
qed

end

lemma DEFL_upper: "DEFL('a::domain upper_pd) = upper_defl\<cdot>DEFL('a)"
by (rule defl_upper_pd_def)

lemma DEFL_lower: "DEFL('a::domain lower_pd) = lower_defl\<cdot>DEFL('a)"
by (rule defl_lower_pd_def)

lemma DEFL_convex: "DEFL('a::domain convex_pd) = convex_defl\<cdot>DEFL('a)"
by (rule defl_convex_pd_def)

subsection {* Isomorphic deflations *}

lemma isodefl_upper:
  "isodefl d t \<Longrightarrow> isodefl (upper_map\<cdot>d) (upper_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_upper_defl cast_isodefl)
apply (simp add: emb_upper_pd_def prj_upper_pd_def)
apply (simp add: upper_map_map)
done

lemma isodefl_lower:
  "isodefl d t \<Longrightarrow> isodefl (lower_map\<cdot>d) (lower_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_lower_defl cast_isodefl)
apply (simp add: emb_lower_pd_def prj_lower_pd_def)
apply (simp add: lower_map_map)
done

lemma isodefl_convex:
  "isodefl d t \<Longrightarrow> isodefl (convex_map\<cdot>d) (convex_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_convex_defl cast_isodefl)
apply (simp add: emb_convex_pd_def prj_convex_pd_def)
apply (simp add: convex_map_map)
done

subsection {* Domain package setup for powerdomains *}

lemmas [domain_defl_simps] = DEFL_upper DEFL_lower DEFL_convex
lemmas [domain_map_ID] = upper_map_ID lower_map_ID convex_map_ID
lemmas [domain_isodefl] = isodefl_upper isodefl_lower isodefl_convex

lemmas [domain_deflation] =
  deflation_upper_map deflation_lower_map deflation_convex_map

setup {*
  fold Domain_Take_Proofs.add_rec_type
    [(@{type_name "upper_pd"}, [true]),
     (@{type_name "lower_pd"}, [true]),
     (@{type_name "convex_pd"}, [true])]
*}

end
