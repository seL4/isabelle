(*  Title:      HOL/HOLCF/Powerdomains.thy
    Author:     Brian Huffman
*)

section \<open>Powerdomains\<close>

theory Powerdomains
imports ConvexPD Domain
begin

subsection \<open>Universal domain embeddings\<close>

definition "upper_emb = udom_emb (\<lambda>i. upper_map\<cdot>(udom_approx i))"
definition "upper_prj = udom_prj (\<lambda>i. upper_map\<cdot>(udom_approx i))"

definition "lower_emb = udom_emb (\<lambda>i. lower_map\<cdot>(udom_approx i))"
definition "lower_prj = udom_prj (\<lambda>i. lower_map\<cdot>(udom_approx i))"

definition "convex_emb = udom_emb (\<lambda>i. convex_map\<cdot>(udom_approx i))"
definition "convex_prj = udom_prj (\<lambda>i. convex_map\<cdot>(udom_approx i))"

lemma ep_pair_upper: "ep_pair upper_emb upper_prj"
  unfolding upper_emb_def upper_prj_def
  by (simp add: ep_pair_udom approx_chain_upper_map)

lemma ep_pair_lower: "ep_pair lower_emb lower_prj"
  unfolding lower_emb_def lower_prj_def
  by (simp add: ep_pair_udom approx_chain_lower_map)

lemma ep_pair_convex: "ep_pair convex_emb convex_prj"
  unfolding convex_emb_def convex_prj_def
  by (simp add: ep_pair_udom approx_chain_convex_map)


subsection \<open>Deflation combinators\<close>

definition upper_defl :: "udom defl \<rightarrow> udom defl"
  where "upper_defl = defl_fun1 upper_emb upper_prj upper_map"

definition lower_defl :: "udom defl \<rightarrow> udom defl"
  where "lower_defl = defl_fun1 lower_emb lower_prj lower_map"

definition convex_defl :: "udom defl \<rightarrow> udom defl"
  where "convex_defl = defl_fun1 convex_emb convex_prj convex_map"

lemma cast_upper_defl:
  "cast\<cdot>(upper_defl\<cdot>A) = upper_emb oo upper_map\<cdot>(cast\<cdot>A) oo upper_prj"
using ep_pair_upper finite_deflation_upper_map
unfolding upper_defl_def by (rule cast_defl_fun1)

lemma cast_lower_defl:
  "cast\<cdot>(lower_defl\<cdot>A) = lower_emb oo lower_map\<cdot>(cast\<cdot>A) oo lower_prj"
using ep_pair_lower finite_deflation_lower_map
unfolding lower_defl_def by (rule cast_defl_fun1)

lemma cast_convex_defl:
  "cast\<cdot>(convex_defl\<cdot>A) = convex_emb oo convex_map\<cdot>(cast\<cdot>A) oo convex_prj"
using ep_pair_convex finite_deflation_convex_map
unfolding convex_defl_def by (rule cast_defl_fun1)


subsection \<open>Domain class instances\<close>

instantiation upper_pd :: ("domain") "domain"
begin

definition
  "emb = upper_emb oo upper_map\<cdot>emb"

definition
  "prj = upper_map\<cdot>prj oo upper_prj"

definition
  "defl (t::'a upper_pd itself) = upper_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a upper_pd u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a upper_pd u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a upper_pd itself) = liftdefl_of\<cdot>DEFL('a upper_pd)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a upper_pd)"
    unfolding emb_upper_pd_def prj_upper_pd_def
    by (intro ep_pair_comp ep_pair_upper ep_pair_upper_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a upper_pd) = emb oo (prj :: udom \<rightarrow> 'a upper_pd)"
    unfolding emb_upper_pd_def prj_upper_pd_def defl_upper_pd_def cast_upper_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff upper_map_map)
qed (fact liftemb_upper_pd_def liftprj_upper_pd_def liftdefl_upper_pd_def)+

end

instantiation lower_pd :: ("domain") "domain"
begin

definition
  "emb = lower_emb oo lower_map\<cdot>emb"

definition
  "prj = lower_map\<cdot>prj oo lower_prj"

definition
  "defl (t::'a lower_pd itself) = lower_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a lower_pd u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a lower_pd u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a lower_pd itself) = liftdefl_of\<cdot>DEFL('a lower_pd)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def
    by (intro ep_pair_comp ep_pair_lower ep_pair_lower_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a lower_pd) = emb oo (prj :: udom \<rightarrow> 'a lower_pd)"
    unfolding emb_lower_pd_def prj_lower_pd_def defl_lower_pd_def cast_lower_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff lower_map_map)
qed (fact liftemb_lower_pd_def liftprj_lower_pd_def liftdefl_lower_pd_def)+

end

instantiation convex_pd :: ("domain") "domain"
begin

definition
  "emb = convex_emb oo convex_map\<cdot>emb"

definition
  "prj = convex_map\<cdot>prj oo convex_prj"

definition
  "defl (t::'a convex_pd itself) = convex_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: 'a convex_pd u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> 'a convex_pd u) = u_map\<cdot>prj"

definition
  "liftdefl (t::'a convex_pd itself) = liftdefl_of\<cdot>DEFL('a convex_pd)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a convex_pd)"
    unfolding emb_convex_pd_def prj_convex_pd_def
    by (intro ep_pair_comp ep_pair_convex ep_pair_convex_map ep_pair_emb_prj)
next
  show "cast\<cdot>DEFL('a convex_pd) = emb oo (prj :: udom \<rightarrow> 'a convex_pd)"
    unfolding emb_convex_pd_def prj_convex_pd_def defl_convex_pd_def cast_convex_defl
    by (simp add: cast_DEFL oo_def cfun_eq_iff convex_map_map)
qed (fact liftemb_convex_pd_def liftprj_convex_pd_def liftdefl_convex_pd_def)+

end

lemma DEFL_upper: "DEFL('a::domain upper_pd) = upper_defl\<cdot>DEFL('a)"
by (rule defl_upper_pd_def)

lemma DEFL_lower: "DEFL('a::domain lower_pd) = lower_defl\<cdot>DEFL('a)"
by (rule defl_lower_pd_def)

lemma DEFL_convex: "DEFL('a::domain convex_pd) = convex_defl\<cdot>DEFL('a)"
by (rule defl_convex_pd_def)


subsection \<open>Isomorphic deflations\<close>

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


subsection \<open>Domain package setup for powerdomains\<close>

lemmas [domain_defl_simps] = DEFL_upper DEFL_lower DEFL_convex
lemmas [domain_map_ID] = upper_map_ID lower_map_ID convex_map_ID
lemmas [domain_isodefl] = isodefl_upper isodefl_lower isodefl_convex

lemmas [domain_deflation] =
  deflation_upper_map deflation_lower_map deflation_convex_map

setup \<open>
  fold Domain_Take_Proofs.add_rec_type
    [(\<^type_name>\<open>upper_pd\<close>, [true]),
     (\<^type_name>\<open>lower_pd\<close>, [true]),
     (\<^type_name>\<open>convex_pd\<close>, [true])]
\<close>

end
