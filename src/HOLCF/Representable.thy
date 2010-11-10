(*  Title:      HOLCF/Representable.thy
    Author:     Brian Huffman
*)

header {* Representable Types *}

theory Representable
imports Algebraic Bifinite Universal Ssum One Fixrec Domain_Aux
uses
  ("Tools/repdef.ML")
  ("Tools/Domain/domain_isomorphism.ML")
begin

default_sort bifinite

subsection {* Representations of types *}

lemma emb_prj: "emb\<cdot>((prj\<cdot>x)::'a) = cast\<cdot>DEFL('a)\<cdot>x"
by (simp add: cast_DEFL)

lemma emb_prj_emb:
  fixes x :: "'a"
  assumes "DEFL('a) \<sqsubseteq> DEFL('b)"
  shows "emb\<cdot>(prj\<cdot>(emb\<cdot>x) :: 'b) = emb\<cdot>x"
unfolding emb_prj
apply (rule cast.belowD)
apply (rule monofun_cfun_arg [OF assms])
apply (simp add: cast_DEFL)
done

lemma prj_emb_prj:
  assumes "DEFL('a) \<sqsubseteq> DEFL('b)"
  shows "prj\<cdot>(emb\<cdot>(prj\<cdot>x :: 'b)) = (prj\<cdot>x :: 'a)"
 apply (rule emb_eq_iff [THEN iffD1])
 apply (simp only: emb_prj)
 apply (rule deflation_below_comp1)
   apply (rule deflation_cast)
  apply (rule deflation_cast)
 apply (rule monofun_cfun_arg [OF assms])
done

text {* Isomorphism lemmas used internally by the domain package: *}

lemma domain_abs_iso:
  fixes abs and rep
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "rep\<cdot>(abs\<cdot>x) = x"
unfolding abs_def rep_def
by (simp add: emb_prj_emb DEFL)

lemma domain_rep_iso:
  fixes abs and rep
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "abs\<cdot>(rep\<cdot>x) = x"
unfolding abs_def rep_def
by (simp add: emb_prj_emb DEFL)

subsection {* Deflations as sets *}

definition defl_set :: "defl \<Rightarrow> udom set"
where "defl_set A = {x. cast\<cdot>A\<cdot>x = x}"

lemma adm_defl_set: "adm (\<lambda>x. x \<in> defl_set A)"
unfolding defl_set_def by simp

lemma defl_set_bottom: "\<bottom> \<in> defl_set A"
unfolding defl_set_def by simp

lemma defl_set_cast [simp]: "cast\<cdot>A\<cdot>x \<in> defl_set A"
unfolding defl_set_def by simp

lemma defl_set_subset_iff: "defl_set A \<subseteq> defl_set B \<longleftrightarrow> A \<sqsubseteq> B"
apply (simp add: defl_set_def subset_eq cast_below_cast [symmetric])
apply (auto simp add: cast.belowI cast.belowD)
done

subsection {* Proving a subtype is representable *}

text {* Temporarily relax type constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::pcpo itself \<Rightarrow> defl"})
  , (@{const_name emb}, SOME @{typ "'a::pcpo \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::pcpo"})
  , (@{const_name liftdefl}, SOME @{typ "'a::pcpo itself \<Rightarrow> defl"})
  , (@{const_name liftemb}, SOME @{typ "'a::pcpo u \<rightarrow> udom"})
  , (@{const_name liftprj}, SOME @{typ "udom \<rightarrow> 'a::pcpo u"}) ]
*}

lemma typedef_rep_class:
  fixes Rep :: "'a::pcpo \<Rightarrow> udom"
  fixes Abs :: "udom \<Rightarrow> 'a::pcpo"
  fixes t :: defl
  assumes type: "type_definition Rep Abs (defl_set t)"
  assumes below: "op \<sqsubseteq> \<equiv> \<lambda>x y. Rep x \<sqsubseteq> Rep y"
  assumes emb: "emb \<equiv> (\<Lambda> x. Rep x)"
  assumes prj: "prj \<equiv> (\<Lambda> x. Abs (cast\<cdot>t\<cdot>x))"
  assumes defl: "defl \<equiv> (\<lambda> a::'a itself. t)"
  assumes liftemb: "(liftemb :: 'a u \<rightarrow> udom) \<equiv> udom_emb u_approx oo u_map\<cdot>emb"
  assumes liftprj: "(liftprj :: udom \<rightarrow> 'a u) \<equiv> u_map\<cdot>prj oo udom_prj u_approx"
  assumes liftdefl: "(liftdefl :: 'a itself \<Rightarrow> defl) \<equiv> (\<lambda>t. u_defl\<cdot>DEFL('a))"
  shows "OFCLASS('a, bifinite_class)"
using liftemb [THEN meta_eq_to_obj_eq]
using liftprj [THEN meta_eq_to_obj_eq]
proof (rule bifinite_class_intro)
  have emb_beta: "\<And>x. emb\<cdot>x = Rep x"
    unfolding emb
    apply (rule beta_cfun)
    apply (rule typedef_cont_Rep [OF type below adm_defl_set])
    done
  have prj_beta: "\<And>y. prj\<cdot>y = Abs (cast\<cdot>t\<cdot>y)"
    unfolding prj
    apply (rule beta_cfun)
    apply (rule typedef_cont_Abs [OF type below adm_defl_set])
    apply simp_all
    done
  have prj_emb: "\<And>x::'a. prj\<cdot>(emb\<cdot>x) = x"
    using type_definition.Rep [OF type]
    unfolding prj_beta emb_beta defl_set_def
    by (simp add: type_definition.Rep_inverse [OF type])
  have emb_prj: "\<And>y. emb\<cdot>(prj\<cdot>y :: 'a) = cast\<cdot>t\<cdot>y"
    unfolding prj_beta emb_beta
    by (simp add: type_definition.Abs_inverse [OF type])
  show "ep_pair (emb :: 'a \<rightarrow> udom) prj"
    apply default
    apply (simp add: prj_emb)
    apply (simp add: emb_prj cast.below)
    done
  show "cast\<cdot>DEFL('a) = emb oo (prj :: udom \<rightarrow> 'a)"
    by (rule cfun_eqI, simp add: defl emb_prj)
  show "LIFTDEFL('a) = u_defl\<cdot>DEFL('a)"
    unfolding liftdefl ..
qed

lemma typedef_DEFL:
  assumes "defl \<equiv> (\<lambda>a::'a::pcpo itself. t)"
  shows "DEFL('a::pcpo) = t"
unfolding assms ..

lemma typedef_LIFTDEFL:
  assumes "liftdefl \<equiv> (\<lambda>a::'a::pcpo itself. u_defl\<cdot>DEFL('a))"
  shows "LIFTDEFL('a::pcpo) = u_defl\<cdot>DEFL('a)"
unfolding assms ..

text {* Restore original typing constraints. *}

setup {*
  fold Sign.add_const_constraint
  [ (@{const_name defl}, SOME @{typ "'a::bifinite itself \<Rightarrow> defl"})
  , (@{const_name emb}, SOME @{typ "'a::bifinite \<rightarrow> udom"})
  , (@{const_name prj}, SOME @{typ "udom \<rightarrow> 'a::bifinite"})
  , (@{const_name liftdefl}, SOME @{typ "'a::predomain itself \<Rightarrow> defl"})
  , (@{const_name liftemb}, SOME @{typ "'a::predomain u \<rightarrow> udom"})
  , (@{const_name liftprj}, SOME @{typ "udom \<rightarrow> 'a::predomain u"}) ]
*}

use "Tools/repdef.ML"

subsection {* Isomorphic deflations *}

definition
  isodefl :: "('a \<rightarrow> 'a) \<Rightarrow> defl \<Rightarrow> bool"
where
  "isodefl d t \<longleftrightarrow> cast\<cdot>t = emb oo d oo prj"

lemma isodeflI: "(\<And>x. cast\<cdot>t\<cdot>x = emb\<cdot>(d\<cdot>(prj\<cdot>x))) \<Longrightarrow> isodefl d t"
unfolding isodefl_def by (simp add: cfun_eqI)

lemma cast_isodefl: "isodefl d t \<Longrightarrow> cast\<cdot>t = (\<Lambda> x. emb\<cdot>(d\<cdot>(prj\<cdot>x)))"
unfolding isodefl_def by (simp add: cfun_eqI)

lemma isodefl_strict: "isodefl d t \<Longrightarrow> d\<cdot>\<bottom> = \<bottom>"
unfolding isodefl_def
by (drule cfun_fun_cong [where x="\<bottom>"], simp)

lemma isodefl_imp_deflation:
  fixes d :: "'a \<rightarrow> 'a"
  assumes "isodefl d t" shows "deflation d"
proof
  note assms [unfolded isodefl_def, simp]
  fix x :: 'a
  show "d\<cdot>(d\<cdot>x) = d\<cdot>x"
    using cast.idem [of t "emb\<cdot>x"] by simp
  show "d\<cdot>x \<sqsubseteq> x"
    using cast.below [of t "emb\<cdot>x"] by simp
qed

lemma isodefl_ID_DEFL: "isodefl (ID :: 'a \<rightarrow> 'a) DEFL('a)"
unfolding isodefl_def by (simp add: cast_DEFL)

lemma isodefl_LIFTDEFL:
  "isodefl (u_map\<cdot>(ID :: 'a \<rightarrow> 'a)) LIFTDEFL('a::predomain)"
unfolding u_map_ID DEFL_u [symmetric]
by (rule isodefl_ID_DEFL)

lemma isodefl_DEFL_imp_ID: "isodefl (d :: 'a \<rightarrow> 'a) DEFL('a) \<Longrightarrow> d = ID"
unfolding isodefl_def
apply (simp add: cast_DEFL)
apply (simp add: cfun_eq_iff)
apply (rule allI)
apply (drule_tac x="emb\<cdot>x" in spec)
apply simp
done

lemma isodefl_bottom: "isodefl \<bottom> \<bottom>"
unfolding isodefl_def by (simp add: cfun_eq_iff)

lemma adm_isodefl:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> adm (\<lambda>x. isodefl (f x) (g x))"
unfolding isodefl_def by simp

lemma isodefl_lub:
  assumes "chain d" and "chain t"
  assumes "\<And>i. isodefl (d i) (t i)"
  shows "isodefl (\<Squnion>i. d i) (\<Squnion>i. t i)"
using prems unfolding isodefl_def
by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma isodefl_fix:
  assumes "\<And>d t. isodefl d t \<Longrightarrow> isodefl (f\<cdot>d) (g\<cdot>t)"
  shows "isodefl (fix\<cdot>f) (fix\<cdot>g)"
unfolding fix_def2
apply (rule isodefl_lub, simp, simp)
apply (induct_tac i)
apply (simp add: isodefl_bottom)
apply (simp add: assms)
done

lemma isodefl_abs_rep:
  fixes abs and rep and d
  assumes DEFL: "DEFL('b) = DEFL('a)"
  assumes abs_def: "(abs :: 'a \<rightarrow> 'b) \<equiv> prj oo emb"
  assumes rep_def: "(rep :: 'b \<rightarrow> 'a) \<equiv> prj oo emb"
  shows "isodefl d t \<Longrightarrow> isodefl (abs oo d oo rep) t"
unfolding isodefl_def
by (simp add: cfun_eq_iff assms prj_emb_prj emb_prj_emb)

lemma isodefl_cfun:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cfun_map\<cdot>d1\<cdot>d2) (cfun_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_cfun_defl cast_isodefl)
apply (simp add: emb_cfun_def prj_cfun_def)
apply (simp add: cfun_map_map cfcomp1)
done

lemma isodefl_ssum:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (ssum_map\<cdot>d1\<cdot>d2) (ssum_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_ssum_defl cast_isodefl)
apply (simp add: emb_ssum_def prj_ssum_def)
apply (simp add: ssum_map_map isodefl_strict)
done

lemma isodefl_sprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (sprod_map\<cdot>d1\<cdot>d2) (sprod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_sprod_defl cast_isodefl)
apply (simp add: emb_sprod_def prj_sprod_def)
apply (simp add: sprod_map_map isodefl_strict)
done

lemma isodefl_cprod:
  "isodefl d1 t1 \<Longrightarrow> isodefl d2 t2 \<Longrightarrow>
    isodefl (cprod_map\<cdot>d1\<cdot>d2) (prod_defl\<cdot>t1\<cdot>t2)"
apply (rule isodeflI)
apply (simp add: cast_prod_defl cast_isodefl)
apply (simp add: emb_prod_def prj_prod_def)
apply (simp add: cprod_map_map cfcomp1)
done

lemma isodefl_u:
  assumes "(liftemb :: 'a u \<rightarrow> udom) = udom_emb u_approx oo u_map\<cdot>emb"
  assumes "(liftprj :: udom \<rightarrow> 'a u) = u_map\<cdot>prj oo udom_prj u_approx"
  shows "isodefl (d :: 'a \<rightarrow> 'a) t \<Longrightarrow> isodefl (u_map\<cdot>d) (u_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_u_defl cast_isodefl)
apply (simp add: emb_u_def prj_u_def assms)
apply (simp add: u_map_map)
done

lemma isodefl_u_u:
  assumes "isodefl (u_map\<cdot>d) (u_defl\<cdot>t)"
  shows "isodefl (u_map\<cdot>(u_map\<cdot>d)) (u_defl\<cdot>(u_defl\<cdot>t))"
using liftemb_u_def liftprj_u_def assms
by (rule isodefl_u)

lemma isodefl_cfun_u:
  assumes "isodefl d1 t1" and "isodefl d2 t2"
  shows "isodefl (u_map\<cdot>(cfun_map\<cdot>d1\<cdot>d2)) (u_defl\<cdot>(cfun_defl\<cdot>t1\<cdot>t2))"
using liftemb_cfun_def liftprj_cfun_def isodefl_cfun [OF assms]
by (rule isodefl_u)

lemma isodefl_cprod_u:
  assumes "isodefl d1 t1" and "isodefl d2 t2"
  shows "isodefl (u_map\<cdot>(cprod_map\<cdot>d1\<cdot>d2)) (u_defl\<cdot>(prod_defl\<cdot>t1\<cdot>t2))"
using liftemb_prod_def liftprj_prod_def isodefl_cprod [OF assms]
by (rule isodefl_u)

lemma isodefl_sprod_u:
  assumes "isodefl d1 t1" and "isodefl d2 t2"
  shows "isodefl (u_map\<cdot>(sprod_map\<cdot>d1\<cdot>d2)) (u_defl\<cdot>(sprod_defl\<cdot>t1\<cdot>t2))"
using liftemb_sprod_def liftprj_sprod_def isodefl_sprod [OF assms]
by (rule isodefl_u)

lemma isodefl_ssum_u:
  assumes "isodefl d1 t1" and "isodefl d2 t2"
  shows "isodefl (u_map\<cdot>(ssum_map\<cdot>d1\<cdot>d2)) (u_defl\<cdot>(ssum_defl\<cdot>t1\<cdot>t2))"
using liftemb_ssum_def liftprj_ssum_def isodefl_ssum [OF assms]
by (rule isodefl_u)

subsection {* Constructing Domain Isomorphisms *}

use "Tools/Domain/domain_isomorphism.ML"

setup Domain_Isomorphism.setup

lemmas [domain_defl_simps] =
  DEFL_cfun DEFL_ssum DEFL_sprod DEFL_prod DEFL_u
  LIFTDEFL_cfun LIFTDEFL_ssum LIFTDEFL_sprod LIFTDEFL_prod LIFTDEFL_u

lemmas [domain_map_ID] =
  cfun_map_ID ssum_map_ID sprod_map_ID cprod_map_ID u_map_ID

lemmas [domain_isodefl] =
  isodefl_cfun isodefl_ssum isodefl_sprod isodefl_cprod isodefl_u_u
  isodefl_cfun_u isodefl_ssum_u isodefl_sprod_u isodefl_cprod_u

lemmas [domain_deflation] =
  deflation_cfun_map deflation_ssum_map deflation_sprod_map
  deflation_cprod_map deflation_u_map

setup {*
  fold Domain_Take_Proofs.add_map_function
    [(@{type_name cfun}, @{const_name cfun_map}, [true, true]),
     (@{type_name ssum}, @{const_name ssum_map}, [true, true]),
     (@{type_name sprod}, @{const_name sprod_map}, [true, true]),
     (@{type_name prod}, @{const_name cprod_map}, [true, true]),
     (@{type_name "u"}, @{const_name u_map}, [true])]
*}

end
