(*  Title:      HOLCF/Powerdomains.thy
    Author:     Brian Huffman
*)

header {* Powerdomains *}

theory Powerdomains
imports ConvexPD Domain
begin

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
  fold Domain_Isomorphism.add_type_constructor
    [(@{type_name "upper_pd"}, @{term upper_defl}, @{const_name upper_map}),
     (@{type_name "lower_pd"}, @{term lower_defl}, @{const_name lower_map}),
     (@{type_name "convex_pd"}, @{term convex_defl}, @{const_name convex_map})]
*}

end
