(*  Title:      HOL/MicroJava/Comp/Index.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2002
*)

(* Index of variable in list of parameter names and local variables *)

theory Index =  AuxLemmas + DefsComp:

(*indexing a variable name among all variable declarations in a method body*)
constdefs
 index :: "java_mb => vname => nat"
 "index ==  \<lambda> (pn,lv,blk,res) v.
  if v = This
  then 0 
  else Suc (length (takeWhile (\<lambda> z. z~=v) (pn @ map fst lv)))"


lemma index_length_pns: "
  \<lbrakk> i = index (pns,lvars,blk,res) vn;
  wf_java_mdecl G C ((mn,pTs),rT, (pns,lvars,blk,res)); 
  vn \<in> set pns\<rbrakk> 
  \<Longrightarrow> 0 < i \<and> i < Suc (length pns)"
apply (simp add: wf_java_mdecl_def index_def)
apply (subgoal_tac "vn \<noteq> This")
apply (auto intro: length_takeWhile)
done

lemma index_length_lvars: "
  \<lbrakk> i = index (pns,lvars,blk,res) vn;
  wf_java_mdecl G C ((mn,pTs),rT, (pns,lvars,blk,res)); 
  vn \<in> set (map fst lvars)\<rbrakk> 
  \<Longrightarrow> (length pns) < i \<and> i < Suc((length pns) + (length lvars))"
apply (simp add: wf_java_mdecl_def index_def)
apply (subgoal_tac "vn \<noteq> This")
apply simp
apply (subgoal_tac "\<forall> x \<in> set pns. (\<lambda>z. z \<noteq> vn) x")
apply (simp add: takeWhile_append2)
apply (subgoal_tac "length (takeWhile (\<lambda>z. z \<noteq> vn) (map fst lvars)) < length (map fst lvars)")
apply simp
apply (rule length_takeWhile)
apply simp
apply (simp add: map_of_in_set)
apply (intro strip notI) apply simp apply blast
done


(***  index  ***)

lemma select_at_index : 
  "x \<in> set (gjmb_plns (gmb G C S)) \<or> x = This 
  \<Longrightarrow> (the (loc This) # glvs (gmb G C S) loc) ! (index (gmb G C S) x) = 
     the (loc x)"
apply (simp only: index_def gjmb_plns_def)
apply (case_tac "(gmb G C S)")
apply (simp add: galldefs del: set_append map_append)
apply (case_tac b, simp add: gmb_def gjmb_lvs_def del: set_append map_append)
apply (intro strip)
apply (simp del: set_append map_append)
apply (frule length_takeWhile)
apply (frule_tac f = "(the \<circ> loc)" in nth_map)
apply simp
done

lemma lift_if: "(f (if b then t else e)) = (if b then (f t) else (f e))"
apply auto
done

lemma update_at_index: "
  \<lbrakk> distinct (gjmb_plns (gmb G C S)); 
  x \<in> set (gjmb_plns (gmb G C S)); x \<noteq> This \<rbrakk> \<Longrightarrow> 
  locvars_xstate G C S (Norm (h, l))[index (gmb G C S) x := val] =
          locvars_xstate G C S (Norm (h, l(x\<mapsto>val)))"
apply (simp only: locvars_xstate_def locvars_locals_def index_def)
apply (case_tac "(gmb G C S)", simp)
apply (case_tac b, simp)
apply (rule conjI)
apply (simp add: gl_def)
apply (intro strip, simp)
apply (simp add: galldefs del: set_append map_append)
done


(* !!!! incomprehensible: why can't List.takeWhile_append2 be applied the same 
  way in the second case as in the first case ? *)
lemma index_of_var: "\<lbrakk> xvar \<notin> set pns; xvar \<notin> set (map fst zs); xvar \<noteq> This \<rbrakk>
  \<Longrightarrow> index (pns, zs @ ((xvar, xval) # xys), blk, res) xvar = Suc (length pns + length zs)"
apply (simp add: index_def)
apply (subgoal_tac "(\<And>x. ((x \<in> (set pns)) \<Longrightarrow> ((\<lambda>z. (z \<noteq> xvar))x)))")
apply (simp add: List.takeWhile_append2)
apply (subgoal_tac "(takeWhile (\<lambda>z. z \<noteq> xvar) (map fst zs @ xvar # map fst xys)) = map fst zs @ (takeWhile (\<lambda>z. z \<noteq> xvar) (xvar # map fst xys))")
apply simp
apply (rule List.takeWhile_append2)
apply auto
done




(* The following def should replace the conditions in WellType.thy / wf_java_mdecl
*)
constdefs 
  disjoint_varnames :: "[vname list, (vname \<times> ty) list] \<Rightarrow> bool"
(* This corresponds to the original def in wf_java_mdecl:
  "disjoint_varnames pns lvars \<equiv> 
  nodups pns \<and> unique lvars \<and> This \<notin> set pns \<and> This \<notin> set (map fst lvars) \<and> 
	(\<forall>pn\<in>set pns. map_of lvars pn = None)"
*)

  "disjoint_varnames pns lvars \<equiv> 
  distinct pns \<and> unique lvars \<and> This \<notin> set pns \<and> This \<notin> set (map fst lvars) \<and> 
  (\<forall>pn\<in>set pns. pn \<notin> set (map fst lvars))"


lemma index_of_var2: "
  disjoint_varnames pns (lvars_pre @ (vn, ty) # lvars_post)
  \<Longrightarrow> index (pns, lvars_pre @ (vn, ty) # lvars_post, blk, res) vn =
  Suc (length pns + length lvars_pre)"
apply (simp add: disjoint_varnames_def index_def unique_def distinct_append)
apply (subgoal_tac "vn \<noteq> This", simp)
apply (subgoal_tac
  "takeWhile (\<lambda>z. z \<noteq> vn) (map fst lvars_pre @ vn # map fst lvars_post) =
  map fst lvars_pre @ takeWhile (\<lambda>z. z \<noteq> vn) (vn # map fst lvars_post)")
apply simp 
apply (rule List.takeWhile_append2)
apply auto
done

lemma wf_java_mdecl_disjoint_varnames: 
  "wf_java_mdecl G C (S,rT,(pns,lvars,blk,res)) 
  \<Longrightarrow> disjoint_varnames pns lvars"
apply (case_tac S)
apply (simp add: wf_java_mdecl_def disjoint_varnames_def  map_of_in_set)
done

lemma wf_java_mdecl_length_pTs_pns: 
  "wf_java_mdecl G C ((mn, pTs), rT, pns, lvars, blk, res)
  \<Longrightarrow> length pTs = length pns"
by (simp add: wf_java_mdecl_def)

end
