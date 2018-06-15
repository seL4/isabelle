(*  Title:      HOL/MicroJava/Comp/DefsComp.thy
    Author:     Martin Strecker
*)

(* Definitions for accessing parts of methods, states etc. *)

theory DefsComp
imports "../JVM/JVMExec"
begin


definition method_rT :: "cname \<times> ty \<times> 'c \<Rightarrow> ty" where
  "method_rT mtd == (fst (snd mtd))"


(* g = get *)
definition
  gx :: "xstate \<Rightarrow> val option" where "gx \<equiv> fst"

definition
  gs :: "xstate \<Rightarrow> state" where "gs \<equiv> snd"

definition
  gh :: "xstate \<Rightarrow> aheap" where "gh \<equiv> fst\<circ>snd"

definition
  gl :: "xstate \<Rightarrow> State.locals" where "gl \<equiv> snd\<circ>snd"

definition
  gmb :: "'a prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> 'a"
    where "gmb G cn si \<equiv> snd(snd(the(method (G,cn) si)))"

definition
  gis :: "jvm_method \<Rightarrow> bytecode"
    where "gis \<equiv> fst \<circ> snd \<circ> snd"

(* jmb = aus einem JavaMaethodBody *)
definition
  gjmb_pns  :: "java_mb \<Rightarrow> vname list" where "gjmb_pns \<equiv> fst"

definition
  gjmb_lvs  :: "java_mb \<Rightarrow> (vname\<times>ty)list" where  "gjmb_lvs \<equiv> fst\<circ>snd"

definition
  gjmb_blk  :: "java_mb \<Rightarrow> stmt" where  "gjmb_blk \<equiv> fst\<circ>snd\<circ>snd"

definition
  gjmb_res  :: "java_mb \<Rightarrow> expr" where  "gjmb_res \<equiv> snd\<circ>snd\<circ>snd"

definition
  gjmb_plns :: "java_mb \<Rightarrow> vname list"
    where  "gjmb_plns \<equiv> \<lambda>jmb. gjmb_pns jmb @ map fst (gjmb_lvs jmb)"

definition
  glvs :: "java_mb \<Rightarrow> State.locals \<Rightarrow> locvars"
    where "glvs jmb loc \<equiv> map (the\<circ>loc) (gjmb_plns jmb)"
  
lemmas gdefs = gx_def gh_def gl_def gmb_def gis_def glvs_def
lemmas gjmbdefs = gjmb_pns_def gjmb_lvs_def gjmb_blk_def gjmb_res_def gjmb_plns_def

lemmas galldefs = gdefs gjmbdefs

definition locvars_locals :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> State.locals \<Rightarrow> locvars" where
  "locvars_locals G C S lvs == the (lvs This) # glvs (gmb G C S) lvs"

definition locals_locvars :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> locvars \<Rightarrow> State.locals" where
  "locals_locvars G C S lvs == 
  Map.empty ((gjmb_plns (gmb G C S))[\<mapsto>](tl lvs)) (This\<mapsto>(hd lvs))"

definition locvars_xstate :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> xstate \<Rightarrow> locvars" where
  "locvars_xstate G C S xs == locvars_locals G C S (gl xs)"


lemma locvars_xstate_par_dep: 
  "lv1 = lv2 \<Longrightarrow> 
  locvars_xstate G C S (xcpt1, hp1, lv1) = locvars_xstate G C S (xcpt2, hp2, lv2)"
by (simp add: locvars_xstate_def gl_def)




(**********************************************************************)
(* Conversions *)


lemma gx_conv [simp]: "gx (xcpt, s) = xcpt" by (simp add: gx_def)

lemma gh_conv [simp]: "gh (xcpt, h, l) = h" by (simp add: gh_def)


end
