(*  Title:      HOL/MicroJava/Comp/DefsComp.thy
    ID:         $Id$
    Author:     Martin Strecker
*)

(* Definitions for accessing parts of methods, states etc. *)

theory DefsComp = JVMExec:



constdefs
  method_rT :: "cname \<times> ty \<times> 'c \<Rightarrow> ty"
  "method_rT mtd == (fst (snd mtd))"


constdefs
(* g = get *)
  gx :: "xstate \<Rightarrow> val option"  "gx \<equiv> fst"
  gs :: "xstate \<Rightarrow> state"  "gs \<equiv> snd"
  gh :: "xstate \<Rightarrow> aheap"        "gh \<equiv> fst\<circ>snd"
  gl :: "xstate \<Rightarrow> State.locals" "gl \<equiv> snd\<circ>snd"

  gmb :: "'a prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> 'a"
    "gmb G cn si \<equiv> snd(snd(the(method (G,cn) si)))"
  gis :: "jvm_method \<Rightarrow> bytecode"
    "gis \<equiv> fst \<circ> snd \<circ> snd"

(* jmb = aus einem JavaMaethodBody *)
  gjmb_pns  :: "java_mb \<Rightarrow> vname list"     "gjmb_pns \<equiv> fst"
  gjmb_lvs  :: "java_mb \<Rightarrow> (vname\<times>ty)list" "gjmb_lvs \<equiv> fst\<circ>snd"
  gjmb_blk  :: "java_mb \<Rightarrow> stmt"           "gjmb_blk \<equiv> fst\<circ>snd\<circ>snd"
  gjmb_res  :: "java_mb \<Rightarrow> expr"           "gjmb_res \<equiv> snd\<circ>snd\<circ>snd"
  gjmb_plns :: "java_mb \<Rightarrow> vname list"
    "gjmb_plns \<equiv> \<lambda>jmb. gjmb_pns jmb @ map fst (gjmb_lvs jmb)"

  glvs :: "java_mb \<Rightarrow> State.locals \<Rightarrow> locvars"
    "glvs jmb loc \<equiv> map (the\<circ>loc) (gjmb_plns jmb)"
  
lemmas gdefs = gx_def gh_def gl_def gmb_def gis_def glvs_def
lemmas gjmbdefs = gjmb_pns_def gjmb_lvs_def gjmb_blk_def gjmb_res_def gjmb_plns_def

lemmas galldefs = gdefs gjmbdefs



constdefs 
  locvars_locals :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> State.locals \<Rightarrow> locvars"
  "locvars_locals G C S lvs == the (lvs This) # glvs (gmb G C S) lvs"

  locals_locvars :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> locvars \<Rightarrow> State.locals"
  "locals_locvars G C S lvs == 
  empty ((gjmb_plns (gmb G C S))[\<mapsto>](tl lvs)) (This\<mapsto>(hd lvs))"

  locvars_xstate :: "java_mb prog \<Rightarrow> cname \<Rightarrow> sig \<Rightarrow> xstate \<Rightarrow> locvars"
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
