(*  Title:      isabelle/Bali/Example.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen

The following example Bali program includes:
 class declarations with inheritance, hiding of fields, and overriding of
  methods (with refined result type), 
 instance creation, local assignment, sequential composition,
 method call with dynamic binding, literal values,
 expression statement, local access, type cast, field assignment (in part), skip

class Base {
  boolean vee;
  Base foo(Base x) {return x;}
}

class Ext extends Base {
  int vee;
  Ext foo(Base x) {((Ext)x).vee=1; return null;}
}

class Example {
  public static void main (String args[]) {
    Base e=new Ext();
    e.foo(null);
  }
}
*)

theory Example = Eval:

datatype cnam_ = Base_ | Ext_
datatype vnam_ = vee_ | x_ | e_

consts

  cnam_ :: "cnam_ => cname"
  vnam_ :: "vnam_ => vnam"

axioms (* cnam_ and vnam_ are intended to be isomorphic to cnam and vnam *)

  inj_cnam_:  "(cnam_ x = cnam_ y) = (x = y)"
  inj_vnam_:  "(vnam_ x = vnam_ y) = (x = y)"

  surj_cnam_: "\<exists>m. n = cnam_ m"
  surj_vnam_: "\<exists>m. n = vnam_ m"

declare inj_cnam_ [simp] inj_vnam_ [simp]

syntax

  Base :: cname
  Ext  :: cname
  vee  :: vname
  x    :: vname
  e    :: vname

translations

  "Base" == "cnam_ Base_"
  "Ext"	 == "cnam_ Ext_"
  "vee"  == "VName (vnam_ vee_)"
  "x"	 == "VName (vnam_ x_)"
  "e"	 == "VName (vnam_ e_)"

axioms

  Base_not_Object: "Base \<noteq> Object"
  Ext_not_Object:  "Ext  \<noteq> Object"

declare Base_not_Object [simp] Ext_not_Object [simp]
declare Base_not_Object [THEN not_sym, simp] 
declare Ext_not_Object  [THEN not_sym, simp]

consts

  foo_Base::  java_mb
  foo_Ext ::  java_mb
  BaseC   :: "java_mb cdecl"
  ExtC    :: "java_mb cdecl"
  test	  ::  stmt
  foo	  ::  mname
  a	  ::  loc
  b       ::  loc

defs

  foo_Base_def:"foo_Base == ([x],[],Skip,LAcc x)"
  BaseC_def:"BaseC == (Base, (Object, 
			     [(vee, PrimT Boolean)], 
			     [((foo,[Class Base]),Class Base,foo_Base)]))"
  foo_Ext_def:"foo_Ext == ([x],[],Expr( {Ext}Cast Ext
				       (LAcc x)..vee:=Lit (Intg #1)),
				   Lit Null)"
  ExtC_def: "ExtC  == (Ext,  (Base  , 
			     [(vee, PrimT Integer)], 
			     [((foo,[Class Base]),Class Ext,foo_Ext)]))"

  test_def:"test == Expr(e::=NewC Ext);; 
                    Expr({Base}LAcc e..foo({[Class Base]}[Lit Null]))"


syntax

  NP	:: xcpt
  tprg 	::"java_mb prog"
  obj1	:: obj
  obj2	:: obj
  s0 	:: state
  s1 	:: state
  s2 	:: state
  s3 	:: state
  s4 	:: state

translations

  "NP"   == "NullPointer"
  "tprg" == "[ObjectC, BaseC, ExtC]"
  "obj1"    <= "(Ext, empty((vee, Base)\<mapsto>Bool False)
			   ((vee, Ext )\<mapsto>Intg #0))"
  "s0" == " Norm    (empty, empty)"
  "s1" == " Norm    (empty(a\<mapsto>obj1),empty(e\<mapsto>Addr a))"
  "s2" == " Norm    (empty(a\<mapsto>obj1),empty(x\<mapsto>Null)(This\<mapsto>Addr a))"
  "s3" == "(Some NP, empty(a\<mapsto>obj1),empty(e\<mapsto>Addr a))"


ML {* bind_thm ("map_of_Cons", hd (tl (thms "map_of.simps"))) *}
lemma map_of_Cons1 [simp]: "map_of ((aa,bb)#ps) aa = Some bb"
apply (simp (no_asm))
done
lemma map_of_Cons2 [simp]: "aa\<noteq>k ==> map_of ((k,bb)#ps) aa = map_of ps aa"
apply (simp (no_asm_simp))
done
declare map_of_Cons [simp del]; (* sic! *)

lemma class_tprg_Object [simp]: "class tprg Object = Some (arbitrary, [], [])"
apply (unfold ObjectC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_Base [simp]: 
"class tprg Base = Some (Object,  
	  [(vee, PrimT Boolean)],  
          [((foo, [Class Base]), Class Base, foo_Base)])"
apply (unfold ObjectC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_Ext [simp]: 
"class tprg Ext = Some (Base,  
	  [(vee, PrimT Integer)],  
          [((foo, [Class Base]), Class Ext, foo_Ext)])"
apply (unfold ObjectC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma not_Object_subcls [elim!]: "(Object,C) \<in> (subcls1 tprg)^+ ==> R"
apply (auto dest!: tranclD subcls1D)
done

lemma subcls_ObjectD [dest!]: "tprg\<turnstile>Object\<preceq>C C ==> C = Object"
apply (erule rtrancl_induct)
apply  auto
apply (drule subcls1D)
apply auto
done

lemma not_Base_subcls_Ext [elim!]: "(Base, Ext) \<in> (subcls1 tprg)^+ ==> R"
apply (auto dest!: tranclD subcls1D)
done

lemma class_tprgD: 
"class tprg C = Some z ==> C=Object \<or> C=Base \<or> C=Ext"
apply (unfold ObjectC_def BaseC_def ExtC_def class_def)
apply (auto split add: split_if_asm simp add: map_of_Cons)
done

lemma not_class_subcls_class [elim!]: "(C,C) \<in> (subcls1 tprg)^+ ==> R"
apply (auto dest!: tranclD subcls1D)
apply (frule class_tprgD)
apply (auto dest!:)
apply (drule rtranclD)
apply auto
done

lemma unique_classes: "unique tprg"
apply (simp (no_asm) add: ObjectC_def BaseC_def ExtC_def)
done

lemmas subcls_direct = subcls1I [THEN r_into_rtrancl]

lemma Ext_subcls_Base [simp]: "tprg\<turnstile>Ext\<preceq>C Base"
apply (rule subcls_direct)
apply auto
done

lemma Ext_widen_Base [simp]: "tprg\<turnstile>Class Ext\<preceq> Class Base"
apply (rule widen.subcls)
apply (simp (no_asm))
done

declare ty_expr_ty_exprs_wt_stmt.intros [intro!]

lemma acyclic_subcls1_: "acyclic (subcls1 tprg)"
apply (rule acyclicI)
apply safe
done

lemmas wf_subcls1_ = acyclic_subcls1_ [THEN finite_subcls1 [THEN finite_acyclic_wf_converse]]

lemmas fields_rec_ = wf_subcls1_ [THEN [2] fields_rec_lemma]

lemma fields_Object [simp]: "fields (tprg, Object) = []"
apply (subst fields_rec_)
apply   auto
done

declare is_class_def [simp]

lemma fields_Base [simp]: "fields (tprg,Base) = [((vee, Base), PrimT Boolean)]"
apply (subst fields_rec_)
apply   auto
done

lemma fields_Ext [simp]: 
  "fields (tprg, Ext)  = [((vee, Ext ), PrimT Integer)] @ fields (tprg, Base)"
apply (rule trans)
apply  (rule fields_rec_)
apply   auto
done

lemmas method_rec_ = wf_subcls1_ [THEN [2] method_rec_lemma]

lemma method_Object [simp]: "method (tprg,Object) = map_of []"
apply (subst method_rec_)
apply  auto
done

lemma method_Base [simp]: "method (tprg, Base) = map_of  
  [((foo, [Class Base]), Base, (Class Base, foo_Base))]"
apply (rule trans)
apply  (rule method_rec_)
apply  auto
done

lemma method_Ext [simp]: "method (tprg, Ext) = (method (tprg, Base) ++ map_of  
  [((foo, [Class Base]), Ext , (Class Ext, foo_Ext))])"
apply (rule trans)
apply  (rule method_rec_)
apply  auto
done

lemma wf_foo_Base: 
"wf_mdecl wf_java_mdecl tprg Base ((foo, [Class Base]), (Class Base, foo_Base))"
apply (unfold wf_mdecl_def wf_mhead_def wf_java_mdecl_def foo_Base_def)
apply auto
done

lemma wf_foo_Ext: 
"wf_mdecl wf_java_mdecl tprg Ext ((foo, [Class Base]), (Class Ext, foo_Ext))"
apply (unfold wf_mdecl_def wf_mhead_def wf_java_mdecl_def foo_Ext_def)
apply auto
apply  (rule ty_expr_ty_exprs_wt_stmt.Cast)
prefer 2
apply   (simp)
apply   (rule_tac [2] cast.subcls)
apply   (unfold field_def)
apply   auto
done

lemma wf_ObjectC: 
"wf_cdecl wf_java_mdecl tprg ObjectC"
apply (unfold wf_cdecl_def wf_fdecl_def ObjectC_def)
apply (simp (no_asm))
done

lemma wf_BaseC: 
"wf_cdecl wf_java_mdecl tprg BaseC"
apply (unfold wf_cdecl_def wf_fdecl_def BaseC_def)
apply (simp (no_asm))
apply (fold BaseC_def)
apply (rule wf_foo_Base [THEN conjI])
apply auto
done

lemma wf_ExtC: 
"wf_cdecl wf_java_mdecl tprg ExtC"
apply (unfold wf_cdecl_def wf_fdecl_def ExtC_def)
apply (simp (no_asm))
apply (fold ExtC_def)
apply (rule wf_foo_Ext [THEN conjI])
apply auto
apply (drule rtranclD)
apply auto
done

lemma wf_tprg: 
"wf_prog wf_java_mdecl tprg"
apply (unfold wf_prog_def Let_def)
apply(simp add: wf_ObjectC wf_BaseC wf_ExtC unique_classes)
done

lemma appl_methds_foo_Base: 
"appl_methds tprg Base (foo, [NT]) =  
  {((Class Base, Class Base), [Class Base])}"
apply (unfold appl_methds_def)
apply (simp (no_asm))
apply (subgoal_tac "tprg\<turnstile>NT\<preceq> Class Base")
apply  (auto simp add: map_of_Cons foo_Base_def)
done

lemma max_spec_foo_Base: "max_spec tprg Base (foo, [NT]) =  
  {((Class Base, Class Base), [Class Base])}"
apply (unfold max_spec_def)
apply (auto simp add: appl_methds_foo_Base)
done

ML {* fun t thm = resolve_tac (thms "ty_expr_ty_exprs_wt_stmt.intros") 1 thm *}
lemma wt_test: "(tprg, empty(e\<mapsto>Class Base))\<turnstile>  
  Expr(e::=NewC Ext);; Expr({Base}LAcc e..foo({?pTs'}[Lit Null]))\<surd>"
apply (tactic t) (* ;; *)
apply  (tactic t) (* Expr *)
apply  (tactic t) (* LAss *)
apply    (tactic t) (* LAcc *)
apply     (simp (no_asm))
apply    (simp (no_asm))
apply   (tactic t) (* NewC *)
apply   (simp (no_asm))
apply  (simp (no_asm))
apply (tactic t) (* Expr *)
apply (tactic t) (* Call *)
apply   (tactic t) (* LAcc *)
apply    (simp (no_asm))
apply   (simp (no_asm))
apply  (tactic t) (* Cons *)
apply   (tactic t) (* Lit *)
apply   (simp (no_asm))
apply  (tactic t) (* Nil *)
apply (simp (no_asm))
apply (rule max_spec_foo_Base)
done

ML {* fun e t = resolve_tac (thm "NewCI"::thms "eval_evals_exec.intros") 1 t *}

declare split_if [split del]
declare init_vars_def [simp] c_hupd_def [simp] cast_ok_def [simp]
lemma exec_test: 
" [|new_Addr (heap (snd s0)) = (a, None)|] ==>  
  tprg\<turnstile>s0 -test-> ?s"
apply (unfold test_def)
(* ?s = s3 *)
apply (tactic e) (* ;; *)
apply  (tactic e) (* Expr *)
apply  (tactic e) (* LAss *)
apply   (tactic e) (* NewC *)
apply    force
apply   force
apply  (simp (no_asm))
apply (erule thin_rl)
apply (tactic e) (* Expr *)
apply (tactic e) (* Call *)
apply       (tactic e) (* LAcc *)
apply      force
apply     (tactic e) (* Cons *)
apply      (tactic e) (* Lit *)
apply     (tactic e) (* Nil *)
apply    (simp (no_asm))
apply   (force simp add: foo_Ext_def)
apply  (simp (no_asm))
apply  (tactic e) (* Expr *)
apply  (tactic e) (* FAss *)
apply       (tactic e) (* Cast *)
apply        (tactic e) (* LAcc *)
apply       (simp (no_asm))
apply      (simp (no_asm))
apply     (simp (no_asm))
apply     (tactic e) (* XcptE *)
apply    (simp (no_asm))
apply   (rule surjective_pairing [THEN sym, THEN[2]trans], subst Pair_eq, force)
apply  (simp (no_asm))
apply (simp (no_asm))
apply (tactic e) (* XcptE *)
done

end
