(*  Title:      HOL/NanoJava/OpSem.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Operational Evaluation Semantics"

theory OpSem = State:

consts
 exec :: "(state \<times> stmt       \<times> nat \<times> state) set"
 eval :: "(state \<times> expr \<times> val \<times> nat \<times> state) set"
syntax (xsymbols)
 exec :: "[state,stmt,    nat,state] => bool" ("_ -_-_\<rightarrow> _"  [98,90,   65,98] 89)
 eval :: "[state,expr,val,nat,state] => bool" ("_ -_\<succ>_-_\<rightarrow> _"[98,95,99,65,98] 89)
syntax
 exec :: "[state,stmt,    nat,state] => bool" ("_ -_-_-> _"  [98,90,   65,98]89)
 eval :: "[state,expr,val,nat,state] => bool" ("_ -_>_-_-> _"[98,95,99,65,98]89)
translations
 "s -c  -n-> s'" == "(s, c,    n, s') \<in> exec"
 "s -e>v-n-> s'" == "(s, e, v, n, s') \<in> eval"

inductive exec eval intros
  Skip: "   s -Skip-n-> s"

  Comp: "[| s0 -c1-n-> s1; s1 -c2-n-> s2 |] ==>
            s0 -c1;; c2-n-> s2"

  Cond: "[| s0 -e>v-n-> s1; s1 -(if v\<noteq>Null then c1 else c2)-n-> s2 |] ==>
            s0 -If(e) c1 Else c2-n-> s2"

  LoopF:"   s0<x> = Null ==>
            s0 -While(x) c-n-> s0"
  LoopT:"[| s0<x> \<noteq> Null; s0 -c-n-> s1; s1 -While(x) c-n-> s2 |] ==>
            s0 -While(x) c-n-> s2"

  LAcc: "   s -LAcc x>s<x>-n-> s"

  LAss: "   s -e>v-n-> s' ==>
            s -x:==e-n-> lupd(x\<mapsto>v) s'"

  FAcc: "   s -e>Addr a-n-> s' ==>
            s -e..f>get_field s' a f-n-> s'"

  FAss: "[| s0 -e1>Addr a-n-> s1;  s1 -e2>v-n-> s2 |] ==>
            s0 -e1..f:==e2-n-> upd_obj a f v s2"

  NewC: "   new_Addr s = Addr a ==>
            s -new C>Addr a-n-> new_obj a C s"

  Cast: "[| s -e>v-n-> s';
            case v of Null => True | Addr a => obj_class s' a \<preceq>C C |] ==>
            s -Cast C e>v-n-> s'"

  Call: "[| s0 -e1>a-n-> s1; s1 -e2>p-n-> s2; 
            lupd(This\<mapsto>a)(lupd(Par\<mapsto>p)(reset_locs s2)) -Meth (C,m)-n-> s3
     |] ==> s0 -{C}e1..m(e2)>s3<Res>-n-> set_locs s2 s3"

  Meth: "[| s<This> = Addr a; D = obj_class s a; D\<preceq>C C;
            init_locs D m s -Impl (D,m)-n-> s' |] ==>
            s -Meth (C,m)-n-> s'"

  Impl: "   s -body Cm-    n-> s' ==>
            s -Impl Cm-Suc n-> s'"


inductive_cases exec_elim_cases':
				  "s -Skip            -n\<rightarrow> t"
				  "s -c1;; c2         -n\<rightarrow> t"
				  "s -If(e) c1 Else c2-n\<rightarrow> t"
				  "s -While(x) c      -n\<rightarrow> t"
				  "s -x:==e           -n\<rightarrow> t"
				  "s -e1..f:==e2      -n\<rightarrow> t"
inductive_cases Meth_elim_cases:  "s -Meth Cm         -n\<rightarrow> t"
inductive_cases Impl_elim_cases:  "s -Impl Cm         -n\<rightarrow> t"
lemmas exec_elim_cases = exec_elim_cases' Meth_elim_cases Impl_elim_cases
inductive_cases eval_elim_cases:
				  "s -new C         \<succ>v-n\<rightarrow> t"
				  "s -Cast C e      \<succ>v-n\<rightarrow> t"
				  "s -LAcc x        \<succ>v-n\<rightarrow> t"
				  "s -e..f          \<succ>v-n\<rightarrow> t"
				  "s -{C}e1..m(e2)  \<succ>v-n\<rightarrow> t"

lemma exec_eval_mono [rule_format]: 
  "(s -c  -n\<rightarrow> t \<longrightarrow> (\<forall>m. n \<le> m \<longrightarrow> s -c  -m\<rightarrow> t)) \<and>
   (s -e\<succ>v-n\<rightarrow> t \<longrightarrow> (\<forall>m. n \<le> m \<longrightarrow> s -e\<succ>v-m\<rightarrow> t))"
apply (rule exec_eval.induct)
prefer 14 (* Impl *)
apply clarify
apply (rename_tac n)
apply (case_tac n)
apply (blast intro:exec_eval.intros)+
done
lemmas exec_mono = exec_eval_mono [THEN conjunct1, rule_format]
lemmas eval_mono = exec_eval_mono [THEN conjunct2, rule_format]

lemma exec_exec_max: "\<lbrakk>s1 -c1-    n1   \<rightarrow> t1 ; s2 -c2-       n2\<rightarrow> t2\<rbrakk> \<Longrightarrow> 
                       s1 -c1-max n1 n2\<rightarrow> t1 \<and> s2 -c2-max n1 n2\<rightarrow> t2"
by (fast intro: exec_mono le_maxI1 le_maxI2)

lemma eval_exec_max: "\<lbrakk>s1 -c-    n1   \<rightarrow> t1 ; s2 -e\<succ>v-       n2\<rightarrow> t2\<rbrakk> \<Longrightarrow> 
                       s1 -c-max n1 n2\<rightarrow> t1 \<and> s2 -e\<succ>v-max n1 n2\<rightarrow> t2"
by (fast intro: eval_mono exec_mono le_maxI1 le_maxI2)

lemma eval_eval_max: "\<lbrakk>s1 -e1\<succ>v1-    n1   \<rightarrow> t1 ; s2 -e2\<succ>v2-       n2\<rightarrow> t2\<rbrakk> \<Longrightarrow> 
                       s1 -e1\<succ>v1-max n1 n2\<rightarrow> t1 \<and> s2 -e2\<succ>v2-max n1 n2\<rightarrow> t2"
by (fast intro: eval_mono le_maxI1 le_maxI2)

lemma eval_eval_exec_max: 
 "\<lbrakk>s1 -e1\<succ>v1-n1\<rightarrow> t1; s2 -e2\<succ>v2-n2\<rightarrow> t2; s3 -c-n3\<rightarrow> t3\<rbrakk> \<Longrightarrow> 
   s1 -e1\<succ>v1-max (max n1 n2) n3\<rightarrow> t1 \<and> 
   s2 -e2\<succ>v2-max (max n1 n2) n3\<rightarrow> t2 \<and> 
   s3 -c    -max (max n1 n2) n3\<rightarrow> t3"
apply (drule (1) eval_eval_max, erule thin_rl)
by (fast intro: exec_mono eval_mono le_maxI1 le_maxI2)

lemma Impl_body_eq: "(\<lambda>t. \<exists>n. Z -Impl M-n\<rightarrow> t) = (\<lambda>t. \<exists>n. Z -body M-n\<rightarrow> t)"
apply (rule ext)
apply (fast elim: exec_elim_cases intro: exec_eval.Impl)
done

end