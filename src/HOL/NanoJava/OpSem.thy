(*  Title:      HOL/NanoJava/OpSem.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Operational Evaluation Semantics"

theory OpSem = State:

consts
  exec :: "(state \<times> stmt \<times> nat \<times> state) set"
syntax (xsymbols)
  exec :: "[state,  stmt,  nat,  state] => bool" ("_ -_-_\<rightarrow> _" [98,90,99,98] 89)
syntax
  exec :: "[state,  stmt,  nat,  state] => bool" ("_ -_-_-> _" [98,90,99,98] 89)
translations
  "s -c-n-> s'" == "(s, c, n, s') \<in> exec"

inductive exec intros

  Skip: "   s -Skip-n-> s"

  Comp: "[| s0 -c1-n-> s1; s1 -c2-n-> s2 |] ==>
            s0 -c1;; c2-n-> s2"

  Cond: "[| s -(if s<e> \<noteq> Null then c1 else c2)-n-> s' |] ==>
            s -If(e) c1 Else c2-n-> s'"

  LoopF:"   s0<e> = Null ==>
            s0 -While(e) c-n-> s0"
  LoopT:"[| s0<e> \<noteq> Null; s0 -c-n-> s1; s1 -While(e) c-n-> s2 |] ==>
            s0 -While(e) c-n-> s2"

  NewC: "   new_Addr s = Addr a ==>
            s -x:=new C-n-> lupd(x\<mapsto>Addr a)(new_obj a C s)"

  Cast: "  (case s<y> of Null => True | Addr a => obj_class s a \<preceq>C C) ==>
            s -x:=(C)y-n-> lupd(x\<mapsto>s<y>) s"

  FAcc: "   s<y> = Addr a ==>
            s -x:=y..f-n-> lupd(x\<mapsto>get_field s a f) s"

  FAss: "   s<y> = Addr a ==>
            s -y..f:=x-n-> upd_obj a f (s<x>) s"

  Call: "lupd(This\<mapsto>s<y>)(lupd(Param\<mapsto>s<p>)(init_locs C m s))-Meth C m -n-> s'==>
            s -x:={C}y..m(p)-n-> lupd(x\<mapsto>s'<Res>)(set_locs s s')"

  Meth: "[| s<This> = Addr a; obj_class s a\<preceq>C C;
            s -Impl (obj_class s a) m-n-> s' |] ==>
            s -Meth C m-n-> s'"

  Impl: "   s -body C m-    n-> s' ==>
            s -Impl C m-Suc n-> s'"

inductive_cases exec_elim_cases':
	"s -Skip            -n-> t"
	"s -c1;; c2         -n-> t"
	"s -If(e) c1 Else c2-n-> t"
	"s -While(e) c      -n-> t"
	"s -x:=new C        -n-> t"
	"s -x:=(C)y         -n-> t"
	"s -x:=y..f         -n-> t"
	"s -y..f:=x         -n-> t"
	"s -x:={C}y..m(p)   -n-> t"
inductive_cases Meth_elim_cases: "s -Meth C m -n-> t"
inductive_cases Impl_elim_cases: "s -Impl C m -n-> t"
lemmas exec_elim_cases = exec_elim_cases' Meth_elim_cases Impl_elim_cases

lemma exec_mono [rule_format]: "s -c-n\<rightarrow> t \<Longrightarrow> \<forall>m. n \<le> m \<longrightarrow> s -c-m\<rightarrow> t"
apply (erule exec.induct)
prefer 12 (* Impl *)
apply clarify
apply (rename_tac n)
apply (case_tac n)
apply (blast intro:exec.intros)+
done

lemma exec_max2: "\<lbrakk>s1 -c1-    n1   \<rightarrow> t1 ; s2 -c2-        n2\<rightarrow> t2\<rbrakk> \<Longrightarrow> 
                   s1 -c1-max n1 n2\<rightarrow> t1 \<and> s2 -c2-max n1 n2\<rightarrow> t2"
by (fast intro: exec_mono le_maxI1 le_maxI2)

lemma Impl_body_eq: "(\<lambda>t. \<exists>n. z -Impl C m-n\<rightarrow> t) = (\<lambda>t. \<exists>n. z -body C m-n\<rightarrow> t)"
apply (rule ext)
apply (fast elim: exec_elim_cases intro: exec.Impl)
done

end