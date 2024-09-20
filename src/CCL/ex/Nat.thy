(*  Title:      CCL/ex/Nat.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Programs defined over the natural numbers\<close>

theory Nat
imports "../Wfd"
begin

definition not :: "i\<Rightarrow>i"
  where "not(b) == if b then false else true"

definition add :: "[i,i]\<Rightarrow>i"  (infixr \<open>#+\<close> 60)
  where "a #+ b == nrec(a, b, \<lambda>x g. succ(g))"

definition mult :: "[i,i]\<Rightarrow>i"  (infixr \<open>#*\<close> 60)
  where "a #* b == nrec(a, zero, \<lambda>x g. b #+ g)"

definition sub :: "[i,i]\<Rightarrow>i"  (infixr \<open>#-\<close> 60)
  where
    "a #- b ==
      letrec sub x y be ncase(y, x, \<lambda>yy. ncase(x, zero, \<lambda>xx. sub(xx,yy)))
      in sub(a,b)"

definition le :: "[i,i]\<Rightarrow>i"  (infixr \<open>#<=\<close> 60)
  where
    "a #<= b ==
      letrec le x y be ncase(x, true, \<lambda>xx. ncase(y, false, \<lambda>yy. le(xx,yy)))
      in le(a,b)"

definition lt :: "[i,i]\<Rightarrow>i"  (infixr \<open>#<\<close> 60)
  where "a #< b == not(b #<= a)"

definition div :: "[i,i]\<Rightarrow>i"  (infixr \<open>##\<close> 60)
  where
    "a ## b ==
      letrec div x y be if x #< y then zero else succ(div(x#-y,y))
      in div(a,b)"

definition ackermann :: "[i,i]\<Rightarrow>i"
  where
    "ackermann(a,b) ==
      letrec ack n m be ncase(n, succ(m), \<lambda>x.
        ncase(m,ack(x,succ(zero)), \<lambda>y. ack(x,ack(succ(x),y))))
      in ack(a,b)"

lemmas nat_defs = not_def add_def mult_def sub_def le_def lt_def ackermann_def napply_def

lemma natBs [simp]:
  "not(true) = false"
  "not(false) = true"
  "zero #+ n = n"
  "succ(n) #+ m = succ(n #+ m)"
  "zero #* n = zero"
  "succ(n) #* m = m #+ (n #* m)"
  "f^zero`a = a"
  "f^succ(n)`a = f(f^n`a)"
  by (simp_all add: nat_defs)


lemma napply_f: "n:Nat \<Longrightarrow> f^n`f(a) = f^succ(n)`a"
  apply (erule Nat_ind)
   apply simp_all
  done

lemma addT: "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> a #+ b : Nat"
  apply (unfold add_def)
  apply typechk
  done

lemma multT: "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> a #* b : Nat"
  apply (unfold add_def mult_def)
  apply typechk
  done

(* Defined to return zero if a<b *)
lemma subT: "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> a #- b : Nat"
  apply (unfold sub_def)
  apply typechk
  apply clean_ccs
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma leT: "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> a #<= b : Bool"
  apply (unfold le_def)
  apply typechk
  apply clean_ccs
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma ltT: "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> a #< b : Bool"
  apply (unfold not_def lt_def)
  apply (typechk leT)
  done


subsection \<open>Termination Conditions for Ackermann's Function\<close>

lemmas relI = NatPR_wf [THEN NatPR_wf [THEN lex_wf, THEN wfI]]

lemma "\<lbrakk>a:Nat; b:Nat\<rbrakk> \<Longrightarrow> ackermann(a,b) : Nat"
  apply (unfold ackermann_def)
  apply gen_ccs
  apply (erule NatPRI [THEN lexI1 [THEN relI]] NatPRI [THEN lexI2 [THEN relI]])+
  done

end
