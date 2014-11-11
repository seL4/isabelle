(*  Title:      CCL/ex/Nat.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section {* Programs defined over the natural numbers *}

theory Nat
imports "../Wfd"
begin

definition not :: "i=>i"
  where "not(b) == if b then false else true"

definition add :: "[i,i]=>i"  (infixr "#+" 60)
  where "a #+ b == nrec(a,b,%x g. succ(g))"

definition mult :: "[i,i]=>i"  (infixr "#*" 60)
  where "a #* b == nrec(a,zero,%x g. b #+ g)"

definition sub :: "[i,i]=>i"  (infixr "#-" 60)
  where
    "a #- b ==
      letrec sub x y be ncase(y,x,%yy. ncase(x,zero,%xx. sub(xx,yy)))
      in sub(a,b)"

definition le :: "[i,i]=>i"  (infixr "#<=" 60)
  where
    "a #<= b ==
      letrec le x y be ncase(x,true,%xx. ncase(y,false,%yy. le(xx,yy)))
      in le(a,b)"

definition lt :: "[i,i]=>i"  (infixr "#<" 60)
  where "a #< b == not(b #<= a)"

definition div :: "[i,i]=>i"  (infixr "##" 60)
  where
    "a ## b ==
      letrec div x y be if x #< y then zero else succ(div(x#-y,y))
      in div(a,b)"

definition ackermann :: "[i,i]=>i"
  where
    "ackermann(a,b) ==
      letrec ack n m be ncase(n,succ(m),%x.
        ncase(m,ack(x,succ(zero)),%y. ack(x,ack(succ(x),y))))
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


lemma napply_f: "n:Nat ==> f^n`f(a) = f^succ(n)`a"
  apply (erule Nat_ind)
   apply simp_all
  done

lemma addT: "[| a:Nat;  b:Nat |] ==> a #+ b : Nat"
  apply (unfold add_def)
  apply typechk
  done

lemma multT: "[| a:Nat;  b:Nat |] ==> a #* b : Nat"
  apply (unfold add_def mult_def)
  apply typechk
  done

(* Defined to return zero if a<b *)
lemma subT: "[| a:Nat;  b:Nat |] ==> a #- b : Nat"
  apply (unfold sub_def)
  apply typechk
  apply clean_ccs
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma leT: "[| a:Nat;  b:Nat |] ==> a #<= b : Bool"
  apply (unfold le_def)
  apply typechk
  apply clean_ccs
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma ltT: "[| a:Nat;  b:Nat |] ==> a #< b : Bool"
  apply (unfold not_def lt_def)
  apply (typechk leT)
  done


subsection {* Termination Conditions for Ackermann's Function *}

lemmas relI = NatPR_wf [THEN NatPR_wf [THEN lex_wf, THEN wfI]]

lemma "[| a:Nat;  b:Nat |] ==> ackermann(a,b) : Nat"
  apply (unfold ackermann_def)
  apply gen_ccs
  apply (erule NatPRI [THEN lexI1 [THEN relI]] NatPRI [THEN lexI2 [THEN relI]])+
  done

end
