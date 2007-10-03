(*  Title:      CCL/ex/Nat.thy
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Programs defined over the natural numbers *}

theory Nat
imports Wfd
begin

consts

  not   :: "i=>i"
  add   :: "[i,i]=>i"            (infixr "#+" 60)
  mult  :: "[i,i]=>i"            (infixr "#*" 60)
  sub   :: "[i,i]=>i"            (infixr "#-" 60)
  div   :: "[i,i]=>i"            (infixr "##" 60)
  lt    :: "[i,i]=>i"            (infixr "#<" 60)
  le    :: "[i,i]=>i"            (infixr "#<=" 60)
  ackermann :: "[i,i]=>i"

defs

  not_def:     "not(b) == if b then false else true"

  add_def:     "a #+ b == nrec(a,b,%x g. succ(g))"
  mult_def:    "a #* b == nrec(a,zero,%x g. b #+ g)"
  sub_def:     "a #- b == letrec sub x y be ncase(y,x,%yy. ncase(x,zero,%xx. sub(xx,yy)))
                        in sub(a,b)"
  le_def:     "a #<= b == letrec le x y be ncase(x,true,%xx. ncase(y,false,%yy. le(xx,yy)))
                        in le(a,b)"
  lt_def:     "a #< b == not(b #<= a)"

  div_def:    "a ## b == letrec div x y be if x #< y then zero else succ(div(x#-y,y))
                       in div(a,b)"
  ack_def:
  "ackermann(a,b) == letrec ack n m be ncase(n,succ(m),%x.
                          ncase(m,ack(x,succ(zero)),%y. ack(x,ack(succ(x),y))))
                    in ack(a,b)"

lemmas nat_defs = not_def add_def mult_def sub_def le_def lt_def ack_def napply_def

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
  apply (tactic {* typechk_tac [] 1 *})
  done

lemma multT: "[| a:Nat;  b:Nat |] ==> a #* b : Nat"
  apply (unfold add_def mult_def)
  apply (tactic {* typechk_tac [] 1 *})
  done

(* Defined to return zero if a<b *)
lemma subT: "[| a:Nat;  b:Nat |] ==> a #- b : Nat"
  apply (unfold sub_def)
  apply (tactic {* typechk_tac [] 1 *})
  apply (tactic clean_ccs_tac)
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma leT: "[| a:Nat;  b:Nat |] ==> a #<= b : Bool"
  apply (unfold le_def)
  apply (tactic {* typechk_tac [] 1 *})
  apply (tactic clean_ccs_tac)
  apply (erule NatPRI [THEN wfstI, THEN NatPR_wf [THEN wmap_wf, THEN wfI]])
  done

lemma ltT: "[| a:Nat;  b:Nat |] ==> a #< b : Bool"
  apply (unfold not_def lt_def)
  apply (tactic {* typechk_tac [thm "leT"] 1 *})
  done


subsection {* Termination Conditions for Ackermann's Function *}

lemmas relI = NatPR_wf [THEN NatPR_wf [THEN lex_wf, THEN wfI]]

lemma "[| a:Nat;  b:Nat |] ==> ackermann(a,b) : Nat"
  apply (unfold ack_def)
  apply (tactic "gen_ccs_tac [] 1")
  apply (erule NatPRI [THEN lexI1 [THEN relI]] NatPRI [THEN lexI2 [THEN relI]])+
  done

end

