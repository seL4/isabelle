(*  Title:      HOL/IMP/Compiler.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TUM
    Copyright   1996 TUM

A simple compiler for a simplistic machine.
*)

theory Compiler = Natural:

datatype instr = ASIN loc aexp | JMPF bexp nat | JMPB nat

consts  stepa1 :: "instr list => ((state*nat) * (state*nat))set"

syntax
        "@stepa1" :: "[instr list,state,nat,state,nat] => bool"
                     ("_ |- <_,_>/ -1-> <_,_>" [50,0,0,0,0] 50)
        "@stepa" :: "[instr list,state,nat,state,nat] => bool"
                     ("_ |-/ <_,_>/ -*-> <_,_>" [50,0,0,0,0] 50)

translations  "P |- <s,m> -1-> <t,n>" == "((s,m),t,n) : stepa1 P"
              "P |- <s,m> -*-> <t,n>" == "((s,m),t,n) : ((stepa1 P)^*)"


inductive "stepa1 P"
intros
ASIN:  "P!n = ASIN x a ==> P |- <s,n> -1-> <s[x::= a s],Suc n>"
JMPFT: "[| P!n = JMPF b i;  b s |] ==> P |- <s,n> -1-> <s,Suc n>"
JMPFF: "[| P!n = JMPF b i; ~b s; m=n+i |] ==> P |- <s,n> -1-> <s,m>"
JMPB:  "[| P!n = JMB i |] ==> P |- <s,n> -1-> <s,n-i>"

consts compile :: "com => instr list"
primrec
"compile SKIP = []"
"compile (x:==a) = [ASIN x a]"
"compile (c1;c2) = compile c1 @ compile c2"
"compile (IF b THEN c1 ELSE c2) =
 [JMPF b (length(compile c1)+2)] @ compile c1 @
 [JMPF (%x. False) (length(compile c2)+1)] @ compile c2"
"compile (WHILE b DO c) = [JMPF b (length(compile c)+2)] @ compile c @
 [JMPB (length(compile c)+1)]"

declare nth_append[simp];

lemma nth_tl[simp]: "tl(xs @ y # ys) ! (length xs + z) = ys!z";
apply(induct_tac xs);
by(auto);

theorem "<c,s> -c-> t ==> 
 !a z. a@compile c@z |- <s,length a> -*-> <t,length a + length(compile c)>";
apply(erule evalc.induct);
      apply simp;
     apply(force intro!: ASIN);
    apply(intro strip);
    apply(erule_tac x = a in allE);
    apply(erule_tac x = "a@compile c0" in allE);
    apply(erule_tac x = "compile c1@z" in allE);
    apply(erule_tac x = z in allE);
    apply(simp add:add_assoc[THEN sym]);
    apply(blast intro:rtrancl_trans);
(* IF b THEN c0 ELSE c1; case b is true *)
   apply(intro strip);
   (* instantiate assumption sufficiently for later: *)
   apply(erule_tac x = "a@[?I]" in allE);
   apply(simp);
   (* execute JMPF: *)
   apply(rule rtrancl_into_rtrancl2);
    apply(rule JMPFT);
     apply(simp);
     apply(blast);
    apply assumption;
   (* execute compile c0: *)
   apply(rule rtrancl_trans);
    apply(erule allE);
    apply assumption;
   (* execute JMPF: *)
   apply(rule r_into_rtrancl);
   apply(rule JMPFF);
     apply(simp);
     apply(blast);
    apply(blast);
   apply(simp);
(* end of case b is true *)
  apply(intro strip);
  apply(erule_tac x = "a@[?I]@compile c0@[?J]" in allE);
  apply(simp add:add_assoc);
  apply(rule rtrancl_into_rtrancl2);
   apply(rule JMPFF);
     apply(simp);
     apply(blast);
    apply assumption;
   apply(simp);
  apply(blast);
 apply(force intro: JMPFF);
apply(intro strip);
apply(erule_tac x = "a@[?I]" in allE);
apply(erule_tac x = a in allE);
apply(simp);
apply(rule rtrancl_into_rtrancl2);
 apply(rule JMPFT);
  apply(simp);
  apply(blast);
 apply assumption;
apply(rule rtrancl_trans);
 apply(erule allE);
 apply assumption;
apply(rule rtrancl_into_rtrancl2);
 apply(rule JMPB);
 apply(simp);
apply(simp);
done

(* Missing: the other direction! *)

end
