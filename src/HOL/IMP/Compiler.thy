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
ASIN:
       "\<lbrakk> n<size P; P!n = ASIN x a \<rbrakk> \<Longrightarrow> P |- <s,n> -1-> <s[x::= a s],Suc n>"
JMPFT:
       "\<lbrakk> n<size P; P!n = JMPF b i;  b s \<rbrakk> \<Longrightarrow> P |- <s,n> -1-> <s,Suc n>"
JMPFF:
       "\<lbrakk> n<size P; P!n = JMPF b i; ~b s; m=n+i \<rbrakk> \<Longrightarrow> P |- <s,n> -1-> <s,m>"
JMPB:
      "\<lbrakk> n<size P; P!n = JMPB i; i <= n \<rbrakk> \<Longrightarrow> P |- <s,n> -1-> <s,n-i>"

consts compile :: "com => instr list"
primrec
"compile SKIP = []"
"compile (x:==a) = [ASIN x a]"
"compile (c1;c2) = compile c1 @ compile c2"
"compile (IF b THEN c1 ELSE c2) =
 [JMPF b (length(compile c1) + 2)] @ compile c1 @
 [JMPF (%x. False) (length(compile c2)+1)] @ compile c2"
"compile (WHILE b DO c) = [JMPF b (length(compile c) + 2)] @ compile c @
 [JMPB (length(compile c)+1)]"

declare nth_append[simp];

(* Lemmas for lifting an execution into a prefix and suffix
   of instructions; only needed for the first proof *)

lemma app_right_1:
  "is1 |- <s1,i1> -1-> <s2,i2> \<Longrightarrow> is1 @ is2 |- <s1,i1> -1-> <s2,i2>"
apply(erule stepa1.induct);
   apply (simp add:ASIN)
  apply (force intro!:JMPFT)
 apply (force intro!:JMPFF)
apply (simp add: JMPB)
done      
      
lemma app_left_1:
  "is2 |- <s1,i1> -1-> <s2,i2> \<Longrightarrow>
   is1 @ is2 |- <s1,size is1+i1> -1-> <s2,size is1+i2>"
apply(erule stepa1.induct);
   apply (simp add:ASIN)
  apply (fastsimp intro!:JMPFT)
 apply (fastsimp intro!:JMPFF)
apply (simp add: JMPB)
done

lemma app_right:
  "is1 |- <s1,i1> -*-> <s2,i2> \<Longrightarrow> is1 @ is2 |- <s1,i1> -*-> <s2,i2>"
apply(erule rtrancl_induct2);
 apply simp
apply(blast intro:app_right_1 rtrancl_trans)
done

lemma app_left:
  "is2 |- <s1,i1> -*-> <s2,i2> \<Longrightarrow>
   is1 @ is2 |- <s1,size is1+i1> -*-> <s2,size is1+i2>"
apply(erule rtrancl_induct2);
 apply simp
apply(blast intro:app_left_1 rtrancl_trans)
done

lemma app_left2:
  "\<lbrakk> is2 |- <s1,i1> -*-> <s2,i2>; j1 = size is1+i1; j2 = size is1+i2 \<rbrakk> \<Longrightarrow>
   is1 @ is2 |- <s1,j1> -*-> <s2,j2>"
by (simp add:app_left)

lemma app1_left:
  "is |- <s1,i1> -*-> <s2,i2> \<Longrightarrow>
   instr # is |- <s1,Suc i1> -*-> <s2,Suc i2>"
by(erule app_left[of _ _ _ _ _ "[instr]",simplified])


(* The first proof; statement very intuitive,
   but application of induction hypothesis requires the above lifting lemmas
*)
theorem "<c,s> -c-> t ==> compile c |- <s,0> -*-> <t,length(compile c)>"
apply(erule evalc.induct);
      apply simp;
     apply(force intro!: ASIN);
    apply simp
    apply(rule rtrancl_trans)
    apply(erule app_right)
    apply(erule app_left[of _ 0,simplified])
(* IF b THEN c0 ELSE c1; case b is true *)
   apply(simp);
   (* execute JMPF: *)
   apply (rule rtrancl_into_rtrancl2)
    apply(force intro!: JMPFT);
   (* execute compile c0: *)
   apply(rule app1_left)
   apply(rule rtrancl_into_rtrancl);
    apply(erule app_right)
   (* execute JMPF: *)
   apply(force intro!: JMPFF);
(* end of case b is true *)
  apply simp
  apply (rule rtrancl_into_rtrancl2)
   apply(force intro!: JMPFF)
  apply(force intro!: app_left2 app1_left)
(* WHILE False *)
 apply(force intro: JMPFF);
(* WHILE True *)
apply(simp)
apply(rule rtrancl_into_rtrancl2);
 apply(force intro!: JMPFT);
apply(rule rtrancl_trans);
 apply(rule app1_left)
 apply(erule app_right)
apply(rule rtrancl_into_rtrancl2);
 apply(force intro!: JMPB)
apply(simp)
done

(* Second proof; statement is generalized to cater for prefixes and suffixes;
   needs none of the lifting lemmas, but instantiations of pre/suffix.
*)
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
    apply(force intro!: JMPFT);
   (* execute compile c0: *)
   apply(rule rtrancl_trans);
    apply(erule allE);
    apply assumption;
   (* execute JMPF: *)
   apply(rule r_into_rtrancl);
   apply(force intro!: JMPFF);
(* end of case b is true *)
  apply(intro strip);
  apply(erule_tac x = "a@[?I]@compile c0@[?J]" in allE);
  apply(simp add:add_assoc);
  apply(rule rtrancl_into_rtrancl2);
   apply(force intro!: JMPFF);
  apply(blast);
 apply(force intro: JMPFF);
apply(intro strip);
apply(erule_tac x = "a@[?I]" in allE);
apply(erule_tac x = a in allE);
apply(simp);
apply(rule rtrancl_into_rtrancl2);
 apply(force intro!: JMPFT);
apply(rule rtrancl_trans);
 apply(erule allE);
 apply assumption;
apply(rule rtrancl_into_rtrancl2);
 apply(force intro!: JMPB);
apply(simp);
done

(* Missing: the other direction! *)

end
