(*  Title:      HOL/IMP/Compiler.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TUM
    Copyright   1996 TUM

This is an early version of the compiler, where the abstract machine
has an explicit pc. This turned out to be awkward, and a second
development was started. See Machines.thy and Compiler.thy.
*)

header "A Simple Compiler"

theory Compiler0 = Natural:

subsection "An abstract, simplistic machine"

text {* There are only three instructions: *}
datatype instr = ASIN loc aexp | JMPF bexp nat | JMPB nat

text {* We describe execution of programs in the machine by
  an operational (small step) semantics:
*}
consts  stepa1 :: "instr list \<Rightarrow> ((state\<times>nat) \<times> (state\<times>nat))set"

syntax
  "_stepa1" :: "[instr list,state,nat,state,nat] \<Rightarrow> bool"
               ("_ |- (3<_,_>/ -1-> <_,_>)" [50,0,0,0,0] 50)
  "_stepa" :: "[instr list,state,nat,state,nat] \<Rightarrow> bool"
               ("_ |-/ (3<_,_>/ -*-> <_,_>)" [50,0,0,0,0] 50)

  "_stepan" :: "[instr list,state,nat,nat,state,nat] \<Rightarrow> bool"
               ("_ |-/ (3<_,_>/ -(_)-> <_,_>)" [50,0,0,0,0,0] 50)

syntax (xsymbols)
  "_stepa1" :: "[instr list,state,nat,state,nat] \<Rightarrow> bool"
               ("_ \<turnstile> (3\<langle>_,_\<rangle>/ -1\<rightarrow> \<langle>_,_\<rangle>)" [50,0,0,0,0] 50)
  "_stepa" :: "[instr list,state,nat,state,nat] \<Rightarrow> bool"
               ("_ \<turnstile>/ (3\<langle>_,_\<rangle>/ -*\<rightarrow> \<langle>_,_\<rangle>)" [50,0,0,0,0] 50)
  "_stepan" :: "[instr list,state,nat,nat,state,nat] \<Rightarrow> bool"
               ("_ \<turnstile>/ (3\<langle>_,_\<rangle>/ -(_)\<rightarrow> \<langle>_,_\<rangle>)" [50,0,0,0,0,0] 50)

translations  
  "P \<turnstile> \<langle>s,m\<rangle> -1\<rightarrow> \<langle>t,n\<rangle>" == "((s,m),t,n) : stepa1 P"
  "P \<turnstile> \<langle>s,m\<rangle> -*\<rightarrow> \<langle>t,n\<rangle>" == "((s,m),t,n) : ((stepa1 P)^*)"
  "P \<turnstile> \<langle>s,m\<rangle> -(i)\<rightarrow> \<langle>t,n\<rangle>" == "((s,m),t,n) : ((stepa1 P)^i)"

inductive "stepa1 P"
intros
ASIN[simp]:
  "\<lbrakk> n<size P; P!n = ASIN x a \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>s,n\<rangle> -1\<rightarrow> \<langle>s[x\<mapsto> a s],Suc n\<rangle>"
JMPFT[simp,intro]:
  "\<lbrakk> n<size P; P!n = JMPF b i;  b s \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>s,n\<rangle> -1\<rightarrow> \<langle>s,Suc n\<rangle>"
JMPFF[simp,intro]:
  "\<lbrakk> n<size P; P!n = JMPF b i; ~b s; m=n+i \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>s,n\<rangle> -1\<rightarrow> \<langle>s,m\<rangle>"
JMPB[simp]:
  "\<lbrakk> n<size P; P!n = JMPB i; i <= n; j = n-i \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>s,n\<rangle> -1\<rightarrow> \<langle>s,j\<rangle>"

subsection "The compiler"

consts compile :: "com \<Rightarrow> instr list"
primrec
"compile \<SKIP> = []"
"compile (x:==a) = [ASIN x a]"
"compile (c1;c2) = compile c1 @ compile c2"
"compile (\<IF> b \<THEN> c1 \<ELSE> c2) =
 [JMPF b (length(compile c1) + 2)] @ compile c1 @
 [JMPF (%x. False) (length(compile c2)+1)] @ compile c2"
"compile (\<WHILE> b \<DO> c) = [JMPF b (length(compile c) + 2)] @ compile c @
 [JMPB (length(compile c)+1)]"

declare nth_append[simp]

subsection "Context lifting lemmas"

text {* 
  Some lemmas for lifting an execution into a prefix and suffix
  of instructions; only needed for the first proof.
*}
lemma app_right_1:
  assumes A: "is1 \<turnstile> \<langle>s1,i1\<rangle> -1\<rightarrow> \<langle>s2,i2\<rangle>"
  shows "is1 @ is2 \<turnstile> \<langle>s1,i1\<rangle> -1\<rightarrow> \<langle>s2,i2\<rangle>"
proof -
 from A show ?thesis
 by induct force+
qed

lemma app_left_1:
  assumes A: "is2 \<turnstile> \<langle>s1,i1\<rangle> -1\<rightarrow> \<langle>s2,i2\<rangle>"
  shows "is1 @ is2 \<turnstile> \<langle>s1,size is1+i1\<rangle> -1\<rightarrow> \<langle>s2,size is1+i2\<rangle>"
proof -
 from A show ?thesis
 by induct force+
qed

declare rtrancl_induct2 [induct set: rtrancl]

lemma app_right:
assumes A: "is1 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle>"
shows "is1 @ is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle>"
proof -
 from A show ?thesis
 proof induct
   show "is1 @ is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s1,i1\<rangle>" by simp
 next
   fix s1' i1' s2 i2
   assume "is1 @ is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s1',i1'\<rangle>"
          "is1 \<turnstile> \<langle>s1',i1'\<rangle> -1\<rightarrow> \<langle>s2,i2\<rangle>"
   thus "is1 @ is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle>"
     by(blast intro:app_right_1 rtrancl_trans)
 qed
qed

lemma app_left:
assumes A: "is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle>"
shows "is1 @ is2 \<turnstile> \<langle>s1,size is1+i1\<rangle> -*\<rightarrow> \<langle>s2,size is1+i2\<rangle>"
proof -
  from A show ?thesis
  proof induct
    show "is1 @ is2 \<turnstile> \<langle>s1,length is1 + i1\<rangle> -*\<rightarrow> \<langle>s1,length is1 + i1\<rangle>" by simp
  next
    fix s1' i1' s2 i2
    assume "is1 @ is2 \<turnstile> \<langle>s1,length is1 + i1\<rangle> -*\<rightarrow> \<langle>s1',length is1 + i1'\<rangle>"
           "is2 \<turnstile> \<langle>s1',i1'\<rangle> -1\<rightarrow> \<langle>s2,i2\<rangle>"
    thus "is1 @ is2 \<turnstile> \<langle>s1,length is1 + i1\<rangle> -*\<rightarrow> \<langle>s2,length is1 + i2\<rangle>"
      by(blast intro:app_left_1 rtrancl_trans)
 qed
qed

lemma app_left2:
  "\<lbrakk> is2 \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle>; j1 = size is1+i1; j2 = size is1+i2 \<rbrakk> \<Longrightarrow>
   is1 @ is2 \<turnstile> \<langle>s1,j1\<rangle> -*\<rightarrow> \<langle>s2,j2\<rangle>"
  by (simp add:app_left)

lemma app1_left:
  "is \<turnstile> \<langle>s1,i1\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle> \<Longrightarrow>
   instr # is \<turnstile> \<langle>s1,Suc i1\<rangle> -*\<rightarrow> \<langle>s2,Suc i2\<rangle>"
  by(erule app_left[of _ _ _ _ _ "[instr]",simplified])

subsection "Compiler correctness"

declare rtrancl_into_rtrancl[trans]
        converse_rtrancl_into_rtrancl[trans]
        rtrancl_trans[trans]

text {*
  The first proof; The statement is very intuitive,
  but application of induction hypothesis requires the above lifting lemmas
*}
theorem assumes A: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
shows "compile c \<turnstile> \<langle>s,0\<rangle> -*\<rightarrow> \<langle>t,length(compile c)\<rangle>" (is "?P c s t")
proof -
  from A show ?thesis
  proof induct
    show "\<And>s. ?P \<SKIP> s s" by simp
  next
    show "\<And>a s x. ?P (x :== a) s (s[x\<mapsto> a s])" by force
  next
    fix c0 c1 s0 s1 s2
    assume "?P c0 s0 s1"
    hence "compile c0 @ compile c1 \<turnstile> \<langle>s0,0\<rangle> -*\<rightarrow> \<langle>s1,length(compile c0)\<rangle>"
      by(rule app_right)
    moreover assume "?P c1 s1 s2"
    hence "compile c0 @ compile c1 \<turnstile> \<langle>s1,length(compile c0)\<rangle> -*\<rightarrow>
           \<langle>s2,length(compile c0)+length(compile c1)\<rangle>"
    proof -
      show "\<And>is1 is2 s1 s2 i2.
	      is2 \<turnstile> \<langle>s1,0\<rangle> -*\<rightarrow> \<langle>s2,i2\<rangle> \<Longrightarrow>
	      is1 @ is2 \<turnstile> \<langle>s1,size is1\<rangle> -*\<rightarrow> \<langle>s2,size is1+i2\<rangle>"
	using app_left[of _ 0] by simp
    qed
    ultimately have "compile c0 @ compile c1 \<turnstile> \<langle>s0,0\<rangle> -*\<rightarrow>
                       \<langle>s2,length(compile c0)+length(compile c1)\<rangle>"
      by (rule rtrancl_trans)
    thus "?P (c0; c1) s0 s2" by simp
  next
    fix b c0 c1 s0 s1
    let ?comp = "compile(\<IF> b \<THEN> c0 \<ELSE> c1)"
    assume "b s0" and IH: "?P c0 s0 s1"
    hence "?comp \<turnstile> \<langle>s0,0\<rangle> -1\<rightarrow> \<langle>s0,1\<rangle>" by auto
    also from IH
    have "?comp \<turnstile> \<langle>s0,1\<rangle> -*\<rightarrow> \<langle>s1,length(compile c0)+1\<rangle>"
      by(auto intro:app1_left app_right)
    also have "?comp \<turnstile> \<langle>s1,length(compile c0)+1\<rangle> -1\<rightarrow> \<langle>s1,length ?comp\<rangle>"
      by(auto)
    finally show "?P (\<IF> b \<THEN> c0 \<ELSE> c1) s0 s1" .
  next
    fix b c0 c1 s0 s1
    let ?comp = "compile(\<IF> b \<THEN> c0 \<ELSE> c1)"
    assume "\<not>b s0" and IH: "?P c1 s0 s1"
    hence "?comp \<turnstile> \<langle>s0,0\<rangle> -1\<rightarrow> \<langle>s0,length(compile c0) + 2\<rangle>" by auto
    also from IH
    have "?comp \<turnstile> \<langle>s0,length(compile c0)+2\<rangle> -*\<rightarrow> \<langle>s1,length ?comp\<rangle>"
      by(force intro!:app_left2 app1_left)
    finally show "?P (\<IF> b \<THEN> c0 \<ELSE> c1) s0 s1" .
  next
    fix b c and s::state
    assume "\<not>b s"
    thus "?P (\<WHILE> b \<DO> c) s s" by force
  next
    fix b c and s0::state and s1 s2
    let ?comp = "compile(\<WHILE> b \<DO> c)"
    assume "b s0" and
      IHc: "?P c s0 s1" and IHw: "?P (\<WHILE> b \<DO> c) s1 s2"
    hence "?comp \<turnstile> \<langle>s0,0\<rangle> -1\<rightarrow> \<langle>s0,1\<rangle>" by auto
    also from IHc
    have "?comp \<turnstile> \<langle>s0,1\<rangle> -*\<rightarrow> \<langle>s1,length(compile c)+1\<rangle>"
      by(auto intro:app1_left app_right)
    also have "?comp \<turnstile> \<langle>s1,length(compile c)+1\<rangle> -1\<rightarrow> \<langle>s1,0\<rangle>" by simp
    also note IHw
    finally show "?P (\<WHILE> b \<DO> c) s0 s2".
  qed
qed

text {*
  Second proof; statement is generalized to cater for prefixes and suffixes;
  needs none of the lifting lemmas, but instantiations of pre/suffix.
  *}
theorem "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t \<Longrightarrow> 
  !a z. a@compile c@z \<turnstile> \<langle>s,length a\<rangle> -*\<rightarrow> \<langle>t,length a + length(compile c)\<rangle>";
apply(erule evalc.induct)
      apply simp
     apply(force intro!: ASIN)
    apply(intro strip)
    apply(erule_tac x = a in allE)
    apply(erule_tac x = "a@compile c0" in allE)
    apply(erule_tac x = "compile c1@z" in allE)
    apply(erule_tac x = z in allE)
    apply(simp add:add_assoc[THEN sym])
    apply(blast intro:rtrancl_trans)
(* \<IF> b \<THEN> c0 \<ELSE> c1; case b is true *)
   apply(intro strip)
   (* instantiate assumption sufficiently for later: *)
   apply(erule_tac x = "a@[?I]" in allE)
   apply(simp)
   (* execute JMPF: *)
   apply(rule converse_rtrancl_into_rtrancl)
    apply(force intro!: JMPFT)
   (* execute compile c0: *)
   apply(rule rtrancl_trans)
    apply(erule allE)
    apply assumption
   (* execute JMPF: *)
   apply(rule r_into_rtrancl)
   apply(force intro!: JMPFF)
(* end of case b is true *)
  apply(intro strip)
  apply(erule_tac x = "a@[?I]@compile c0@[?J]" in allE)
  apply(simp add:add_assoc)
  apply(rule converse_rtrancl_into_rtrancl)
   apply(force intro!: JMPFF)
  apply(blast)
 apply(force intro: JMPFF)
apply(intro strip)
apply(erule_tac x = "a@[?I]" in allE)
apply(erule_tac x = a in allE)
apply(simp)
apply(rule converse_rtrancl_into_rtrancl)
 apply(force intro!: JMPFT)
apply(rule rtrancl_trans)
 apply(erule allE)
 apply assumption
apply(rule converse_rtrancl_into_rtrancl)
 apply(force intro!: JMPB)
apply(simp)
done

text {* Missing: the other direction! I did much of it, and although
the main lemma is very similar to the one in the new development, the
lemmas surrounding it seemed much more complicated. In the end I gave
up. *}

end
