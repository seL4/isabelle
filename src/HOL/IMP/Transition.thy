(*  Title:        HOL/IMP/Transition.thy
    ID:           $Id$
    Author:       Tobias Nipkow & Robert Sandner, TUM
    Isar Version: Gerwin Klein, 2001
    Copyright     1996 TUM
*)

header "Transition Semantics of Commands"

theory Transition = Natural:

subsection "The transition relation"

text {*
  We formalize the transition semantics as in \cite{Nielson}. This
  makes some of the rules a bit more intuitive, but also requires
  some more (internal) formal overhead.
  
  Since configurations that have terminated are written without 
  a statement, the transition relation is not 
  @{typ "((com \<times> state) \<times> (com \<times> state)) set"}
  but instead:
*}
consts evalc1 :: "((com option \<times> state) \<times> (com option \<times> state)) set"

text {*
  Some syntactic sugar that we will use to hide the 
  @{text option} part in configurations:
*}
syntax
  "_angle" :: "[com, state] \<Rightarrow> com option \<times> state" ("<_,_>")
  "_angle2" :: "state \<Rightarrow> com option \<times> state" ("<_>")

syntax (xsymbols)
  "_angle" :: "[com, state] \<Rightarrow> com option \<times> state" ("\<langle>_,_\<rangle>")
  "_angle2" :: "state \<Rightarrow> com option \<times> state" ("\<langle>_\<rangle>")

translations
  "\<langle>c,s\<rangle>" == "(Some c, s)"
  "\<langle>s\<rangle>" == "(None, s)"

text {*
  More syntactic sugar for the transition relation, and its
  iteration.
*}
syntax
  "_evalc1" :: "[(com option\<times>state),(com option\<times>state)] \<Rightarrow> bool"
    ("_ -1-> _" [60,60] 60)
  "_evalcn" :: "[(com option\<times>state),nat,(com option\<times>state)] \<Rightarrow> bool"
    ("_ -_-> _" [60,60,60] 60)
  "_evalc*" :: "[(com option\<times>state),(com option\<times>state)] \<Rightarrow> bool"
    ("_ -*-> _" [60,60] 60)

syntax (xsymbols)
  "_evalc1" :: "[(com option\<times>state),(com option\<times>state)] \<Rightarrow> bool"
    ("_ \<longrightarrow>\<^sub>1 _" [60,60] 61)
  "_evalcn" :: "[(com option\<times>state),nat,(com option\<times>state)] \<Rightarrow> bool"
    ("_ -_\<rightarrow>\<^sub>1 _" [60,60,60] 60)
  "_evalc*" :: "[(com option\<times>state),(com option\<times>state)] \<Rightarrow> bool"
    ("_ \<longrightarrow>\<^sub>1\<^sup>* _" [60,60] 60)

translations
  "cs \<longrightarrow>\<^sub>1 cs'" == "(cs,cs') \<in> evalc1"
  "cs -n\<rightarrow>\<^sub>1 cs'" == "(cs,cs') \<in> evalc1^n" 
  "cs \<longrightarrow>\<^sub>1\<^sup>* cs'" == "(cs,cs') \<in> evalc1^*" 

  -- {* Isabelle converts @{text "(cs0,(c1,s1))"} to @{term "(cs0,c1,s1)"}, 
        so we also include: *}
  "cs0 \<longrightarrow>\<^sub>1 (c1,s1)" == "(cs0,c1,s1) \<in> evalc1"   
  "cs0 -n\<rightarrow>\<^sub>1 (c1,s1)" == "(cs0,c1,s1) \<in> evalc1^n"
  "cs0 \<longrightarrow>\<^sub>1\<^sup>* (c1,s1)" == "(cs0,c1,s1) \<in> evalc1^*" 

text {*
  Now, finally, we are set to write down the rules for our small step semantics:
*}
inductive evalc1
  intros
  Skip:    "\<langle>\<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s\<rangle>"  
  Assign:  "\<langle>x :== a, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s[x \<mapsto> a s]\<rangle>"

  Semi1:   "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s'\<rangle> \<Longrightarrow> \<langle>c0;c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1,s'\<rangle>"
  Semi2:   "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c0',s'\<rangle> \<Longrightarrow> \<langle>c0;c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c0';c1,s'\<rangle>"

  IfTrue:  "b s \<Longrightarrow> \<langle>\<IF> b \<THEN> c1 \<ELSE> c2,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1,s\<rangle>"
  IfFalse: "\<not>b s \<Longrightarrow> \<langle>\<IF> b \<THEN> c1 \<ELSE> c2,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c2,s\<rangle>"

  While:   "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<IF> b \<THEN> c; \<WHILE> b \<DO> c \<ELSE> \<SKIP>,s\<rangle>"

lemmas [intro] = evalc1.intros -- "again, use these rules in automatic proofs"

(*<*)
(* fixme: move to Relation_Power.thy *)
lemma rel_pow_Suc_E2 [elim!]:
  "[| (x, z) \<in> R ^ Suc n; !!y. [| (x, y) \<in> R; (y, z) \<in> R ^ n |] ==> P |] ==> P"
  by (drule rel_pow_Suc_D2) blast

lemma rtrancl_imp_rel_pow: "p \<in> R^* \<Longrightarrow> \<exists>n. p \<in> R^n"
proof -
  assume "p \<in> R\<^sup>*"
  moreover obtain x y where p: "p = (x,y)" by (cases p)
  ultimately have "(x,y) \<in> R\<^sup>*" by hypsubst
  hence "\<exists>n. (x,y) \<in> R^n"
  proof induct
    fix a have "(a,a) \<in> R^0" by simp
    thus "\<exists>n. (a,a) \<in> R ^ n" ..
  next
    fix a b c assume "\<exists>n. (a,b) \<in> R ^ n"
    then obtain n where "(a,b) \<in> R^n" ..
    moreover assume "(b,c) \<in> R"
    ultimately have "(a,c) \<in> R^(Suc n)" by auto
    thus "\<exists>n. (a,c) \<in> R^n" ..
  qed
  with p show ?thesis by hypsubst
qed  
(*>*)    
text {*
  As for the big step semantics you can read these rules in a 
  syntax directed way:
*}
lemma SKIP_1: "\<langle>\<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 y = (y = \<langle>s\<rangle>)" 
  by (rule, cases set: evalc1, auto)      

lemma Assign_1: "\<langle>x :== a, s\<rangle> \<longrightarrow>\<^sub>1 y = (y = \<langle>s[x \<mapsto> a s]\<rangle>)"
  by (rule, cases set: evalc1, auto)

lemma Cond_1: 
  "\<langle>\<IF> b \<THEN> c1 \<ELSE> c2, s\<rangle> \<longrightarrow>\<^sub>1 y = ((b s \<longrightarrow> y = \<langle>c1, s\<rangle>) \<and> (\<not>b s \<longrightarrow> y = \<langle>c2, s\<rangle>))"
  by (rule, cases set: evalc1, auto)

lemma While_1: 
  "\<langle>\<WHILE> b \<DO> c, s\<rangle> \<longrightarrow>\<^sub>1 y = (y = \<langle>\<IF> b \<THEN> c; \<WHILE> b \<DO> c \<ELSE> \<SKIP>, s\<rangle>)"
  by (rule, cases set: evalc1, auto)

lemmas [simp] = SKIP_1 Assign_1 Cond_1 While_1


subsection "Examples"

lemma 
  "s x = 0 \<Longrightarrow> \<langle>\<WHILE> \<lambda>s. s x \<noteq> 1 \<DO> (x:== \<lambda>s. s x+1), s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s[x \<mapsto> 1]\<rangle>"
  (is "_ \<Longrightarrow> \<langle>?w, _\<rangle> \<longrightarrow>\<^sub>1\<^sup>* _")
proof -
  let ?c  = "x:== \<lambda>s. s x+1"
  let ?if = "\<IF> \<lambda>s. s x \<noteq> 1 \<THEN> ?c; ?w \<ELSE> \<SKIP>"
  assume [simp]: "s x = 0"
  have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1  \<langle>?if, s\<rangle>" ..
  also have "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?c; ?w, s\<rangle>" by simp 
  also have "\<langle>?c; ?w, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?w, s[x \<mapsto> 1]\<rangle>" by (rule Semi1, simp)
  also have "\<langle>?w, s[x \<mapsto> 1]\<rangle> \<longrightarrow>\<^sub>1 \<langle>?if, s[x \<mapsto> 1]\<rangle>" ..
  also have "\<langle>?if, s[x \<mapsto> 1]\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<SKIP>, s[x \<mapsto> 1]\<rangle>" by (simp add: update_def)
  also have "\<langle>\<SKIP>, s[x \<mapsto> 1]\<rangle> \<longrightarrow>\<^sub>1 \<langle>s[x \<mapsto> 1]\<rangle>" ..
  finally show ?thesis ..
qed

lemma 
  "s x = 2 \<Longrightarrow> \<langle>\<WHILE> \<lambda>s. s x \<noteq> 1 \<DO> (x:== \<lambda>s. s x+1), s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* s'"
  (is "_ \<Longrightarrow> \<langle>?w, _\<rangle> \<longrightarrow>\<^sub>1\<^sup>* s'")
proof -
  let ?c = "x:== \<lambda>s. s x+1"
  let ?if = "\<IF> \<lambda>s. s x \<noteq> 1 \<THEN> ?c; ?w \<ELSE> \<SKIP>"  
  assume [simp]: "s x = 2"
  note update_def [simp]
  have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1  \<langle>?if, s\<rangle>" ..
  also have "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?c; ?w, s\<rangle>" by simp
  also have "\<langle>?c; ?w, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?w, s[x \<mapsto> 3]\<rangle>" by (rule Semi1, simp)
  also have "\<langle>?w, s[x \<mapsto> 3]\<rangle> \<longrightarrow>\<^sub>1 \<langle>?if, s[x \<mapsto> 3]\<rangle>" ..
  also have "\<langle>?if, s[x \<mapsto> 3]\<rangle> \<longrightarrow>\<^sub>1  \<langle>?c; ?w, s[x \<mapsto> 3]\<rangle>" by simp
  also have "\<langle>?c; ?w, s[x \<mapsto> 3]\<rangle> \<longrightarrow>\<^sub>1 \<langle>?w, s[x \<mapsto> 4]\<rangle>" by (rule Semi1, simp)
  also have "\<langle>?w, s[x \<mapsto> 4]\<rangle> \<longrightarrow>\<^sub>1 \<langle>?if, s[x \<mapsto> 4]\<rangle>" ..
  also have "\<langle>?if, s[x \<mapsto> 4]\<rangle> \<longrightarrow>\<^sub>1  \<langle>?c; ?w, s[x \<mapsto> 4]\<rangle>" by simp
  also have "\<langle>?c; ?w, s[x \<mapsto> 4]\<rangle> \<longrightarrow>\<^sub>1 \<langle>?w, s[x \<mapsto> 5]\<rangle>" by (rule Semi1, simp) 
  oops

subsection "Basic properties"

text {* 
  There are no \emph{stuck} programs:
*}
lemma no_stuck: "\<exists>y. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1 y"
proof (induct c)
  -- "case Semi:"
  fix c1 c2 assume "\<exists>y. \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1 y" 
  then obtain y where "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1 y" ..
  then obtain c1' s' where "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s'\<rangle> \<or> \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1',s'\<rangle>"
    by (cases y, cases "fst y", auto)
  thus "\<exists>s'. \<langle>c1;c2,s\<rangle> \<longrightarrow>\<^sub>1 s'" by auto
next
  -- "case If:"
  fix b c1 c2 assume "\<exists>y. \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1 y" and "\<exists>y. \<langle>c2,s\<rangle> \<longrightarrow>\<^sub>1 y"
  thus "\<exists>y. \<langle>\<IF> b \<THEN> c1 \<ELSE> c2, s\<rangle> \<longrightarrow>\<^sub>1 y" by (cases "b s") auto
qed auto -- "the rest is trivial"

text {*
  If a configuration does not contain a statement, the program
  has terminated and there is no next configuration:
*}
lemma stuck [elim!]: "\<langle>s\<rangle> \<longrightarrow>\<^sub>1 y \<Longrightarrow> P" 
  by (auto elim: evalc1.elims)

lemma evalc_None_retrancl [simp, dest!]: "\<langle>s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* s' \<Longrightarrow> s' = \<langle>s\<rangle>" 
  by (erule rtrancl_induct) auto 

(*<*)
(* fixme: relpow.simps don't work *)
lemma rel_pow_0 [simp]: "!!R::('a*'a) set. R^0 = Id" by simp
lemma rel_pow_Suc_0 [simp]: "!!R::('a*'a) set. R^(Suc 0) = R" by simp 
lemmas [simp del] = relpow.simps
(*>*)
lemma evalc1_None_0 [simp, dest!]: "\<langle>s\<rangle> -n\<rightarrow>\<^sub>1 y = (n = 0 \<and> y = \<langle>s\<rangle>)"
  by (cases n) auto

lemma SKIP_n: "\<langle>\<SKIP>, s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s'\<rangle> \<Longrightarrow> s' = s \<and> n=1" 
  by (cases n) auto

subsection "Equivalence to natural semantics (after Nielson and Nielson)"

text {*
  We first need two lemmas about semicolon statements:
  decomposition and composition.
*}
lemma semiD:
  "\<And>c1 c2 s s''. \<langle>c1; c2, s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle> \<Longrightarrow> 
  \<exists>i j s'. \<langle>c1, s\<rangle> -i\<rightarrow>\<^sub>1 \<langle>s'\<rangle> \<and> \<langle>c2, s'\<rangle> -j\<rightarrow>\<^sub>1 \<langle>s''\<rangle> \<and> n = i+j"
  (is "PROP ?P n")
proof (induct n)
  show "PROP ?P 0" by simp
next
  fix n assume IH: "PROP ?P n"
  show "PROP ?P (Suc n)"
  proof -
    fix c1 c2 s s''
    assume "\<langle>c1; c2, s\<rangle> -Suc n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>"
    then obtain y where
      1: "\<langle>c1; c2, s\<rangle> \<longrightarrow>\<^sub>1 y" and
      n: "y -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>"
      by blast

    from 1
    show "\<exists>i j s'. \<langle>c1, s\<rangle> -i\<rightarrow>\<^sub>1 \<langle>s'\<rangle> \<and> \<langle>c2, s'\<rangle> -j\<rightarrow>\<^sub>1 \<langle>s''\<rangle> \<and> Suc n = i+j"
      (is "\<exists>i j s'. ?Q i j s'")
    proof (cases set: evalc1)
      case Semi1
      then obtain s' where
        "y = \<langle>c2, s'\<rangle>" and "\<langle>c1, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s'\<rangle>"
        by auto
      with 1 n have "?Q 1 n s'" by simp
      thus ?thesis by blast
    next
      case Semi2
      then obtain c1' s' where
        y:  "y = \<langle>c1'; c2, s'\<rangle>" and
        c1: "\<langle>c1, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1', s'\<rangle>"
        by auto
      with n have "\<langle>c1'; c2, s'\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" by simp 
      with IH obtain i j s0 where 
        c1': "\<langle>c1',s'\<rangle> -i\<rightarrow>\<^sub>1 \<langle>s0\<rangle>" and
        c2:  "\<langle>c2,s0\<rangle> -j\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" and
        i:   "n = i+j"
        by fast
          
      from c1 c1'
      have "\<langle>c1,s\<rangle> -(i+1)\<rightarrow>\<^sub>1 \<langle>s0\<rangle>" by (auto intro: rel_pow_Suc_I2)
      with c2 i
      have "?Q (i+1) j s0" by simp
      thus ?thesis by blast
    qed auto -- "the remaining cases cannot occur"
  qed
qed


lemma semiI: 
  "\<And>c0 s s''. \<langle>c0,s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle> \<Longrightarrow> \<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle> \<Longrightarrow> \<langle>c0; c1, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
proof (induct n)
  fix c0 s s'' assume "\<langle>c0,s\<rangle> -(0::nat)\<rightarrow>\<^sub>1 \<langle>s''\<rangle>"
  hence False by simp
  thus "?thesis c0 s s''" ..
next
  fix c0 s s'' n 
  assume c0: "\<langle>c0,s\<rangle> -Suc n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>"
  assume c1: "\<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
  assume IH: "\<And>c0 s s''.
    \<langle>c0,s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle> \<Longrightarrow> \<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle> \<Longrightarrow> \<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
  from c0 obtain y where 
    1: "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>1 y" and n: "y -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" by blast
  from 1 obtain c0' s0' where
    "y = \<langle>s0'\<rangle> \<or> y = \<langle>c0', s0'\<rangle>" 
    by (cases y, cases "fst y", auto)
  moreover
  { assume y: "y = \<langle>s0'\<rangle>"
    with n have "s'' = s0'" by simp
    with y 1 have "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1, s''\<rangle>" by blast
    with c1 have "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by (blast intro: rtrancl_trans)
  }
  moreover
  { assume y: "y = \<langle>c0', s0'\<rangle>"
    with n have "\<langle>c0', s0'\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" by blast
    with IH c1 have "\<langle>c0'; c1,s0'\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by blast
    moreover
    from y 1 have "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c0'; c1,s0'\<rangle>" by blast
    hence "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>c0'; c1,s0'\<rangle>" by blast
    ultimately
    have "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by (blast intro: rtrancl_trans)
  }
  ultimately
  show "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by blast
qed

text {*
  The easy direction of the equivalence proof:
*}
lemma evalc_imp_evalc1: 
  "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>c, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
proof -
  assume "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'"
  thus "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
  proof induct
    fix s show "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s\<rangle>" by auto
  next
    fix x a s show "\<langle>x :== a ,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s[x\<mapsto>a s]\<rangle>" by auto
  next
    fix c0 c1 s s'' s'
    assume "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s''\<rangle>"
    then obtain n where "\<langle>c0,s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" by (blast dest: rtrancl_imp_rel_pow)
    moreover
    assume "\<langle>c1,s''\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
    ultimately
    show "\<langle>c0; c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by (rule semiI)
  next
    fix s::state and b c0 c1 s'
    assume "b s"
    hence "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c0,s\<rangle>" by simp
    also assume "\<langle>c0,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" 
    finally show "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" .
  next
    fix s::state and b c0 c1 s'
    assume "\<not>b s"
    hence "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c1,s\<rangle>" by simp
    also assume "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
    finally show "\<langle>\<IF> b \<THEN> c0 \<ELSE> c1,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" .
  next
    fix b c and s::state
    assume b: "\<not>b s"
    let ?if = "\<IF> b \<THEN> c; \<WHILE> b \<DO> c \<ELSE> \<SKIP>"
    have "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?if, s\<rangle>" by blast
    also have "\<langle>?if,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<SKIP>, s\<rangle>" by (simp add: b)
    also have "\<langle>\<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s\<rangle>" by blast
    finally show "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s\<rangle>" ..
  next
    fix b c s s'' s'
    let ?w  = "\<WHILE> b \<DO> c"
    let ?if = "\<IF> b \<THEN> c; ?w \<ELSE> \<SKIP>"
    assume w: "\<langle>?w,s''\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
    assume c: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s''\<rangle>"
    assume b: "b s"
    have "\<langle>?w,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>?if, s\<rangle>" by blast
    also have "\<langle>?if, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c; ?w, s\<rangle>" by (simp add: b)
    also 
    from c obtain n where "\<langle>c,s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" by (blast dest: rtrancl_imp_rel_pow)
    with w have "\<langle>c; ?w,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by - (rule semiI)
    finally show "\<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" ..
  qed
qed

text {*
  Finally, the equivalence theorem:
*}
theorem evalc_equiv_evalc1:
  "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>c s' = \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
proof
  assume "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'"
  show "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>" by (rule evalc_imp_evalc1)
next  
  assume "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s'\<rangle>"
  then obtain n where "\<langle>c, s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s'\<rangle>" by (blast dest: rtrancl_imp_rel_pow)
  moreover
  have "\<And>c s s'. \<langle>c, s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s'\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" 
  proof (induct rule: nat_less_induct)
    fix n
    assume IH: "\<forall>m. m < n \<longrightarrow> (\<forall>c s s'. \<langle>c, s\<rangle> -m\<rightarrow>\<^sub>1 \<langle>s'\<rangle> \<longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s')"
    fix c s s'
    assume c:  "\<langle>c, s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>s'\<rangle>"
    then obtain m where n: "n = Suc m" by (cases n) auto
    with c obtain y where 
      c': "\<langle>c, s\<rangle> \<longrightarrow>\<^sub>1 y" and m: "y -m\<rightarrow>\<^sub>1 \<langle>s'\<rangle>" by blast
    show "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" 
    proof (cases c)
      case SKIP
      with c n show ?thesis by auto
    next 
      case Assign
      with c n show ?thesis by auto
    next
      fix c1 c2 assume semi: "c = (c1; c2)"
      with c obtain i j s'' where
        c1: "\<langle>c1, s\<rangle> -i\<rightarrow>\<^sub>1 \<langle>s''\<rangle>" and
        c2: "\<langle>c2, s''\<rangle> -j\<rightarrow>\<^sub>1 \<langle>s'\<rangle>" and
        ij: "n = i+j"
        by (blast dest: semiD)
      from c1 c2 obtain 
        "0 < i" and "0 < j" by (cases i, auto, cases j, auto)
      with ij obtain
        i: "i < n" and j: "j < n" by simp
      from c1 i IH
      have "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s''" by blast
      moreover
      from c2 j IH
      have "\<langle>c2,s''\<rangle> \<longrightarrow>\<^sub>c s'" by blast
      moreover
      note semi
      ultimately
      show "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
    next
      fix b c1 c2 assume If: "c = \<IF> b \<THEN> c1 \<ELSE> c2"
      { assume True: "b s = True"
        with If c n
        have "\<langle>c1,s\<rangle> -m\<rightarrow>\<^sub>1 \<langle>s'\<rangle>" by auto      
        with n IH
        have "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
        with If True
        have "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by simp        
      }
      moreover
      { assume False: "b s = False"
        with If c n
        have "\<langle>c2,s\<rangle> -m\<rightarrow>\<^sub>1 \<langle>s'\<rangle>" by auto      
        with n IH
        have "\<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
        with If False
        have "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by simp        
      }
      ultimately
      show "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by (cases "b s") auto
    next
      fix b c' assume w: "c = \<WHILE> b \<DO> c'"
      with c n 
      have "\<langle>\<IF> b \<THEN> c'; \<WHILE> b \<DO> c' \<ELSE> \<SKIP>,s\<rangle> -m\<rightarrow>\<^sub>1 \<langle>s'\<rangle>"
        (is "\<langle>?if,_\<rangle> -m\<rightarrow>\<^sub>1 _") by auto
      with n IH
      have "\<langle>\<IF> b \<THEN> c'; \<WHILE> b \<DO> c' \<ELSE> \<SKIP>,s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
      moreover note unfold_while [of b c']
      -- {* @{thm unfold_while [of b c']} *}
      ultimately      
      have "\<langle>\<WHILE> b \<DO> c',s\<rangle> \<longrightarrow>\<^sub>c s'" by (blast dest: equivD2)
      with w show "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by simp
    qed
  qed
  ultimately
  show "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s'" by blast
qed


subsection "Winskel's Proof"

declare rel_pow_0_E [elim!]

text {*
  Winskel's small step rules are a bit different \cite{Winskel}; 
  we introduce their equivalents as derived rules:
*}
lemma whileFalse1 [intro]:
  "\<not> b s \<Longrightarrow> \<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s\<rangle>" (is "_ \<Longrightarrow> \<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s\<rangle>")  
proof -
  assume "\<not>b s"
  have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<IF> b \<THEN> c;?w \<ELSE> \<SKIP>, s\<rangle>" ..
  also have "\<langle>\<IF> b \<THEN> c;?w \<ELSE> \<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<SKIP>, s\<rangle>" ..
  also have "\<langle>\<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s\<rangle>" ..
  finally show "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s\<rangle>" ..
qed

lemma whileTrue1 [intro]:
  "b s \<Longrightarrow> \<langle>\<WHILE> b \<DO> c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>c;\<WHILE> b \<DO> c, s\<rangle>" 
  (is "_ \<Longrightarrow> \<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>c;?w,s\<rangle>")
proof -
  assume "b s"
  have "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>\<IF> b \<THEN> c;?w \<ELSE> \<SKIP>, s\<rangle>" ..
  also have "\<langle>\<IF> b \<THEN> c;?w \<ELSE> \<SKIP>, s\<rangle> \<longrightarrow>\<^sub>1 \<langle>c;?w, s\<rangle>" ..
  finally show "\<langle>?w, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>c;?w,s\<rangle>" ..
qed

inductive_cases evalc1_SEs: 
  "\<langle>\<SKIP>,s\<rangle> \<longrightarrow>\<^sub>1 t" 
  "\<langle>x:==a,s\<rangle> \<longrightarrow>\<^sub>1 t"
  "\<langle>c1;c2, s\<rangle> \<longrightarrow>\<^sub>1 t"
  "\<langle>\<IF> b \<THEN> c1 \<ELSE> c2, s\<rangle> \<longrightarrow>\<^sub>1 t"
  "\<langle>\<WHILE> b \<DO> c, s\<rangle> \<longrightarrow>\<^sub>1 t"

inductive_cases evalc1_E: "\<langle>\<WHILE> b \<DO> c, s\<rangle> \<longrightarrow>\<^sub>1 t"

declare evalc1_SEs [elim!]

lemma evalc_impl_evalc1: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s1 \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s1\<rangle>"
apply (erule evalc.induct)

-- SKIP 
apply blast

-- ASSIGN 
apply fast

-- SEMI 
apply (fast dest: rtrancl_imp_UN_rel_pow intro: semiI)

-- IF 
apply (fast intro: converse_rtrancl_into_rtrancl)
apply (fast intro: converse_rtrancl_into_rtrancl)

-- WHILE 
apply fast
apply (fast dest: rtrancl_imp_UN_rel_pow intro: converse_rtrancl_into_rtrancl semiI)

done


lemma lemma2 [rule_format (no_asm)]: 
  "\<forall>c d s u. \<langle>c;d,s\<rangle> -n\<rightarrow>\<^sub>1 \<langle>u\<rangle> \<longrightarrow> (\<exists>t m. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>t\<rangle> \<and> \<langle>d,t\<rangle> -m\<rightarrow>\<^sub>1 \<langle>u\<rangle> \<and> m \<le> n)"
apply (induct_tac "n")
 -- "case n = 0"
 apply fastsimp
-- "induction step"
apply (fast intro!: le_SucI le_refl dest!: rel_pow_Suc_D2 
            elim!: rel_pow_imp_rtrancl converse_rtrancl_into_rtrancl)
done

lemma evalc1_impl_evalc [rule_format (no_asm)]: 
  "\<forall>s t. \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>t\<rangle> \<longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
apply (induct_tac "c")
apply (safe dest!: rtrancl_imp_UN_rel_pow)

-- SKIP
apply (simp add: SKIP_n)

-- ASSIGN 
apply (fastsimp elim: rel_pow_E2)

-- SEMI
apply (fast dest!: rel_pow_imp_rtrancl lemma2)

-- IF 
apply (erule rel_pow_E2)
apply simp
apply (fast dest!: rel_pow_imp_rtrancl)

-- "WHILE, induction on the length of the computation"
apply (rename_tac b c s t n)
apply (erule_tac P = "?X -n\<rightarrow>\<^sub>1 ?Y" in rev_mp)
apply (rule_tac x = "s" in spec)
apply (induct_tac "n" rule: nat_less_induct)
apply (intro strip)
apply (erule rel_pow_E2)
 apply simp
apply (erule evalc1_E)

apply simp
apply (case_tac "b x")
 -- WhileTrue
 apply (erule rel_pow_E2)
  apply simp
 apply (clarify dest!: lemma2)
 apply (erule allE, erule allE, erule impE, assumption)
 apply (erule_tac x=mb in allE, erule impE, fastsimp)
 apply blast
-- WhileFalse 
apply (erule rel_pow_E2)
 apply simp
apply (simp add: SKIP_n)
done


text {* proof of the equivalence of evalc and evalc1 *}
lemma evalc1_eq_evalc: "(\<langle>c, s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>t\<rangle>) = (\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t)"
apply (fast elim!: evalc1_impl_evalc evalc_impl_evalc1)
done


subsection "A proof without n"

text {*
  The inductions are a bit awkward to write in this section,
  because @{text None} as result statement in the small step
  semantics doesn't have a direct counterpart in the big step
  semantics. 

  Winskel's small step rule set (using the @{text "\<SKIP>"} statement
  to indicate termination) is better suited for this proof.
*}

lemma my_lemma1 [rule_format (no_asm)]: 
  "\<langle>c1,s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s2\<rangle> \<Longrightarrow> \<langle>c2,s2\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3 \<Longrightarrow> \<langle>c1;c2,s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3"
proof -
  -- {* The induction rule needs @{text P} to be a function of @{term "Some c1"} *}
  have "\<langle>c1,s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s2\<rangle> \<Longrightarrow> \<langle>c2,s2\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3 \<longrightarrow> 
       \<langle>(\<lambda>c. if c = None then c2 else the c; c2) (Some c1),s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3"
    apply (erule converse_rtrancl_induct2)
     apply simp
    apply (rename_tac c s')
    apply simp
    apply (rule conjI)
     apply fast 
    apply clarify
    apply (case_tac c)
    apply (auto intro: converse_rtrancl_into_rtrancl)
    done
  moreover assume "\<langle>c1,s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s2\<rangle>" "\<langle>c2,s2\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3"
  ultimately show "\<langle>c1;c2,s1\<rangle> \<longrightarrow>\<^sub>1\<^sup>* cs3" by simp
qed

lemma evalc_impl_evalc1': "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s1 \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>s1\<rangle>"
apply (erule evalc.induct)

-- SKIP 
apply fast

-- ASSIGN
apply fast

-- SEMI 
apply (fast intro: my_lemma1)

-- IF
apply (fast intro: converse_rtrancl_into_rtrancl)
apply (fast intro: converse_rtrancl_into_rtrancl) 

-- WHILE 
apply fast
apply (fast intro: converse_rtrancl_into_rtrancl my_lemma1)

done

text {*
  The opposite direction is based on a Coq proof done by Ranan Fraer and
  Yves Bertot. The following sketch is from an email by Ranan Fraer.

\begin{verbatim}
First we've broke it into 2 lemmas:

Lemma 1
((c,s) --> (SKIP,t)) => (<c,s> -c-> t)

This is a quick one, dealing with the cases skip, assignment
and while_false.

Lemma 2
((c,s) -*-> (c',s')) /\ <c',s'> -c'-> t
  => 
<c,s> -c-> t

This is proved by rule induction on the  -*-> relation
and the induction step makes use of a third lemma: 

Lemma 3
((c,s) --> (c',s')) /\ <c',s'> -c'-> t
  => 
<c,s> -c-> t

This captures the essence of the proof, as it shows that <c',s'> 
behaves as the continuation of <c,s> with respect to the natural
semantics.
The proof of Lemma 3 goes by rule induction on the --> relation,
dealing with the cases sequence1, sequence2, if_true, if_false and
while_true. In particular in the case (sequence1) we make use again
of Lemma 1.
\end{verbatim}
*}

inductive_cases evalc1_term_cases: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>1 \<langle>s'\<rangle>"

lemma FB_lemma3 [rule_format]:
  "(c,s) \<longrightarrow>\<^sub>1 (c',s') \<Longrightarrow> c \<noteq> None \<longrightarrow>
  (\<forall>t. \<langle>if c'=None then \<SKIP> else the c',s'\<rangle> \<longrightarrow>\<^sub>c t \<longrightarrow> \<langle>the c,s\<rangle> \<longrightarrow>\<^sub>c t)"
  apply (erule evalc1.induct)
  apply (auto elim!: evalc1_term_cases equivD2 [OF unfold_while])
  done

lemma FB_lemma2 [rule_format]:
  "(c,s) \<longrightarrow>\<^sub>1\<^sup>* (c',s') \<Longrightarrow> c \<noteq> None \<longrightarrow> 
   \<langle>if c' = None then \<SKIP> else the c',s'\<rangle> \<longrightarrow>\<^sub>c t \<longrightarrow> \<langle>the c,s\<rangle> \<longrightarrow>\<^sub>c t" 
  apply (erule converse_rtrancl_induct2)
   apply simp
  apply clarsimp
  apply (fastsimp elim!: evalc1_term_cases intro: FB_lemma3)
  done

lemma evalc1_impl_evalc': "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>1\<^sup>* \<langle>t\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
  apply (fastsimp dest: FB_lemma2)
  done

end
