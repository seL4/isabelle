theory Live imports Natural
begin

text{* Which variables/locations does an expression depend on?
Any set of variables that completely determine the value of the expression,
in the worst case all locations: *}

consts Dep :: "((loc \<Rightarrow> 'a) \<Rightarrow> 'b) \<Rightarrow> loc set"
specification (Dep)
dep_on: "(\<forall>x\<in>Dep e. s x = t x) \<Longrightarrow> e s = e t"
by(rule_tac x="%x. UNIV" in exI)(simp add: expand_fun_eq[symmetric])

text{* The following definition of @{const Dep} looks very tempting
@{prop"Dep e = {a. EX s t. (ALL x. x\<noteq>a \<longrightarrow> s x = t x) \<and> e s \<noteq> e t}"}
but does not work in case @{text e} depends on an infinite set of variables.
For example, if @{term"e s"} tests if @{text s} is 0 at infinitely many locations. Then @{term"Dep e"} incorrectly yields the empty set!

If we had a concrete representation of expressions, we would simply write
a recursive free-variables function.
*}

primrec L :: "com \<Rightarrow> loc set \<Rightarrow> loc set" where
"L SKIP A = A" |
"L (x :== e) A = A-{x} \<union> Dep e" |
"L (c1; c2) A = (L c1 \<circ> L c2) A" |
"L (IF b THEN c1 ELSE c2) A = Dep b \<union> L c1 A \<union> L c2 A" |
"L (WHILE b DO c) A = Dep b \<union> A \<union> L c A"

primrec "kill" :: "com \<Rightarrow> loc set" where
"kill SKIP = {}" |
"kill (x :== e) = {x}" |
"kill (c1; c2) = kill c1 \<union> kill c2" |
"kill (IF b THEN c1 ELSE c2) = Dep b \<union> kill c1 \<inter>  kill c2" |
"kill (WHILE b DO c) = {}"

primrec gen :: "com \<Rightarrow> loc set" where
"gen SKIP = {}" |
"gen (x :== e) = Dep e" |
"gen (c1; c2) = gen c1 \<union> (gen c2-kill c1)" |
"gen (IF b THEN c1 ELSE c2) = Dep b \<union> gen c1 \<union> gen c2" |
"gen (WHILE b DO c) = Dep b \<union> gen c"

lemma L_gen_kill: "L c A = gen c \<union> (A - kill c)"
by(induct c arbitrary:A) auto

lemma L_idemp: "L c (L c A) \<subseteq> L c A"
by(fastsimp simp add:L_gen_kill)

theorem L_sound: "\<forall> x \<in> L c A. s x = t x \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>c,t\<rangle> \<longrightarrow>\<^sub>c t' \<Longrightarrow>
 \<forall>x\<in>A. s' x = t' x"
proof (induct c arbitrary: A s t s' t')
  case SKIP then show ?case by auto
next
  case (Assign x e) then show ?case
    by (auto simp:update_def ball_Un dest!: dep_on)
next
  case (Semi c1 c2)
  from Semi(4) obtain s'' where s1: "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s''" and s2: "\<langle>c2,s''\<rangle> \<longrightarrow>\<^sub>c s'"
    by auto
  from Semi(5) obtain t'' where t1: "\<langle>c1,t\<rangle> \<longrightarrow>\<^sub>c t''" and t2: "\<langle>c2,t''\<rangle> \<longrightarrow>\<^sub>c t'"
    by auto
  show ?case using Semi(1)[OF _ s1 t1] Semi(2)[OF _ s2 t2] Semi(3) by fastsimp
next
  case (Cond b c1 c2)
  show ?case
  proof cases
    assume "b s"
    hence s: "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s'" using Cond(4) by simp
    have "b t" using `b s` Cond(3) by (simp add: ball_Un)(blast dest: dep_on)
    hence t: "\<langle>c1,t\<rangle> \<longrightarrow>\<^sub>c t'" using Cond(5) by auto
    show ?thesis using Cond(1)[OF _ s t] Cond(3) by fastsimp
  next
    assume "\<not> b s"
    hence s: "\<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c s'" using Cond(4) by auto
    have "\<not> b t" using `\<not> b s` Cond(3) by (simp add: ball_Un)(blast dest: dep_on)
    hence t: "\<langle>c2,t\<rangle> \<longrightarrow>\<^sub>c t'" using Cond(5) by auto
    show ?thesis using Cond(2)[OF _ s t] Cond(3) by fastsimp
  qed
next
  case (While b c) note IH = this
  { fix cw
    have "\<langle>cw,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> cw = (While b c) \<Longrightarrow> \<langle>cw,t\<rangle> \<longrightarrow>\<^sub>c t' \<Longrightarrow>
          \<forall> x \<in> L cw A. s x = t x \<Longrightarrow> \<forall>x\<in>A. s' x = t' x"
    proof (induct arbitrary: t A pred:evalc)
      case WhileFalse
      have "\<not> b t" using WhileFalse by (simp add: ball_Un)(blast dest:dep_on)
      then have "t' = t" using WhileFalse by auto
      then show ?case using WhileFalse by auto
    next
      case (WhileTrue _ s _ s'' s')
      have "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s''" using WhileTrue(2,6) by simp
      have "b t" using WhileTrue by (simp add: ball_Un)(blast dest:dep_on)
      then obtain t'' where "\<langle>c,t\<rangle> \<longrightarrow>\<^sub>c t''" and "\<langle>While b c,t''\<rangle> \<longrightarrow>\<^sub>c t'"
        using WhileTrue(6,7) by auto
      have "\<forall>x\<in>Dep b \<union> A \<union> L c A. s'' x = t'' x"
        using IH(1)[OF _ `\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s''` `\<langle>c,t\<rangle> \<longrightarrow>\<^sub>c t''`] WhileTrue(6,8)
        by (auto simp:L_gen_kill)
      moreover then have "\<forall>x\<in>L (While b c) A. s'' x = t'' x" by auto
      ultimately show ?case using WhileTrue(5,6) `\<langle>While b c,t''\<rangle> \<longrightarrow>\<^sub>c t'` by metis
    qed auto }
  from this[OF IH(3) _ IH(4,2)] show ?case by metis
qed


primrec bury :: "com \<Rightarrow> loc set \<Rightarrow> com" where
"bury SKIP _ = SKIP" |
"bury (x :== e) A = (if x:A then x:== e else SKIP)" |
"bury (c1; c2) A = (bury c1 (L c2 A); bury c2 A)" |
"bury (IF b THEN c1 ELSE c2) A = (IF b THEN bury c1 A ELSE bury c2 A)" |
"bury (WHILE b DO c) A = (WHILE b DO bury c (Dep b \<union> A \<union> L c A))"

theorem bury_sound:
  "\<forall> x \<in> L c A. s x = t x \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> \<langle>bury c A,t\<rangle> \<longrightarrow>\<^sub>c t' \<Longrightarrow>
   \<forall>x\<in>A. s' x = t' x"
proof (induct c arbitrary: A s t s' t')
  case SKIP then show ?case by auto
next
  case (Assign x e) then show ?case
    by (auto simp:update_def ball_Un split:split_if_asm dest!: dep_on)
next
  case (Semi c1 c2)
  from Semi(4) obtain s'' where s1: "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s''" and s2: "\<langle>c2,s''\<rangle> \<longrightarrow>\<^sub>c s'"
    by auto
  from Semi(5) obtain t'' where t1: "\<langle>bury c1 (L c2 A),t\<rangle> \<longrightarrow>\<^sub>c t''" and t2: "\<langle>bury c2 A,t''\<rangle> \<longrightarrow>\<^sub>c t'"
    by auto
  show ?case using Semi(1)[OF _ s1 t1] Semi(2)[OF _ s2 t2] Semi(3) by fastsimp
next
  case (Cond b c1 c2)
  show ?case
  proof cases
    assume "b s"
    hence s: "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c s'" using Cond(4) by simp
    have "b t" using `b s` Cond(3) by (simp add: ball_Un)(blast dest: dep_on)
    hence t: "\<langle>bury c1 A,t\<rangle> \<longrightarrow>\<^sub>c t'" using Cond(5) by auto
    show ?thesis using Cond(1)[OF _ s t] Cond(3) by fastsimp
  next
    assume "\<not> b s"
    hence s: "\<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c s'" using Cond(4) by auto
    have "\<not> b t" using `\<not> b s` Cond(3) by (simp add: ball_Un)(blast dest: dep_on)
    hence t: "\<langle>bury c2 A,t\<rangle> \<longrightarrow>\<^sub>c t'" using Cond(5) by auto
    show ?thesis using Cond(2)[OF _ s t] Cond(3) by fastsimp
  qed
next
  case (While b c) note IH = this
  { fix cw
    have "\<langle>cw,s\<rangle> \<longrightarrow>\<^sub>c s' \<Longrightarrow> cw = (While b c) \<Longrightarrow> \<langle>bury cw A,t\<rangle> \<longrightarrow>\<^sub>c t' \<Longrightarrow>
          \<forall> x \<in> L cw A. s x = t x \<Longrightarrow> \<forall>x\<in>A. s' x = t' x"
    proof (induct arbitrary: t A pred:evalc)
      case WhileFalse
      have "\<not> b t" using WhileFalse by (simp add: ball_Un)(blast dest:dep_on)
      then have "t' = t" using WhileFalse by auto
      then show ?case using WhileFalse by auto
    next
      case (WhileTrue _ s _ s'' s')
      have "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s''" using WhileTrue(2,6) by simp
      have "b t" using WhileTrue by (simp add: ball_Un)(blast dest:dep_on)
      then obtain t'' where tt'': "\<langle>bury c (Dep b \<union> A \<union> L c A),t\<rangle> \<longrightarrow>\<^sub>c t''"
        and "\<langle>bury (While b c) A,t''\<rangle> \<longrightarrow>\<^sub>c t'"
        using WhileTrue(6,7) by auto
      have "\<forall>x\<in>Dep b \<union> A \<union> L c A. s'' x = t'' x"
        using IH(1)[OF _ `\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c s''` tt''] WhileTrue(6,8)
        by (auto simp:L_gen_kill)
      moreover then have "\<forall>x\<in>L (While b c) A. s'' x = t'' x" by auto
      ultimately show ?case
        using WhileTrue(5,6) `\<langle>bury (While b c) A,t''\<rangle> \<longrightarrow>\<^sub>c t'` by metis
    qed auto }
  from this[OF IH(3) _ IH(4,2)] show ?case by metis
qed


end