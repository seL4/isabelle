header {* Correctness of Definite Assignment *}

theory DefiniteAssignmentCorrect = WellForm + Eval:

ML {*
Delsimprocs [wt_expr_proc,wt_var_proc,wt_exprs_proc,wt_stmt_proc]
*}

lemma sxalloc_no_jump:
  assumes sxalloc: "G\<turnstile>s0 \<midarrow>sxalloc\<rightarrow> s1" and
           no_jmp: "abrupt s0 \<noteq> Some (Jump j)"
   shows "abrupt s1 \<noteq> Some (Jump j)"
using sxalloc no_jmp
by cases simp_all

lemma sxalloc_no_jump':
  assumes sxalloc: "G\<turnstile>s0 \<midarrow>sxalloc\<rightarrow> s1" and
          jump:  "abrupt s1 = Some (Jump j)"
 shows "abrupt s0 = Some (Jump j)"
using sxalloc jump
by cases simp_all

lemma halloc_no_jump:
  assumes halloc: "G\<turnstile>s0 \<midarrow>halloc oi\<succ>a\<rightarrow> s1" and
           no_jmp: "abrupt s0 \<noteq> Some (Jump j)"
   shows "abrupt s1 \<noteq> Some (Jump j)"
using halloc no_jmp
by cases simp_all

lemma halloc_no_jump':
  assumes halloc: "G\<turnstile>s0 \<midarrow>halloc oi\<succ>a\<rightarrow> s1" and
          jump:  "abrupt s1 = Some (Jump j)"
  shows "abrupt s0 = Some (Jump j)"
using halloc jump
by cases simp_all

lemma Body_no_jump: 
   assumes eval: "G\<turnstile>s0 \<midarrow>Body D c-\<succ>v\<rightarrow>s1" and
           jump: "abrupt s0 \<noteq> Some (Jump j)"
   shows "abrupt s1 \<noteq> Some (Jump j)"
proof (cases "normal s0")
  case True
  with eval obtain s0' where eval': "G\<turnstile>Norm s0' \<midarrow>Body D c-\<succ>v\<rightarrow>s1" and
                             s0: "s0 = Norm s0'"
    by (cases s0) simp
  from eval' obtain s2 where
     s1: "s1 = abupd (absorb Ret)
             (if \<exists>l. abrupt s2 = Some (Jump (Break l)) \<or>
                     abrupt s2 = Some (Jump (Cont l))
              then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 else s2)"
    by cases simp
  show ?thesis
  proof (cases "\<exists>l. abrupt s2 = Some (Jump (Break l)) \<or> 
                   abrupt s2 = Some (Jump (Cont l))")
    case True
    with s1 have "abrupt s1 = Some (Error CrossMethodJump)"
      by (cases s2) simp
    thus ?thesis by simp
  next
    case False
    with s1 have "s1=abupd (absorb Ret) s2"
      by simp
    with False show ?thesis
      by (cases s2,cases j) (auto simp add: absorb_def)
  qed
next
  case False
  with eval obtain s0' abr where "G\<turnstile>(Some abr,s0') \<midarrow>Body D c-\<succ>v\<rightarrow>s1"
                                 "s0 = (Some abr, s0')"
    by (cases s0) fastsimp
  with this jump
  show ?thesis
    by (cases) (simp)
qed

lemma Methd_no_jump: 
   assumes eval: "G\<turnstile>s0 \<midarrow>Methd D sig-\<succ>v\<rightarrow> s1" and
           jump: "abrupt s0 \<noteq> Some (Jump j)"
   shows "abrupt s1 \<noteq> Some (Jump j)"
proof (cases "normal s0")
  case True
   with eval obtain s0' where "G\<turnstile>Norm s0' \<midarrow>Methd D sig-\<succ>v\<rightarrow>s1" 
                              "s0 = Norm s0'"
    by (cases s0) simp
  then obtain D' body where "G\<turnstile>s0 \<midarrow>Body D' body-\<succ>v\<rightarrow>s1"
    by (cases) (simp add: body_def2)
  from this jump
  show ?thesis
    by (rule Body_no_jump)
next
  case False
  with eval obtain s0' abr where "G\<turnstile>(Some abr,s0') \<midarrow>Methd D sig-\<succ>v\<rightarrow>s1"
                                 "s0 = (Some abr, s0')"
    by (cases s0) fastsimp
  with this jump
  show ?thesis
    by (cases) (simp)
qed

lemma jumpNestingOkS_mono: 
  assumes jumpNestingOk_l': "jumpNestingOkS jmps' c" 
      and      subset: "jmps' \<subseteq> jmps"
 shows "jumpNestingOkS jmps c"
proof -
    have True and True and 
       "\<And> jmps' jmps. \<lbrakk>jumpNestingOkS jmps' c; jmps' \<subseteq> jmps\<rbrakk> \<Longrightarrow> jumpNestingOkS jmps c" 
       and True
  proof (induct rule: var_expr_stmt.induct)
    case (Lab j c jmps' jmps)
    have jmpOk: "jumpNestingOkS jmps' (j\<bullet> c)" .
    have jmps: "jmps' \<subseteq> jmps" .
    with jmpOk have "jumpNestingOkS ({j} \<union> jmps') c" by simp
    moreover from jmps have "({j} \<union> jmps') \<subseteq> ({j} \<union> jmps)" by auto
    ultimately
    have "jumpNestingOkS ({j} \<union> jmps) c"
      by (rule Lab.hyps)
    thus ?case 
      by simp
  next
    case (Jmp j jmps' jmps) 
    thus ?case 
      by (cases j) auto
  next
    case (Comp c1 c2 jmps' jmps)
    from Comp.prems 
    have "jumpNestingOkS jmps c1" by - (rule Comp.hyps,auto)
    moreover from Comp.prems
    have "jumpNestingOkS jmps c2" by - (rule Comp.hyps,auto)
    ultimately show ?case
      by simp
  next
    case (If_ e c1 c2 jmps' jmps)
    from If_.prems 
    have "jumpNestingOkS jmps c1" by - (rule If_.hyps,auto)
    moreover from If_.prems 
    have "jumpNestingOkS jmps c2" by - (rule If_.hyps,auto)
    ultimately show ?case
      by simp
  next
    case (Loop l e c jmps' jmps)
    have "jumpNestingOkS jmps' (l\<bullet> While(e) c)" .
    hence "jumpNestingOkS ({Cont l} \<union> jmps') c" by simp
    moreover have "jmps' \<subseteq> jmps" .
    hence "{Cont l} \<union> jmps'  \<subseteq> {Cont l} \<union> jmps" by auto
    ultimately
    have "jumpNestingOkS ({Cont l} \<union> jmps) c"
      by (rule Loop.hyps)
    thus ?case by simp
  next
    case (TryC c1 C vn c2 jmps' jmps)
    from TryC.prems 
    have "jumpNestingOkS jmps c1" by - (rule TryC.hyps,auto)
    moreover from TryC.prems 
    have "jumpNestingOkS jmps c2" by - (rule TryC.hyps,auto)
    ultimately show ?case
      by simp
  next
    case (Fin c1 c2 jmps' jmps)
    from Fin.prems 
    have "jumpNestingOkS jmps c1" by - (rule Fin.hyps,auto)
    moreover from Fin.prems 
    have "jumpNestingOkS jmps c2" by - (rule Fin.hyps,auto)
    ultimately show ?case
      by simp
  qed (simp_all)
  with jumpNestingOk_l' subset
  show ?thesis
    by rules
qed
   
corollary jumpNestingOk_mono: 
  assumes jmpOk: "jumpNestingOk jmps' t" 
     and subset: "jmps' \<subseteq> jmps"
  shows  "jumpNestingOk jmps t"
proof (cases t)
  case (In1 expr_stmt)
  show ?thesis
  proof (cases expr_stmt)
    case (Inl e)
    with In1 show ?thesis by simp
  next
    case (Inr s)
    with In1 jmpOk subset show ?thesis by (auto intro: jumpNestingOkS_mono)
  qed
qed (simp_all)

lemma assign_abrupt_propagation: 
 assumes f_ok: "abrupt (f n s) \<noteq> x"
   and    ass: "abrupt (assign f n s) = x"
  shows "abrupt s = x"
proof (cases x)
  case None
  with ass show ?thesis
    by (cases s) (simp add: assign_def Let_def)
next
  case (Some xcpt)
  from f_ok
  obtain xf sf where "f n s = (xf,sf)"
    by (cases "f n s")
  with Some ass f_ok show ?thesis
    by (cases s) (simp add: assign_def Let_def)
qed
 
lemma wt_init_comp_ty': 
"is_acc_type (prg Env) (pid (cls Env)) T \<Longrightarrow> Env\<turnstile>init_comp_ty T\<Colon>\<surd>"
apply (unfold init_comp_ty_def)
apply (clarsimp simp add: accessible_in_RefT_simp 
                          is_acc_type_def is_acc_class_def)
done

lemma fvar_upd_no_jump: 
      assumes upd: "upd = snd (fst (fvar statDeclC stat fn a s'))"
        and noJmp: "abrupt s \<noteq> Some (Jump j)"
        shows "abrupt (upd val s) \<noteq> Some (Jump j)"
proof (cases "stat")
  case True
  with noJmp upd
  show ?thesis
    by (cases s) (simp add: fvar_def2)
next
  case False
  with noJmp upd
  show ?thesis
    by (cases s) (simp add: fvar_def2)
qed


lemma avar_state_no_jump: 
  assumes jmp: "abrupt (snd (avar G i a s)) = Some (Jump j)"
  shows "abrupt s = Some (Jump j)"
proof (cases "normal s")
  case True with jmp show ?thesis by (auto simp add: avar_def2 abrupt_if_def)
next
  case False with jmp show ?thesis by (auto simp add: avar_def2 abrupt_if_def)
qed

lemma avar_upd_no_jump: 
      assumes upd: "upd = snd (fst (avar G i a s'))"
        and noJmp: "abrupt s \<noteq> Some (Jump j)"
        shows "abrupt (upd val s) \<noteq> Some (Jump j)"
using upd noJmp
by (cases s) (simp add: avar_def2 abrupt_if_def)


text {* 
The next theorem expresses: If jumps (breaks, continues, returns) are nested
correctly, we won't find an unexpected jump in the result state of the 
evaluation. For exeample, a break can't leave its enclosing loop, an return
cant leave its enclosing method.
To proove this, the method call is critical. Allthough the
wellformedness of the whole program guarantees that the jumps (breaks,continues
and returns) are nested
correctly in all method bodies, the call rule alone does not guarantee that I
will call a method or even a class that is part of the program due to dynamic
binding! To be able to enshure this we need a kind of conformance of the
state, like in the typesafety proof. But then we will redo the typesafty
proof here. It would be nice if we could find an easy precondition that will
guarantee that all calls will actually call classes and methods of the current
program, which can be instantiated in the typesafty proof later on.
To fix this problem, I have instrumented the semantic definition of a call
to filter out any breaks in the state and to throw an error instead. 

To get an induction hypothesis which is strong enough to perform the
proof, we can't just 
assume @{term jumpNestingOk} for the empty set and conlcude, that no jump at 
all will be in the resulting state,  because the set is altered by 
the statements @{term Lab} and @{term While}. 

The wellformedness of the program is used to enshure that for all
classinitialisations and methods the nesting of jumps is wellformed, too.
*}  
theorem jumpNestingOk_eval:
  assumes eval: "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
     and jmpOk: "jumpNestingOk jmps t" 
     and wt: "Env\<turnstile>t\<Colon>T" 
     and wf: "wf_prog G"
     and  G: "prg Env = G"
     and no_jmp: "\<forall> j. abrupt s0 = Some (Jump j) \<longrightarrow> j \<in> jmps"
                    (is "?Jmp jmps s0")
  shows  "?Jmp jmps s1 \<and> 
                 (normal s1 \<longrightarrow>
                  (\<forall> w upd. v=In2 (w,upd)  
                   \<longrightarrow>   (\<forall> s j val. 
                          abrupt s \<noteq> Some (Jump j) \<longrightarrow>
                          abrupt (upd val s) \<noteq> Some (Jump j))))"
        (is "?Jmp jmps s1 \<and> ?Upd v s1")  
proof -
  let ?HypObj = "\<lambda> t s0 s1 v.
       (\<forall> jmps T Env. 
          ?Jmp jmps s0 \<longrightarrow> jumpNestingOk jmps t \<longrightarrow> Env\<turnstile>t\<Colon>T \<longrightarrow> prg Env=G\<longrightarrow>
          ?Jmp jmps s1 \<and> ?Upd v s1)"
  -- {* Variable @{text ?HypObj} is the following goal spelled in terms of
        the object logic, instead of the meta logic. It is needed in some
        cases of the induction were, the atomize-rulify process of induct 
        does not work fine, because the eval rules mix up object and meta
        logic. See for example the case for the loop. *} 
  from eval 
  have "\<And> jmps T Env. \<lbrakk>?Jmp jmps s0; jumpNestingOk jmps t; Env\<turnstile>t\<Colon>T;prg Env=G\<rbrakk>
            \<Longrightarrow> ?Jmp jmps s1 \<and> ?Upd v s1" 
        (is "PROP ?Hyp t s0 s1 v")
  -- {* We need to abstract over @{term jmps} since @{term jmps} are extended
        during analysis of @{term Lab}. Also we need to abstract over 
        @{term T} and @{term Env} since they are altered in various
        typing judgements. *}    
  proof (induct)   
    case Abrupt thus ?case by simp 
  next
    case Skip thus ?case by simp
  next
    case Expr thus ?case by (elim wt_elim_cases) simp
  next
    case (Lab c jmp s0 s1 jmps T Env) 
    have jmpOK: "jumpNestingOk jmps (In1r (jmp\<bullet> c))" .
    have G: "prg Env = G" .
    have wt_c: "Env\<turnstile>c\<Colon>\<surd>" 
      using Lab.prems by (elim wt_elim_cases)
    { 
      fix j
      assume ab_s1: "abrupt (abupd (absorb jmp) s1) = Some (Jump j)"
      have "j\<in>jmps"          
      proof -
        from ab_s1 have jmp_s1: "abrupt s1 = Some (Jump j)"
          by (cases s1) (simp add: absorb_def)
        have hyp_c: "PROP ?Hyp (In1r c) (Norm s0) s1 \<diamondsuit>" .
        from ab_s1 have "j \<noteq> jmp" 
          by (cases s1) (simp add: absorb_def)
        moreover have "j \<in> {jmp} \<union> jmps"
        proof -
          from jmpOK 
          have "jumpNestingOk ({jmp} \<union> jmps) (In1r c)" by simp
          with wt_c jmp_s1 G hyp_c
          show ?thesis
            by - (rule hyp_c [THEN conjunct1,rule_format],simp)
        qed
        ultimately show ?thesis
          by simp
      qed
    }
    thus ?case by simp
  next
    case (Comp c1 c2 s0 s1 s2 jmps T Env)
    have jmpOk: "jumpNestingOk jmps (In1r (c1;; c2))" .
    have G: "prg Env = G" .
    from Comp.prems obtain 
      wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and wt_c2: "Env\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases)
    {
      fix j
      assume abr_s2: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have jmp: "?Jmp jmps s1"
        proof -
          have hyp_c1: "PROP ?Hyp (In1r c1) (Norm s0) s1 \<diamondsuit>" .
          with wt_c1 jmpOk G 
          show ?thesis by simp
        qed
        moreover have hyp_c2: "PROP ?Hyp (In1r c2) s1 s2 (\<diamondsuit>::vals)" .
        have jmpOk': "jumpNestingOk jmps (In1r c2)" using jmpOk by simp
        moreover note wt_c2 G abr_s2
        ultimately show "j \<in> jmps"
          by (rule hyp_c2 [THEN conjunct1,rule_format (no_asm)])
      qed
    } thus ?case by simp
  next
    case (If b c1 c2 e s0 s1 s2 jmps T Env)
    have jmpOk: "jumpNestingOk jmps (In1r (If(e) c1 Else c2))" .
    have G: "prg Env = G" .
    from If.prems obtain 
              wt_e: "Env\<turnstile>e\<Colon>-PrimT Boolean" and 
      wt_then_else: "Env\<turnstile>(if the_Bool b then c1 else c2)\<Colon>\<surd>"
      by (elim wt_elim_cases) simp
    { 
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 b)" .
        with wt_e G have "?Jmp jmps s1" 
          by simp
        moreover have hyp_then_else: 
          "PROP ?Hyp (In1r (if the_Bool b then c1 else c2)) s1 s2 \<diamondsuit>" .
        have "jumpNestingOk jmps (In1r (if the_Bool b then c1 else c2))"
          using jmpOk by (cases "the_Bool b") simp_all
        moreover note wt_then_else G jmp
        ultimately show "j\<in> jmps" 
          by (rule hyp_then_else [THEN conjunct1,rule_format (no_asm)])
      qed
    }
    thus ?case by simp
  next
    case (Loop b c e l s0 s1 s2 s3 jmps T Env)
    have jmpOk: "jumpNestingOk jmps (In1r (l\<bullet> While(e) c))" .
    have G: "prg Env = G" .
    have wt: "Env\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" .
    then obtain 
              wt_e: "Env\<turnstile>e\<Colon>-PrimT Boolean" and 
              wt_c: "Env\<turnstile>c\<Colon>\<surd>"
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt s3 = Some (Jump j)" 
      have "j\<in>jmps"
      proof -
        have "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 b)" .
        with wt_e G have jmp_s1: "?Jmp jmps s1" 
          by simp
        show ?thesis
	proof (cases "the_Bool b")
          case False
          from Loop.hyps
          have "s3=s1"
            by (simp (no_asm_use) only: if_False False) 
          with jmp_s1 jmp have "j \<in> jmps" by simp
          thus ?thesis by simp
        next
          case True
          from Loop.hyps 
            (* Because of the mixture of object and pure logic in the rule 
               eval.If the atomization-rulification of the induct method 
               leaves the hypothesis in object logic *)
          have "?HypObj (In1r c) s1 s2 (\<diamondsuit>::vals)"
            apply (simp (no_asm_use) only: True if_True )
            apply (erule conjE)+
            apply assumption
            done
          note hyp_c = this [rule_format (no_asm)]
          moreover from jmpOk have "jumpNestingOk ({Cont l} \<union> jmps) (In1r c)"
            by simp
          moreover from jmp_s1 have "?Jmp ({Cont l} \<union> jmps) s1" by simp
          ultimately have jmp_s2: "?Jmp ({Cont l} \<union> jmps) s2" 
            using wt_c G by rules
          have "?Jmp jmps (abupd (absorb (Cont l)) s2)"
          proof -
            {
      	      fix j'
      	      assume abs: "abrupt (abupd (absorb (Cont l)) s2)=Some (Jump j')"
      	      have "j' \<in> jmps"
      	      proof (cases "j' = Cont l")
      		case True
      		with abs show ?thesis
      		  by (cases s2) (simp add: absorb_def)
      	      next
      		case False 
      		with abs have "abrupt s2 = Some (Jump j')"
      		  by (cases s2) (simp add: absorb_def) 
      		with jmp_s2 False show ?thesis
      		  by simp
      	      qed
            }
            thus ?thesis by simp
          qed
          moreover
          from Loop.hyps
          have "?HypObj (In1r (l\<bullet> While(e) c)) 
                        (abupd (absorb (Cont l)) s2) s3 (\<diamondsuit>::vals)"
            apply (simp (no_asm_use) only: True if_True)
            apply (erule conjE)+
            apply assumption
            done
          note hyp_w = this [rule_format (no_asm)]
          note jmpOk wt G jmp 
          ultimately show "j\<in> jmps" 
            by (rule hyp_w [THEN conjunct1,rule_format (no_asm)])
        qed
      qed
    }
    thus ?case by simp
  next
    case (Jmp j s jmps T Env) thus ?case by simp
  next
    case (Throw a e s0 s1 jmps T Env)
    have jmpOk: "jumpNestingOk jmps (In1r (Throw e))" .
    have G: "prg Env = G" .
    from Throw.prems obtain Te where 
      wt_e: "Env\<turnstile>e\<Colon>-Te" 
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt (abupd (throw a) s1) = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 a)" .
        hence "?Jmp jmps s1" using wt_e G by simp
        moreover
        from jmp 
        have "abrupt s1 = Some (Jump j)"
          by (cases s1) (simp add: throw_def abrupt_if_def)
        ultimately show "j \<in> jmps" by simp
      qed
    }
    thus ?case by simp
  next
    case (Try C c1 c2 s0 s1 s2 s3 vn jmps T Env)
    have jmpOk: "jumpNestingOk jmps (In1r (Try c1 Catch(C vn) c2))" .
    have G: "prg Env = G" .
    from Try.prems obtain 
      wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and  
      wt_c2: "Env\<lparr>lcl := lcl Env(VName vn\<mapsto>Class C)\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt s3 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have "PROP ?Hyp (In1r c1) (Norm s0) s1 (\<diamondsuit>::vals)" .
        with jmpOk wt_c1 G
        have jmp_s1: "?Jmp jmps s1" by simp
        have s2: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
        show "j \<in> jmps"
        proof (cases "G,s2\<turnstile>catch C")
          case False
          from Try.hyps have "s3=s2" 
	    by (simp (no_asm_use) only: False if_False)
          with jmp have "abrupt s1 = Some (Jump j)"
            using sxalloc_no_jump' [OF s2] by simp
          with jmp_s1 
          show ?thesis by simp
        next
          case True
          with Try.hyps 
          have "?HypObj (In1r c2) (new_xcpt_var vn s2) s3 (\<diamondsuit>::vals)"
            apply (simp (no_asm_use) only: True if_True simp_thms)
            apply (erule conjE)+
            apply assumption
            done
          note hyp_c2 = this [rule_format (no_asm)]
          from jmp_s1 sxalloc_no_jump' [OF s2] 
          have "?Jmp jmps s2"
            by simp
          hence "?Jmp jmps (new_xcpt_var vn s2)"
            by (cases s2) simp
          moreover have "jumpNestingOk jmps (In1r c2)" using jmpOk by simp
          moreover note wt_c2
          moreover from G 
          have "prg (Env\<lparr>lcl := lcl Env(VName vn\<mapsto>Class C)\<rparr>) = G"
            by simp
          moreover note jmp
          ultimately show ?thesis 
            by (rule hyp_c2 [THEN conjunct1,rule_format (no_asm)])
        qed
      qed
    }
    thus ?case by simp
  next
    case (Fin c1 c2 s0 s1 s2 s3 x1 jmps T Env)
    have jmpOk: " jumpNestingOk jmps (In1r (c1 Finally c2))" .
    have G: "prg Env = G" .
    from Fin.prems obtain 
      wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and wt_c2: "Env\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt s3 = Some (Jump j)" 
      have "j \<in> jmps"
      proof (cases "x1=Some (Jump j)")
        case True
        have hyp_c1: "PROP ?Hyp (In1r c1) (Norm s0) (x1,s1) \<diamondsuit>" .
        with True jmpOk wt_c1 G show ?thesis 
          by - (rule hyp_c1 [THEN conjunct1,rule_format (no_asm)],simp_all)
      next
        case False
        have hyp_c2:  "PROP ?Hyp (In1r c2) (Norm s1) s2 \<diamondsuit>" .
        have "s3 = (if \<exists>err. x1 = Some (Error err) then (x1, s1)
                             else abupd (abrupt_if (x1 \<noteq> None) x1) s2)" .
        with False jmp have "abrupt s2 = Some (Jump j)"
          by (cases s2, simp add: abrupt_if_def)
        with jmpOk wt_c2 G show ?thesis 
          by - (rule hyp_c2 [THEN conjunct1,rule_format (no_asm)],simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Init C c s0 s1 s2 s3 jmps T Env)
    have "jumpNestingOk jmps (In1r (Init C))".
    have G: "prg Env = G" .
    have "the (class G C) = c" .
    with Init.prems have c: "class G C = Some c"
      by (elim wt_elim_cases) auto
    {
      fix j
      assume jmp: "abrupt s3 = (Some (Jump j))" 
      have "j\<in>jmps"
      proof (cases "inited C (globs s0)") 
        case True
        with Init.hyps have "s3=Norm s0"
          by simp
        with jmp
        have "False" by simp thus ?thesis ..
      next
        case False
        from wf c G
        have wf_cdecl: "wf_cdecl G (C,c)"
          by (simp add: wf_prog_cdecl)
        from Init.hyps
        have "?HypObj (In1r (if C = Object then Skip else Init (super c))) 
                            (Norm ((init_class_obj G C) s0)) s1 (\<diamondsuit>::vals)"
          apply (simp (no_asm_use) only: False if_False simp_thms)
          apply (erule conjE)+
          apply assumption
          done
        note hyp_s1 = this [rule_format (no_asm)]
        from wf_cdecl G have
          wt_super: "Env\<turnstile>(if C = Object then Skip else Init (super c))\<Colon>\<surd>"
          by (cases "C=Object")
             (auto dest: wf_cdecl_supD is_acc_classD) 
        from hyp_s1 [OF _ _ wt_super G]
        have "?Jmp jmps s1" 
          by simp
        hence jmp_s1: "?Jmp jmps ((set_lvars empty) s1)" by (cases s1) simp
        from False Init.hyps
        have "?HypObj (In1r (init c)) ((set_lvars empty) s1) s2 (\<diamondsuit>::vals)" 
          apply (simp (no_asm_use) only: False if_False simp_thms)
          apply (erule conjE)+
          apply assumption
          done
        note hyp_init_c = this [rule_format (no_asm)] 
        from wf_cdecl 
        have wt_init_c: "\<lparr>prg = G, cls = C, lcl = empty\<rparr>\<turnstile>init c\<Colon>\<surd>"
          by (rule wf_cdecl_wt_init)
        from wf_cdecl have "jumpNestingOkS {} (init c)" 
          by (cases rule: wf_cdeclE)
        hence "jumpNestingOkS jmps (init c)"
          by (rule jumpNestingOkS_mono) simp
        moreover 
        have "abrupt s2 = Some (Jump j)"
        proof -
          from False Init.hyps 
          have "s3 = (set_lvars (locals (store s1))) s2"  by simp
          with jmp show ?thesis by (cases s2) simp
        qed
        ultimately show ?thesis
          using hyp_init_c [OF jmp_s1 _ wt_init_c]
          by simp
      qed
    }
    thus ?case by simp
  next
    case (NewC C a s0 s1 s2 jmps T Env)
    {
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof - 
        have "prg Env = G" .
        moreover have hyp_init: "PROP ?Hyp (In1r (Init C)) (Norm s0) s1 \<diamondsuit>" .
        moreover from wf NewC.prems 
        have "Env\<turnstile>(Init C)\<Colon>\<surd>"
          by (elim wt_elim_cases) (drule is_acc_classD,simp)
        moreover 
        have "abrupt s1 = Some (Jump j)"
        proof -
          have "G\<turnstile>s1 \<midarrow>halloc CInst C\<succ>a\<rightarrow> s2" .
          from this jmp show ?thesis
            by (rule halloc_no_jump')
        qed
        ultimately show "j \<in> jmps" 
          by - (rule hyp_init [THEN conjunct1,rule_format (no_asm)],auto)
      qed
    }
    thus ?case by simp
  next
    case (NewA elT a e i s0 s1 s2 s3 jmps T Env)
    {
      fix j
      assume jmp: "abrupt s3 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have G: "prg Env = G" .
        from NewA.prems 
        obtain wt_init: "Env\<turnstile>init_comp_ty elT\<Colon>\<surd>" and 
               wt_size: "Env\<turnstile>e\<Colon>-PrimT Integer"
          by (elim wt_elim_cases) (auto dest:  wt_init_comp_ty')
        have "PROP ?Hyp (In1r (init_comp_ty elT)) (Norm s0) s1 \<diamondsuit>" .
        with wt_init G 
        have "?Jmp jmps s1" 
          by (simp add: init_comp_ty_def)
        moreover
        have hyp_e: "PROP ?Hyp (In1l e) s1 s2 (In1 i)" .
        have "abrupt s2 = Some (Jump j)"
        proof -
          have "G\<turnstile>abupd (check_neg i) s2\<midarrow>halloc Arr elT (the_Intg i)\<succ>a\<rightarrow> s3".
          moreover note jmp
          ultimately 
          have "abrupt (abupd (check_neg i) s2) = Some (Jump j)"
            by (rule halloc_no_jump')
          thus ?thesis by (cases s2) auto
        qed
        ultimately show "j\<in>jmps" using wt_size G 
          by - (rule hyp_e [THEN conjunct1,rule_format (no_asm)],simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Cast cT e s0 s1 s2 v jmps T Env)
    {
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e: "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 v)" .
        have "prg Env = G" .
        moreover from Cast.prems
        obtain eT where "Env\<turnstile>e\<Colon>-eT" by (elim wt_elim_cases)
        moreover 
        have "abrupt s1 = Some (Jump j)"
        proof -
          have "s2 = abupd (raise_if (\<not> G,snd s1\<turnstile>v fits cT) ClassCast) s1" .
          moreover note jmp
          ultimately show ?thesis by (cases s1) (simp add: abrupt_if_def)
        qed
        ultimately show ?thesis 
          by - (rule hyp_e [THEN conjunct1,rule_format (no_asm)], simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Inst eT b e s0 s1 v jmps T Env)
    {
      fix j
      assume jmp: "abrupt s1 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e: "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 v)" .
        have "prg Env = G" .
        moreover from Inst.prems
        obtain eT where "Env\<turnstile>e\<Colon>-eT" by (elim wt_elim_cases)
        moreover note jmp
        ultimately show "j\<in>jmps" 
          by - (rule hyp_e [THEN conjunct1,rule_format (no_asm)], simp_all)
      qed
    }
    thus ?case by simp
  next
    case Lit thus ?case by simp
  next
    case (UnOp e s0 s1 unop v jmps T Env)
    {
      fix j
      assume jmp: "abrupt s1 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e: "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 v)" .
        have "prg Env = G" .
        moreover from UnOp.prems
        obtain eT where "Env\<turnstile>e\<Colon>-eT" by (elim wt_elim_cases)
        moreover note jmp
        ultimately show  "j\<in>jmps" 
          by - (rule hyp_e [THEN conjunct1,rule_format (no_asm)], simp_all) 
      qed
    }
    thus ?case by simp
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2 jmps T Env)
    {
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have G: "prg Env = G" .
        from BinOp.prems
        obtain e1T e2T where 
          wt_e1: "Env\<turnstile>e1\<Colon>-e1T" and
          wt_e2: "Env\<turnstile>e2\<Colon>-e2T" 
          by (elim wt_elim_cases)
        have "PROP ?Hyp (In1l e1) (Norm s0) s1 (In1 v1)" .
        with G wt_e1 have jmp_s1: "?Jmp jmps s1" by simp
        have hyp_e2: 
          "PROP ?Hyp (if need_second_arg binop v1 then In1l e2 else In1r Skip)
                     s1 s2 (In1 v2)" .
        show "j\<in>jmps"
        proof (cases "need_second_arg binop v1")
          case True with jmp_s1 wt_e2 jmp G
          show ?thesis 
            by - (rule hyp_e2 [THEN conjunct1,rule_format (no_asm)],simp_all)
        next
          case False with jmp_s1 jmp G
          show ?thesis 
            by - (rule hyp_e2 [THEN conjunct1,rule_format (no_asm)],auto)
        qed
      qed
    }
    thus ?case by simp
  next
    case Super thus ?case by simp
  next
    case (Acc f s0 s1 v va jmps T Env)
    {
      fix j
      assume jmp: "abrupt s1 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_va: "PROP ?Hyp (In2 va) (Norm s0) s1 (In2 (v,f))" .
        have "prg Env = G" .
        moreover from Acc.prems
        obtain vT where "Env\<turnstile>va\<Colon>=vT" by (elim wt_elim_cases)
        moreover note jmp
        ultimately show "j\<in>jmps" 
          by - (rule hyp_va [THEN conjunct1,rule_format (no_asm)], simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Ass e f s0 s1 s2 v va w jmps T Env)
    have G: "prg Env = G" .
    from Ass.prems
    obtain vT eT where
      wt_va: "Env\<turnstile>va\<Colon>=vT" and
       wt_e: "Env\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases)
    have hyp_v: "PROP ?Hyp (In2 va) (Norm s0) s1 (In2 (w,f))" .
    have hyp_e: "PROP ?Hyp (In1l e) s1 s2 (In1 v)" . 
    {
      fix j
      assume jmp: "abrupt (assign f v s2) = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have "abrupt s2 = Some (Jump j)"
        proof (cases "normal s2")
          case True
          have "G\<turnstile>s1 \<midarrow>e-\<succ>v\<rightarrow> s2" .
          from this True have nrm_s1: "normal s1" 
            by (rule eval_no_abrupt_lemma [rule_format]) 
          with nrm_s1 wt_va G True
          have "abrupt (f v s2) \<noteq> Some (Jump j)"
            using hyp_v [THEN conjunct2,rule_format (no_asm)]
            by simp
          from this jmp
          show ?thesis
            by (rule assign_abrupt_propagation)
        next
          case False with jmp 
          show ?thesis by (cases s2) (simp add: assign_def Let_def)
        qed
        moreover from wt_va G
        have "?Jmp jmps s1"
          by - (rule hyp_v [THEN conjunct1],simp_all)
        ultimately show ?thesis using G 
          by - (rule hyp_e [THEN conjunct1,rule_format (no_asm)],simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Cond b e0 e1 e2 s0 s1 s2 v jmps T Env)
    have G: "prg Env = G" .
    have hyp_e0: "PROP ?Hyp (In1l e0) (Norm s0) s1 (In1 b)" .
    have hyp_e1_e2: "PROP ?Hyp (In1l (if the_Bool b then e1 else e2)) 
                               s1 s2 (In1 v)" .
    from Cond.prems
    obtain e1T e2T
      where wt_e0: "Env\<turnstile>e0\<Colon>-PrimT Boolean"
       and  wt_e1: "Env\<turnstile>e1\<Colon>-e1T"
       and  wt_e2: "Env\<turnstile>e2\<Colon>-e2T"
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps" 
      proof -
        from wt_e0 G 
        have jmp_s1: "?Jmp jmps s1"
          by - (rule hyp_e0 [THEN conjunct1],simp_all)
        show ?thesis
        proof (cases "the_Bool b")
          case True
          with jmp_s1 wt_e1 G jmp
          show ?thesis
            by-(rule hyp_e1_e2 [THEN conjunct1,rule_format (no_asm)],simp_all)
        next
          case False
          with jmp_s1 wt_e2 G jmp
          show ?thesis
            by-(rule hyp_e1_e2 [THEN conjunct1,rule_format (no_asm)],simp_all)
        qed
      qed
    }
    thus ?case by simp
  next
    case (Call D a accC args e mn mode pTs s0 s1 s2 s3 s3' s4 statT v vs 
               jmps T Env)
    have G: "prg Env = G" .
    from Call.prems
    obtain eT argsT 
      where wt_e: "Env\<turnstile>e\<Colon>-eT" and wt_args: "Env\<turnstile>args\<Colon>\<doteq>argsT"
      by (elim wt_elim_cases)
    {
      fix j
      assume jmp: "abrupt ((set_lvars (locals (store s2))) s4) 
                     = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e: "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 a)" .
        from wt_e G 
        have jmp_s1: "?Jmp jmps s1"
          by - (rule hyp_e [THEN conjunct1],simp_all)
        have hyp_args: "PROP ?Hyp (In3 args) s1 s2 (In3 vs)" .
        have "abrupt s2 = Some (Jump j)"
        proof -
          have "G\<turnstile>s3' \<midarrow>Methd D \<lparr>name = mn, parTs = pTs\<rparr>-\<succ>v\<rightarrow> s4" .
          moreover
          from jmp have "abrupt s4 = Some (Jump j)"
            by (cases s4) simp
          ultimately have "abrupt s3' = Some (Jump j)"
            by - (rule ccontr,drule (1) Methd_no_jump,simp)
          moreover have "s3' = check_method_access G accC statT mode 
                              \<lparr>name = mn, parTs = pTs\<rparr> a s3" .
          ultimately have "abrupt s3 = Some (Jump j)"
            by (cases s3) 
               (simp add: check_method_access_def abrupt_if_def Let_def)
          moreover 
          have "s3 = init_lvars G D \<lparr>name=mn, parTs=pTs\<rparr> mode a vs s2" .
          ultimately show ?thesis
            by (cases s2) (auto simp add: init_lvars_def2)
        qed
        with jmp_s1 wt_args G
        show ?thesis
          by - (rule hyp_args [THEN conjunct1,rule_format (no_asm)], simp_all)
      qed
    }
    thus ?case by simp
  next
    case (Methd D s0 s1 sig v jmps T Env)
    have "G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<rightarrow> s1"
      by (rule eval.Methd)
    hence "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
      by (rule Methd_no_jump) simp
    thus ?case by simp
  next
    case (Body D c s0 s1 s2 s3 jmps T Env)
    have "G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)
           \<rightarrow> abupd (absorb Ret) s3"
      by (rule eval.Body)
    hence "\<And> j. abrupt (abupd (absorb Ret) s3) \<noteq> Some (Jump j)"
      by (rule Body_no_jump) simp
    thus ?case by simp
  next
    case LVar
    thus ?case by (simp add: lvar_def Let_def)
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v jmps T Env)
    have G: "prg Env = G" .
    from wf FVar.prems 
    obtain  statC f where
      wt_e: "Env\<turnstile>e\<Colon>-Class statC" and
      accfield: "accfield (prg Env) accC statC fn = Some (statDeclC,f)"
      by  (elim wt_elim_cases) simp
    have wt_init: "Env\<turnstile>Init statDeclC\<Colon>\<surd>"
    proof -
      from wf wt_e G 
      have "is_class (prg Env) statC"
        by (auto dest: ty_expr_is_type type_is_class)
      with wf accfield G
      have "is_class (prg Env) statDeclC"
        by (auto dest!: accfield_fields dest: fields_declC)
      thus ?thesis
        by simp
    qed
    have fvar: "(v, s2') = fvar statDeclC stat fn a s2" .
    {
      fix j
      assume jmp: "abrupt s3 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_init: "PROP ?Hyp (In1r (Init statDeclC)) (Norm s0) s1 \<diamondsuit>" .
        from G wt_init 
        have "?Jmp jmps s1"
          by - (rule hyp_init [THEN conjunct1],auto)
        moreover
        have hyp_e: "PROP ?Hyp (In1l e) s1 s2 (In1 a)" .
        have "abrupt s2 = Some (Jump j)"
        proof -
          have "s3 = check_field_access G accC statDeclC fn stat a s2'" .
          with jmp have "abrupt s2' = Some (Jump j)"
            by (cases s2') 
               (simp add: check_field_access_def abrupt_if_def Let_def)
         with fvar show "abrupt s2 =  Some (Jump j)"
            by (cases s2) (simp add: fvar_def2 abrupt_if_def)
        qed
        ultimately show ?thesis
          using G wt_e
          by - (rule hyp_e [THEN conjunct1, rule_format (no_asm)],simp_all)
      qed
    }
    moreover
    from fvar obtain upd w
      where upd: "upd = snd (fst (fvar statDeclC stat fn a s2))" and
              v: "v=(w,upd)"
      by (cases "fvar statDeclC stat fn a s2") simp
    {
      fix j val fix s::state
      assume "normal s3"
      assume no_jmp: "abrupt s \<noteq> Some (Jump j)"
      with upd
      have "abrupt (upd val s) \<noteq> Some (Jump j)"
        by (rule fvar_upd_no_jump)
    }
    ultimately show ?case using v by simp
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v jmps T Env)
    have G: "prg Env = G" .
    from AVar.prems 
    obtain  e1T e2T where
      wt_e1: "Env\<turnstile>e1\<Colon>-e1T" and wt_e2: "Env\<turnstile>e2\<Colon>-e2T"
      by  (elim wt_elim_cases) simp
    have avar: "(v, s2') = avar G i a s2" .
    {
      fix j
      assume jmp: "abrupt s2' = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e1: "PROP ?Hyp (In1l e1) (Norm s0) s1 (In1 a)" .
        from G wt_e1
        have "?Jmp jmps s1"
          by - (rule hyp_e1 [THEN conjunct1],auto)
        moreover
        have hyp_e2: "PROP ?Hyp (In1l e2) s1 s2 (In1 i)" .
        have "abrupt s2 = Some (Jump j)"
        proof -
          from avar have "s2' = snd (avar G i a s2)"
            by (cases "avar G i a s2") simp
          with jmp show ?thesis by - (rule avar_state_no_jump,simp) 
        qed  
        ultimately show ?thesis
          using wt_e2 G
          by - (rule hyp_e2 [THEN conjunct1, rule_format (no_asm)],simp_all)
      qed
    }
    moreover
    from avar obtain upd w
      where upd: "upd = snd (fst (avar G i a s2))" and
              v: "v=(w,upd)"
      by (cases "avar G i a s2") simp
    {
      fix j val fix s::state
      assume "normal s2'"
      assume no_jmp: "abrupt s \<noteq> Some (Jump j)"
      with upd
      have "abrupt (upd val s) \<noteq> Some (Jump j)"
        by (rule avar_upd_no_jump)
    }
    ultimately show ?case using v by simp
  next
    case Nil thus ?case by simp
  next
    case (Cons e es s0 s1 s2 v vs jmps T Env)
    have G: "prg Env = G" .
    from Cons.prems obtain eT esT
      where wt_e: "Env\<turnstile>e\<Colon>-eT" and wt_e2: "Env\<turnstile>es\<Colon>\<doteq>esT"
      by  (elim wt_elim_cases) simp
    {
      fix j
      assume jmp: "abrupt s2 = Some (Jump j)"
      have "j\<in>jmps"
      proof -
        have hyp_e: "PROP ?Hyp (In1l e) (Norm s0) s1 (In1 v)" .
        from G wt_e
        have "?Jmp jmps s1"
          by - (rule hyp_e [THEN conjunct1],simp_all)
        moreover
        have hyp_es: "PROP ?Hyp (In3 es) s1 s2 (In3 vs)" .  
        ultimately show ?thesis
          using wt_e2 G jmp
          by - (rule hyp_es [THEN conjunct1, rule_format (no_asm)],
                (assumption|simp (no_asm_simp))+)
      qed
    }
    thus ?case by simp
  qed
  note generalized = this
  from no_jmp jmpOk wt G
  show ?thesis
    by (rule generalized)
qed

lemmas jumpNestingOk_evalE = jumpNestingOk_eval [THEN conjE,rule_format]


lemma jumpNestingOk_eval_no_jump:
 assumes    eval: "prg Env\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
           jmpOk: "jumpNestingOk {} t" and
          no_jmp: "abrupt s0 \<noteq> Some (Jump j)" and
              wt: "Env\<turnstile>t\<Colon>T" and 
              wf: "wf_prog (prg Env)" 
 shows "abrupt s1 \<noteq> Some (Jump j) \<and>
        (normal s1 \<longrightarrow> v=In2 (w,upd)  
         \<longrightarrow> abrupt s \<noteq> Some (Jump j')
         \<longrightarrow> abrupt (upd val s) \<noteq> Some (Jump j'))"
proof (cases "\<exists> j'. abrupt s0 = Some (Jump j')") 
  case True
  then obtain j' where jmp: "abrupt s0 = Some (Jump j')" ..
  with no_jmp have "j'\<noteq>j" by simp
  with eval jmp have "s1=s0" by auto
  with no_jmp jmp show ?thesis by simp
next
  case False
  obtain G where G: "prg Env = G"
    by (cases Env) simp
  from G eval have "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" by simp
  moreover note jmpOk wt
  moreover from G wf have "wf_prog G" by simp
  moreover note G 
  moreover from False have "\<And> j. abrupt s0 = Some (Jump j) \<Longrightarrow> j \<in> {}"
    by simp
  ultimately show ?thesis
    apply (rule jumpNestingOk_evalE)
    apply assumption
    apply simp
    apply fastsimp
    done
qed

lemmas jumpNestingOk_eval_no_jumpE 
       = jumpNestingOk_eval_no_jump [THEN conjE,rule_format]

corollary eval_expression_no_jump:
  assumes eval: "prg Env\<turnstile>s0 \<midarrow>e-\<succ>v\<rightarrow> s1" and
        no_jmp: "abrupt s0 \<noteq> Some (Jump j)" and
        wt: "Env\<turnstile>e\<Colon>-T" and 
        wf: "wf_prog (prg Env)" 
  shows "abrupt s1 \<noteq> Some (Jump j)"
using eval _ no_jmp wt wf
by (rule jumpNestingOk_eval_no_jumpE, simp_all)

corollary eval_var_no_jump:
  assumes eval: "prg Env\<turnstile>s0 \<midarrow>var=\<succ>(w,upd)\<rightarrow> s1" and
        no_jmp: "abrupt s0 \<noteq> Some (Jump j)" and
        wt: "Env\<turnstile>var\<Colon>=T" and 
        wf: "wf_prog (prg Env)" 
  shows "abrupt s1 \<noteq> Some (Jump j) \<and> 
         (normal s1 \<longrightarrow> 
          (abrupt s \<noteq> Some (Jump j') 
           \<longrightarrow> abrupt (upd val s) \<noteq> Some (Jump j')))"
apply (rule_tac upd="upd" and val="val" and s="s" and w="w" and j'=j' 
         in jumpNestingOk_eval_no_jumpE [OF eval _ no_jmp wt wf])
by simp_all

lemmas eval_var_no_jumpE = eval_var_no_jump [THEN conjE,rule_format]

corollary eval_statement_no_jump:
  assumes eval: "prg Env\<turnstile>s0 \<midarrow>c\<rightarrow> s1" and
         jmpOk: "jumpNestingOkS {} c" and
        no_jmp: "abrupt s0 \<noteq> Some (Jump j)" and
        wt: "Env\<turnstile>c\<Colon>\<surd>" and 
        wf: "wf_prog (prg Env)" 
  shows "abrupt s1 \<noteq> Some (Jump j)"
using eval _ no_jmp wt wf
by (rule jumpNestingOk_eval_no_jumpE) (simp_all add: jmpOk)

corollary eval_expression_list_no_jump:
  assumes eval: "prg Env\<turnstile>s0 \<midarrow>es\<doteq>\<succ>v\<rightarrow> s1" and
        no_jmp: "abrupt s0 \<noteq> Some (Jump j)" and
        wt: "Env\<turnstile>es\<Colon>\<doteq>T" and 
        wf: "wf_prog (prg Env)" 
  shows "abrupt s1 \<noteq> Some (Jump j)"
using eval _ no_jmp wt wf
by (rule jumpNestingOk_eval_no_jumpE, simp_all)

(* ### FIXME: Do i need this *)
lemma union_subseteq_elim [elim]: "\<lbrakk>A \<union> B \<subseteq> C; \<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by blast

lemma dom_locals_halloc_mono:
  assumes halloc: "G\<turnstile>s0\<midarrow>halloc oi\<succ>a\<rightarrow>s1"
  shows "dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
proof -
  from halloc show ?thesis
    by cases simp_all
qed
 
lemma dom_locals_sxalloc_mono:
  assumes sxalloc: "G\<turnstile>s0\<midarrow>sxalloc\<rightarrow>s1"
  shows "dom (locals (store s0)) \<subseteq> dom (locals (store s1))"
proof -
  from sxalloc show ?thesis
  proof (cases)
    case Norm thus ?thesis by simp
  next
    case Jmp thus ?thesis by simp
  next
    case Error thus ?thesis by simp
  next
    case XcptL thus ?thesis by simp
  next
    case SXcpt thus ?thesis 
      by - (drule dom_locals_halloc_mono,simp)
  qed
qed
    

lemma dom_locals_assign_mono: 
 assumes f_ok: "dom (locals (store s)) \<subseteq> dom (locals (store (f n s)))"
   shows  "dom (locals (store s)) \<subseteq> dom (locals (store (assign f n s)))"
proof (cases "normal s")
  case False thus ?thesis
    by (cases s) (auto simp add: assign_def Let_def)
next
  case True
  then obtain s' where s': "s = (None,s')"
    by auto
  moreover
  obtain x1 s1 where "f n s = (x1,s1)"
    by (cases "f n s", simp)
  ultimately
  show ?thesis
    using f_ok
    by (simp add: assign_def Let_def)
qed

(*
lemma dom_locals_init_lvars_mono: 
 "dom (locals (store s)) 
   \<subseteq> dom (locals (store (init_lvars G D sig mode a vs s)))"
proof (cases "mode = Static")
  case True
  thus ?thesis
    apply (cases s)
    apply (simp add: init_lvars_def Let_def)
*)

lemma dom_locals_lvar_mono:
 "dom (locals (store s)) \<subseteq> dom (locals (store (snd (lvar vn s') val s)))"
by (simp add: lvar_def) blast


lemma dom_locals_fvar_vvar_mono:
"dom (locals (store s)) 
  \<subseteq> dom (locals (store (snd (fst (fvar statDeclC stat fn a s')) val s)))"
proof (cases stat) 
  case True
  thus ?thesis
    by (cases s) (simp add: fvar_def2)
next
  case False
  thus ?thesis
    by (cases s) (simp add: fvar_def2)
qed

lemma dom_locals_fvar_mono:
"dom (locals (store s)) 
  \<subseteq> dom (locals (store (snd (fvar statDeclC stat fn a s))))"
proof (cases stat) 
  case True
  thus ?thesis
    by (cases s) (simp add: fvar_def2)
next
  case False
  thus ?thesis
    by (cases s) (simp add: fvar_def2)
qed


lemma dom_locals_avar_vvar_mono:
"dom (locals (store s)) 
  \<subseteq> dom (locals (store (snd (fst (avar G i a s')) val s)))"
by (cases s, simp add: avar_def2)

lemma dom_locals_avar_mono:
"dom (locals (store s)) 
  \<subseteq> dom (locals (store (snd (avar G i a s))))"
by (cases s, simp add: avar_def2)

  text {* 
Since assignments are modelled as functions from states to states, we
  must take into account these functions. They  appear only in the assignment 
  rule and as result from evaluating a variable. Thats why we need the 
  complicated second part of the conjunction in the goal.
 The reason for the very generic way to treat assignments was the aim
to omit redundancy. There is only one evaluation rule for each kind of
variable (locals, fields, arrays). These rules are used for both accessing 
variables and updating variables. Thats why the evaluation rules for variables
result in a pair consisting of a value and an update function. Of course we
could also think of a pair of a value and a reference in the store, instead of
the generic update function. But as only array updates can cause a special
exception (if the types mismatch) and not array reads we then have to introduce
two different rules to handle array reads and updates *} 
lemma dom_locals_eval_mono: 
  assumes   eval: "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" 
  shows "dom (locals (store s0)) \<subseteq> dom (locals (store s1)) \<and>
         (\<forall> vv. v=In2 vv \<and> normal s1 
            \<longrightarrow> (\<forall> s val. dom (locals (store s)) 
                           \<subseteq> dom (locals (store ((snd vv) val s)))))"
proof -
  from eval show ?thesis
  proof (induct)
    case Abrupt thus ?case by simp 
  next
    case Skip thus ?case by simp
  next
    case Expr thus ?case by simp
  next
    case Lab thus ?case by simp
  next
    case (Comp c1 c2 s0 s1 s2) 
    from Comp.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Comp.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    finally show ?case by simp
  next
    case (If b c1 c2 e s0 s1 s2)
    from If.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from If.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    finally show ?case by simp
  next
    case (Loop b c e l s0 s1 s2 s3) 
    show ?case
    proof (cases "the_Bool b")
      case True
      with Loop.hyps
      obtain
	s0_s1: 
	"dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))" and
	s1_s2: "dom (locals (store s1)) \<subseteq> dom (locals (store s2))" and
	s2_s3: "dom (locals (store s2)) \<subseteq> dom (locals (store s3))"
	by simp
      note s0_s1 also note s1_s2 also note s2_s3
      finally show ?thesis
	by simp
    next
      case False
      with Loop.hyps show ?thesis
	by simp
    qed
  next
    case Jmp thus ?case by simp
  next
    case Throw thus ?case by simp
  next
    case (Try C c1 c2 s0 s1 s2 s3 vn)
    then
    have s0_s1: "dom (locals (store ((Norm s0)::state))) 
                  \<subseteq> dom (locals (store s1))" by simp
    have "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
    hence s1_s2: "dom (locals (store s1)) \<subseteq> dom (locals (store s2))" 
      by (rule dom_locals_sxalloc_mono)
    thus ?case 
    proof (cases "G,s2\<turnstile>catch C")
      case True
      note s0_s1 also note s1_s2
      also
      from True Try.hyps 
      have "dom (locals (store (new_xcpt_var vn s2))) 
              \<subseteq> dom (locals (store s3))"
	by simp
      hence "dom (locals (store s2)) \<subseteq> dom (locals (store s3))"
	by (cases s2, simp )
      finally show ?thesis by simp
    next
      case False
      note s0_s1 also note s1_s2
      finally 
      show ?thesis 
	using False Try.hyps by simp
    qed
  next
    case (Fin c1 c2 s0 s1 s2 s3 x1) 
    show ?case
    proof (cases "\<exists>err. x1 = Some (Error err)")
      case True
      with Fin.hyps show ?thesis
	by simp
    next
      case False
      from Fin.hyps
      have "dom (locals (store ((Norm s0)::state))) 
             \<subseteq> dom (locals (store (x1, s1)))" 
	by simp
      hence "dom (locals (store ((Norm s0)::state))) 
              \<subseteq> dom (locals (store ((Norm s1)::state)))"
	by simp
      also
      from Fin.hyps
      have "\<dots> \<subseteq> dom (locals (store s2))"
	by simp
      finally show ?thesis 
	using Fin.hyps by simp
    qed
  next
    case (Init C c s0 s1 s2 s3)
    show ?case
    proof (cases "inited C (globs s0)")
      case True
      with Init.hyps show ?thesis by simp 
    next
      case False
      with Init.hyps 
      obtain s0_s1: "dom (locals (store (Norm ((init_class_obj G C) s0))))
                     \<subseteq> dom (locals (store s1))" and
	     s3: "s3 = (set_lvars (locals (snd s1))) s2"
	by simp
      from s0_s1
      have "dom (locals (store (Norm s0))) \<subseteq> dom (locals (store s1))"
	by (cases s0) simp
      with s3
      have "dom (locals (store (Norm s0))) \<subseteq> dom (locals (store s3))"
	by (cases s2) simp
      thus ?thesis by simp
    qed
  next
    case (NewC C a s0 s1 s2)
    have halloc: "G\<turnstile>s1 \<midarrow>halloc CInst C\<succ>a\<rightarrow> s2" .
    from NewC.hyps
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))" 
      by simp
    also
    from halloc
    have "\<dots>  \<subseteq> dom (locals (store s2))" by (rule dom_locals_halloc_mono)
    finally show ?case by simp
  next
    case (NewA T a e i s0 s1 s2 s3)
    have halloc: "G\<turnstile>abupd (check_neg i) s2 \<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" .
    from NewA.hyps
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))" 
      by simp
    also
    from NewA.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" by simp
    also
    from halloc 
    have "\<dots> \<subseteq>  dom (locals (store s3))"
      by (rule dom_locals_halloc_mono [elim_format]) simp
    finally show ?case by simp
  next
    case Cast thus ?case by simp
  next
    case Inst thus ?case by simp
  next
    case Lit thus ?case by simp
  next
    case UnOp thus ?case by simp
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2) 
    from BinOp.hyps
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))" 
      by simp
    also
    from BinOp.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" by simp
    finally show ?case by simp
  next
    case Super thus ?case by simp
  next
    case Acc thus ?case by simp
  next
    case (Ass e f s0 s1 s2 v va w)
    from Ass.hyps
    have s0_s1: 
      "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))" 
      by simp
    show ?case
    proof (cases "normal s1")
      case True
      with Ass.hyps 
      have ass_ok:
        "\<And> s val. dom (locals (store s)) \<subseteq> dom (locals (store (f val s)))"
	by simp
      note s0_s1
      also
      from Ass.hyps
      have "dom (locals (store s1)) \<subseteq> dom (locals (store s2))" 
	by simp
      also
      from ass_ok
      have "\<dots> \<subseteq> dom (locals (store (assign f v s2)))"
	by (rule dom_locals_assign_mono)
      finally show ?thesis by simp
    next
      case False
      have "G\<turnstile>s1 \<midarrow>e-\<succ>v\<rightarrow> s2" .
      with False 
      have "s2=s1"
	by auto
      with s0_s1 False
      have "dom (locals (store ((Norm s0)::state))) 
            \<subseteq> dom (locals (store (assign f v s2)))"
	by simp
      thus ?thesis
	by simp
    qed
  next
    case (Cond b e0 e1 e2 s0 s1 s2 v)
    from Cond.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Cond.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    finally show ?case by simp
  next
    case (Call D a' accC args e mn mode pTs s0 s1 s2 s3 s3' s4 statT v vs)
    have s3: "s3 = init_lvars G D \<lparr>name = mn, parTs = pTs\<rparr> mode a' vs s2" .
    from Call.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Call.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    also
    have "\<dots> \<subseteq> dom (locals (store ((set_lvars (locals (store s2))) s4)))"
      by (cases s4) simp
    finally show ?case by simp
  next
    case Methd thus ?case by simp
  next
    case (Body D c s0 s1 s2 s3)
    from Body.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Body.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    also
    have "\<dots> \<subseteq> dom (locals (store (abupd (absorb Ret) s2)))"
      by simp
    also
    have "\<dots> \<subseteq> dom (locals (store (abupd (absorb Ret) s3)))"
    proof -
       have "s3 =
         (if \<exists>l. abrupt s2 = Some (Jump (Break l)) \<or> 
                 abrupt s2 = Some (Jump (Cont l))
             then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 else s2)".
      thus ?thesis
	by simp
    qed
    finally show ?case by simp
  next
    case LVar
    thus ?case
      using dom_locals_lvar_mono
      by simp
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v)
    from FVar.hyps
    obtain s2': "s2' = snd (fvar statDeclC stat fn a s2)" and
             v: "v = fst (fvar statDeclC stat fn a s2)"
      by (cases "fvar statDeclC stat fn a s2" ) simp
    from v 
    have "\<forall>s val. dom (locals (store s)) 
                          \<subseteq> dom (locals (store (snd v val s)))" (is "?V_ok")
      by (simp add: dom_locals_fvar_vvar_mono) 
    hence v_ok: "(\<forall>vv. In2 v = In2 vv \<and> normal s3 \<longrightarrow> ?V_ok)"
      by - (intro strip, simp)
    have s3: "s3 = check_field_access G accC statDeclC fn stat a s2'" .
    from FVar.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from FVar.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    also
    from s2'
    have "\<dots> \<subseteq> dom (locals (store s2'))"
      by (simp add: dom_locals_fvar_mono)
    also
    from s3
    have "\<dots> \<subseteq> dom (locals (store s3))"
      by (simp add: check_field_access_def Let_def)
    finally
    show ?case
      using v_ok
      by simp
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v)
    from AVar.hyps
    obtain s2': "s2' = snd (avar G i a s2)" and
             v: "v   = fst (avar G i a s2)"
      by (cases "avar G i a s2") simp
    from v
    have "\<forall>s val. dom (locals (store s)) 
                          \<subseteq> dom (locals (store (snd v val s)))" (is "?V_ok")
      by (simp add: dom_locals_avar_vvar_mono)
    hence v_ok: "(\<forall>vv. In2 v = In2 vv \<and> normal s2' \<longrightarrow> ?V_ok)"
      by - (intro strip, simp)
    from AVar.hyps 
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from AVar.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    also
    from s2'
    have "\<dots> \<subseteq> dom (locals (store s2'))"
      by (simp add: dom_locals_avar_mono)
    finally
    show ?case using v_ok by simp
  next
    case Nil thus ?case by simp
  next
    case (Cons e es s0 s1 s2 v vs)
    from Cons.hyps
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Cons.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))" 
      by simp
    finally show ?case by simp
  qed
qed
     
lemma dom_locals_eval_mono_elim [consumes 1]: 
  assumes   eval: "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
    hyps: "\<lbrakk>dom (locals (store s0)) \<subseteq> dom (locals (store s1));
           \<And> vv s val. \<lbrakk>v=In2 vv; normal s1\<rbrakk> 
                        \<Longrightarrow> dom (locals (store s)) 
                             \<subseteq> dom (locals (store ((snd vv) val s)))\<rbrakk> \<Longrightarrow> P"
 shows "P"
using eval
proof (rule dom_locals_eval_mono [THEN conjE])
qed (rule hyps,auto)

lemma halloc_no_abrupt:
  assumes halloc: "G\<turnstile>s0\<midarrow>halloc oi\<succ>a\<rightarrow>s1" and
          normal: "normal s1"
  shows "normal s0"
proof -
  from halloc normal show ?thesis
    by cases simp_all
qed
 
lemma sxalloc_mono_no_abrupt:
  assumes sxalloc: "G\<turnstile>s0\<midarrow>sxalloc\<rightarrow>s1" and
           normal: "normal s1"
  shows "normal s0"
proof -
  from sxalloc normal show ?thesis
    by cases simp_all
qed
   
lemma union_subseteqI: "\<lbrakk>A \<union> B \<subseteq> C; A' \<subseteq> A; B' \<subseteq> B\<rbrakk>  \<Longrightarrow>   A' \<union> B' \<subseteq> C"
  by blast

lemma union_subseteqIl: "\<lbrakk>A \<union> B \<subseteq> C; A' \<subseteq> A\<rbrakk>  \<Longrightarrow>   A' \<union> B \<subseteq> C"
  by blast

lemma union_subseteqIr: "\<lbrakk>A \<union> B \<subseteq> C; B' \<subseteq> B\<rbrakk>  \<Longrightarrow>   A \<union> B' \<subseteq> C"
  by blast

lemma subseteq_union_transl [trans]: "\<lbrakk>A \<subseteq> B; B \<union> C \<subseteq> D\<rbrakk> \<Longrightarrow> A \<union> C \<subseteq> D"
  by blast

lemma subseteq_union_transr [trans]: "\<lbrakk>A \<subseteq> B; C \<union> B \<subseteq> D\<rbrakk> \<Longrightarrow> A \<union> C \<subseteq> D"
  by blast

lemma union_subseteq_weaken: "\<lbrakk>A \<union> B \<subseteq> C; \<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"  
  by blast

lemma assigns_good_approx: 
  assumes
      eval: "G\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
    normal: "normal s1" 
  shows "assigns t \<subseteq> dom (locals (store s1))"
proof -
  from eval normal show ?thesis
  proof (induct)
    case Abrupt thus ?case by simp 
  next -- {* For statements its trivial, since then @{term "assigns t = {}"} *}
    case Skip show ?case by simp
  next
    case Expr show ?case by simp 
  next
    case Lab show ?case by simp
  next
    case Comp show ?case by simp
  next
    case If show ?case by simp
  next
    case Loop show ?case by simp
  next
    case Jmp show ?case by simp
  next
    case Throw show ?case by simp
  next
    case Try show ?case by simp 
  next
    case Fin show ?case by simp
  next
    case Init show ?case by simp 
  next
    case NewC show ?case by simp
  next
    case (NewA T a e i s0 s1 s2 s3)
    have halloc: "G\<turnstile>abupd (check_neg i) s2 \<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" .
    have "assigns (In1l e) \<subseteq> dom (locals (store s2))"
    proof -
      from NewA
      have "normal (abupd (check_neg i) s2)"
	by - (erule halloc_no_abrupt [rule_format])
      hence "normal s2" by (cases s2) simp
      with NewA.hyps
      show ?thesis by rules
    qed
    also
    from halloc 
    have "\<dots> \<subseteq>  dom (locals (store s3))"
      by (rule dom_locals_halloc_mono [elim_format]) simp
    finally show ?case by simp 
  next
    case (Cast T e s0 s1 s2 v)
    hence "normal s1" by (cases s1,simp)
    with Cast.hyps
    have "assigns (In1l e) \<subseteq> dom (locals (store s1))"
      by simp
    also
    from Cast.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))"
      by simp
    finally 
    show ?case
      by simp
  next
    case Inst thus ?case by simp
  next
    case Lit thus ?case by simp
  next
    case UnOp thus ?case by simp
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2)
    hence "normal s1" by - (erule eval_no_abrupt_lemma [rule_format]) 
    with BinOp.hyps
    have "assigns (In1l e1) \<subseteq> dom (locals (store s1))"
      by rules
    also
    have "\<dots>  \<subseteq> dom (locals (store s2))"
    proof -
      have "G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then In1l e2
                      else In1r Skip)\<succ>\<rightarrow> (In1 v2, s2)" .
      thus ?thesis
	by (rule dom_locals_eval_mono_elim)
    qed
    finally have s2: "assigns (In1l e1) \<subseteq> dom (locals (store s2))" .
    show ?case
    proof (cases "binop=CondAnd \<or> binop=CondOr")
      case True
      with s2 show ?thesis by simp 
    next
      case False
      with BinOp 
      have "assigns (In1l e2) \<subseteq> dom (locals (store s2))"
	by (simp add: need_second_arg_def)
      with s2
      show ?thesis using False by (simp add: Un_subset_iff)
    qed
  next
    case Super thus ?case by simp
  next
    case Acc thus ?case by simp
  next 
    case (Ass e f s0 s1 s2 v va w)
    have  nrm_ass_s2: "normal (assign f v s2)" .
    hence nrm_s2: "normal s2"
      by (cases s2, simp add: assign_def Let_def)
    with Ass.hyps 
    have nrm_s1: "normal s1"
      by - (erule eval_no_abrupt_lemma [rule_format]) 
    with Ass.hyps
    have "assigns (In2 va) \<subseteq> dom (locals (store s1))" 
      by rules
    also
    from Ass.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))"
      by - (erule dom_locals_eval_mono_elim)
    also
    from nrm_s2 Ass.hyps
    have "assigns (In1l e) \<subseteq> dom (locals (store s2))"
      by rules
    ultimately
    have "assigns (In2 va) \<union> assigns (In1l e) \<subseteq>  dom (locals (store s2))"
      by (rule Un_least)
    also
    from Ass.hyps nrm_s1
    have "\<dots>  \<subseteq> dom (locals (store (f v s2)))"
      by - (erule dom_locals_eval_mono_elim, cases s2,simp)
    then
    have "dom (locals (store s2))  \<subseteq> dom (locals (store (assign f v s2)))"
      by (rule dom_locals_assign_mono)
    finally
    have va_e: " assigns (In2 va) \<union> assigns (In1l e)
                  \<subseteq> dom (locals (snd (assign f v s2)))" .
    show ?case
    proof (cases "\<exists> n. va = LVar n")
      case False
      with va_e show ?thesis 
	by (simp add: Un_assoc)
    next
      case True
      then obtain n where va: "va = LVar n"
	by blast
      with Ass.hyps 
      have "G\<turnstile>Norm s0 \<midarrow>LVar n=\<succ>(w,f)\<rightarrow> s1" 
	by simp
      hence "(w,f) = lvar n s0"
	by (rule eval_elim_cases) simp
      with nrm_ass_s2
      have "n \<in> dom (locals (store (assign f v s2)))"
	by (cases s2) (simp add: assign_def Let_def lvar_def)
      with va_e True va 
      show ?thesis by (simp add: Un_assoc)
    qed
  next
    case (Cond b e0 e1 e2 s0 s1 s2 v) 
    hence "normal s1"
      by - (erule eval_no_abrupt_lemma [rule_format])
    with Cond.hyps
    have "assigns (In1l e0) \<subseteq> dom (locals (store s1))"
      by rules
    also from Cond.hyps
    have "\<dots> \<subseteq> dom (locals (store s2))"
      by - (erule dom_locals_eval_mono_elim)
    finally have e0: "assigns (In1l e0) \<subseteq> dom (locals (store s2))" .
    show ?case
    proof (cases "the_Bool b")
      case True
      with Cond 
      have "assigns (In1l e1) \<subseteq> dom (locals (store s2))"
	by simp
      hence "assigns (In1l e1) \<inter> assigns (In1l e2) \<subseteq> \<dots>" 
	by blast
      with e0
      have "assigns (In1l e0) \<union> assigns (In1l e1) \<inter> assigns (In1l e2) 
             \<subseteq> dom (locals (store s2))"
	by (rule Un_least)
      thus ?thesis using True by simp 
    next
      case False
      with Cond 
      have " assigns (In1l e2) \<subseteq> dom (locals (store s2))"
	by simp
      hence "assigns (In1l e1) \<inter> assigns (In1l e2) \<subseteq> \<dots>"
	by blast
      with e0
      have "assigns (In1l e0) \<union> assigns (In1l e1) \<inter> assigns (In1l e2) 
             \<subseteq> dom (locals (store s2))"
	by (rule Un_least)
      thus ?thesis using False by simp 
    qed
  next
    case (Call D a' accC args e mn mode pTs s0 s1 s2 s3 s3' s4 statT v vs)
    have nrm_s2: "normal s2"
    proof -
      have "normal ((set_lvars (locals (snd s2))) s4)" .
      hence normal_s4: "normal s4" by simp
      hence "normal s3'" using Call.hyps
	by - (erule eval_no_abrupt_lemma [rule_format]) 
      moreover have  
       "s3' = check_method_access G accC statT mode \<lparr>name=mn, parTs=pTs\<rparr> a' s3".
      ultimately have "normal s3"
	by (cases s3) (simp add: check_method_access_def Let_def) 
      moreover
      have s3: "s3 = init_lvars G D \<lparr>name = mn, parTs = pTs\<rparr> mode a' vs s2" .
      ultimately show "normal s2"
	by (cases s2) (simp add: init_lvars_def2)
    qed
    hence "normal s1" using Call.hyps
      by - (erule eval_no_abrupt_lemma [rule_format])
    with Call.hyps
    have "assigns (In1l e) \<subseteq> dom (locals (store s1))"
      by rules
    also from Call.hyps
    have "\<dots> \<subseteq>  dom (locals (store s2))"
      by - (erule dom_locals_eval_mono_elim)
    also
    from nrm_s2 Call.hyps
    have "assigns (In3 args) \<subseteq> dom (locals (store s2))"
      by rules
    ultimately have "assigns (In1l e) \<union> assigns (In3 args) \<subseteq> \<dots>"
      by (rule Un_least)
    also 
    have "\<dots> \<subseteq> dom (locals (store ((set_lvars (locals (store s2))) s4)))"
      by (cases s4) simp
    finally show ?case
      by simp
  next
    case Methd thus ?case by simp
  next
    case Body thus ?case by simp
  next
    case LVar thus ?case by simp
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v)
    have s3:  "s3 = check_field_access G accC statDeclC fn stat a s2'" .
    have avar: "(v, s2') = fvar statDeclC stat fn a s2" .
    have nrm_s2: "normal s2"
    proof -
      have "normal s3" .
      with s3 have "normal s2'"
	by (cases s2') (simp add: check_field_access_def Let_def)
      with avar show "normal s2"
	by (cases s2) (simp add: fvar_def2)
    qed
    with FVar.hyps 
    have "assigns (In1l e) \<subseteq> dom (locals (store s2))"
      by rules
    also
    have "\<dots> \<subseteq>  dom (locals (store s2'))"
    proof -
      from avar
      have "s2' = snd (fvar statDeclC stat fn a s2)"
	by (cases "fvar statDeclC stat fn a s2") simp
      thus ?thesis
	by simp (rule dom_locals_fvar_mono)
    qed
    also from s3
    have "\<dots> \<subseteq>  dom (locals (store s3))"
      by (cases s2') (simp add: check_field_access_def Let_def)
    finally show ?case
      by simp
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v)
    have avar: "(v, s2') = avar G i a s2" .
    have nrm_s2: "normal s2"
    proof -
      have "normal s2'" .
      with avar
      show ?thesis by (cases s2) (simp add: avar_def2)
    qed
    with AVar.hyps 
    have "normal s1"
      by - (erule eval_no_abrupt_lemma [rule_format])
    with AVar.hyps
    have "assigns (In1l e1) \<subseteq> dom (locals (store s1))"
      by rules
    also from AVar.hyps
    have "\<dots> \<subseteq>  dom (locals (store s2))"
      by - (erule dom_locals_eval_mono_elim)
    also
    from AVar.hyps nrm_s2
    have "assigns (In1l e2) \<subseteq> dom (locals (store s2))"
      by rules
    ultimately
    have "assigns (In1l e1) \<union> assigns (In1l e2) \<subseteq> \<dots>"
      by (rule Un_least)
    also
    have "dom (locals (store s2)) \<subseteq>  dom (locals (store s2'))"
    proof -
      from avar have "s2' = snd (avar G i a s2)"
	by (cases "avar G i a s2") simp
      thus ?thesis
	by simp (rule dom_locals_avar_mono)
    qed
    finally  
    show ?case
      by simp
  next
    case Nil show ?case by simp
  next
    case (Cons e es s0 s1 s2 v vs)
    have "assigns (In1l e) \<subseteq> dom (locals (store s1))"
    proof -
      from Cons
      have "normal s1" by - (erule eval_no_abrupt_lemma [rule_format])
      with Cons.hyps show ?thesis by rules
    qed
    also from Cons.hyps
    have "\<dots> \<subseteq>  dom (locals (store s2))"
      by - (erule dom_locals_eval_mono_elim)
    also from Cons
    have "assigns (In3 es) \<subseteq> dom (locals (store s2))"
      by rules
    ultimately
    have "assigns (In1l e) \<union> assigns (In3 es) \<subseteq> dom (locals (store s2))"
      by (rule Un_least)
    thus ?case
      by simp
  qed
qed

corollary assignsE_good_approx:
  assumes
      eval: "prg Env\<turnstile> s0 \<midarrow>e-\<succ>v\<rightarrow> s1" and
    normal: "normal s1"
  shows "assignsE e \<subseteq> dom (locals (store s1))"
proof -
from eval normal show ?thesis
  by (rule assigns_good_approx [elim_format]) simp
qed

corollary assignsV_good_approx:
  assumes
     eval: "prg Env\<turnstile> s0 \<midarrow>v=\<succ>vf\<rightarrow> s1" and
   normal: "normal s1"
  shows "assignsV v \<subseteq> dom (locals (store s1))"
proof -
from eval normal show ?thesis
  by (rule assigns_good_approx [elim_format]) simp
qed
   
corollary assignsEs_good_approx:
  assumes
      eval: "prg Env\<turnstile> s0 \<midarrow>es\<doteq>\<succ>vs\<rightarrow> s1" and
    normal: "normal s1" 
  shows "assignsEs es \<subseteq> dom (locals (store s1))"
proof -
from eval normal show ?thesis
  by (rule assigns_good_approx [elim_format]) simp
qed

lemma constVal_eval: 
 assumes const: "constVal e = Some c" and
          eval: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s"
  shows "v = c \<and> normal s"
proof -
  have  True and 
        "\<And> c v s0 s. \<lbrakk> constVal e = Some c; G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s\<rbrakk> 
                      \<Longrightarrow> v = c \<and> normal s"
        and True and True
  proof (induct  rule: var_expr_stmt.induct)
    case NewC hence False by simp thus ?case ..
  next
    case NewA hence False by simp thus ?case ..
  next
    case Cast hence False by simp thus ?case ..
  next
    case Inst hence False by simp thus ?case ..
  next
    case (Lit val c v s0 s)
    have "constVal (Lit val) = Some c" .
    moreover
    have "G\<turnstile>Norm s0 \<midarrow>Lit val-\<succ>v\<rightarrow> s" .
    then obtain "v=val" and "normal s"
      by cases simp
    ultimately show "v=c \<and> normal s" by simp
  next
    case (UnOp unop e c v s0 s)
    have const: "constVal (UnOp unop e) = Some c" .
    then obtain ce where ce: "constVal e = Some ce" by simp
    have "G\<turnstile>Norm s0 \<midarrow>UnOp unop e-\<succ>v\<rightarrow> s" .
    then obtain ve where ve: "G\<turnstile>Norm s0 \<midarrow>e-\<succ>ve\<rightarrow> s" and
                          v: "v = eval_unop unop ve" 
      by cases simp
    from ce ve
    obtain eq_ve_ce: "ve=ce" and nrm_s: "normal s"
      by (rule UnOp.hyps [elim_format]) rules
    from eq_ve_ce const ce v 
    have "v=c" 
      by simp
    from this nrm_s
    show ?case ..
  next
    case (BinOp binop e1 e2 c v s0 s)
    have const: "constVal (BinOp binop e1 e2) = Some c" .
    then obtain c1 c2 where c1: "constVal e1 = Some c1" and
                            c2: "constVal e2 = Some c2" and
                             c: "c = eval_binop binop c1 c2"
      by simp
    have "G\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>v\<rightarrow> s" .
    then obtain v1 s1 v2
      where v1: "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<rightarrow> s1" and
            v2: "G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then In1l e2
                               else In1r Skip)\<succ>\<rightarrow> (In1 v2, s)" and
             v: "v = eval_binop binop v1 v2"
      by cases simp
    from c1 v1
    obtain eq_v1_c1: "v1 = c1" and 
             nrm_s1: "normal s1"
      by (rule BinOp.hyps [elim_format]) rules
    show ?case
    proof (cases "need_second_arg binop v1")
      case True
      with v2 nrm_s1  obtain s1' 
	where "G\<turnstile>Norm s1' \<midarrow>e2-\<succ>v2\<rightarrow> s" 
	by (cases s1) simp
      with c2 obtain "v2 = c2" "normal s"
	by (rule BinOp.hyps [elim_format]) rules
      with c c1 c2 eq_v1_c1 v 
      show ?thesis by simp
    next
      case False
      with nrm_s1 v2
      have "s=s1"
	by (cases s1) (auto elim!: eval_elim_cases)
      moreover
      from False c v eq_v1_c1  
      have "v = c"
	by (simp add: eval_binop_arg2_indep)
      ultimately 
      show ?thesis
	using nrm_s1 by simp
    qed  (* hallo ehco *)
  next
    case Super hence False by simp thus ?case ..
  next
    case Acc hence False by simp thus ?case ..
  next
    case Ass hence False by simp thus ?case ..
  next
    case (Cond b e1 e2 c v s0 s)
    have c: "constVal (b ? e1 : e2) = Some c" .
    then obtain cb c1 c2 where
      cb: "constVal b  = Some cb" and
      c1: "constVal e1 = Some c1" and
      c2: "constVal e2 = Some c2"
      by (auto split: bool.splits)
    have "G\<turnstile>Norm s0 \<midarrow>b ? e1 : e2-\<succ>v\<rightarrow> s" .
    then obtain vb s1
      where     vb: "G\<turnstile>Norm s0 \<midarrow>b-\<succ>vb\<rightarrow> s1" and
            eval_v: "G\<turnstile>s1 \<midarrow>(if the_Bool vb then e1 else e2)-\<succ>v\<rightarrow> s"
      by cases simp 
    from cb vb
    obtain eq_vb_cb: "vb = cb" and nrm_s1: "normal s1"
      by (rule Cond.hyps [elim_format]) rules 
    show ?case
    proof (cases "the_Bool vb")
      case True
      with c cb c1 eq_vb_cb 
      have "c = c1"
	by simp
      moreover
      from True eval_v nrm_s1 obtain s1' 
	where "G\<turnstile>Norm s1' \<midarrow>e1-\<succ>v\<rightarrow> s"
	by (cases s1) simp
      with c1 obtain "c1 = v" "normal s"
	by (rule Cond.hyps [elim_format]) rules 
      ultimately show ?thesis by simp
    next
      case False
      with c cb c2 eq_vb_cb 
      have "c = c2"
	by simp
      moreover
      from False eval_v nrm_s1 obtain s1' 
	where "G\<turnstile>Norm s1' \<midarrow>e2-\<succ>v\<rightarrow> s"
	by (cases s1) simp
      with c2 obtain "c2 = v" "normal s"
	by (rule Cond.hyps [elim_format]) rules 
      ultimately show ?thesis by simp
    qed
  next
    case Call hence False by simp thus ?case ..
  qed simp_all
  with const eval
  show ?thesis
    by rules
qed
  
lemmas constVal_eval_elim = constVal_eval [THEN conjE]

lemma eval_unop_type: 
  "typeof dt (eval_unop unop v) = Some (PrimT (unop_type unop))"
  by (cases unop) simp_all

lemma eval_binop_type:
  "typeof dt (eval_binop binop v1 v2) = Some (PrimT (binop_type binop))"
  by (cases binop) simp_all

lemma constVal_Boolean: 
 assumes const: "constVal e = Some c" and
            wt: "Env\<turnstile>e\<Colon>-PrimT Boolean"
  shows "typeof empty_dt c = Some (PrimT Boolean)"
proof - 
  have True and 
       "\<And> c. \<lbrakk>constVal e = Some c;Env\<turnstile>e\<Colon>-PrimT Boolean\<rbrakk> 
                \<Longrightarrow> typeof empty_dt c = Some (PrimT Boolean)"
       and True and True 
  proof (induct rule: var_expr_stmt.induct)
    case NewC hence False by simp thus ?case ..
  next
    case NewA hence False by simp thus ?case ..
  next
    case Cast hence False by simp thus ?case ..
  next
    case Inst hence False by simp thus ?case ..
  next
    case (Lit v c)
    have "constVal (Lit v) = Some c" .
    hence "c=v" by simp
    moreover have "Env\<turnstile>Lit v\<Colon>-PrimT Boolean" .
    hence "typeof empty_dt v = Some (PrimT Boolean)"
      by cases simp
    ultimately show ?case by simp
  next
    case (UnOp unop e c)
    have "Env\<turnstile>UnOp unop e\<Colon>-PrimT Boolean" .
    hence "Boolean = unop_type unop" by cases simp
    moreover have "constVal (UnOp unop e) = Some c" .
    then obtain ce where "c = eval_unop unop ce" by auto
    ultimately show ?case by (simp add: eval_unop_type)
  next
    case (BinOp binop e1 e2 c)
    have "Env\<turnstile>BinOp binop e1 e2\<Colon>-PrimT Boolean" .
    hence "Boolean = binop_type binop" by cases simp
    moreover have "constVal (BinOp binop e1 e2) = Some c" .
    then obtain c1 c2 where "c = eval_binop binop c1 c2" by auto
    ultimately show ?case by (simp add: eval_binop_type)
  next
    case Super hence False by simp thus ?case ..
  next
    case Acc hence False by simp thus ?case ..
  next
    case Ass hence False by simp thus ?case ..
  next
    case (Cond b e1 e2 c)
    have c: "constVal (b ? e1 : e2) = Some c" .
    then obtain cb c1 c2 where
      cb: "constVal b  = Some cb" and
      c1: "constVal e1 = Some c1" and
      c2: "constVal e2 = Some c2"
      by (auto split: bool.splits)
    have wt: "Env\<turnstile>b ? e1 : e2\<Colon>-PrimT Boolean" .
    then
    obtain T1 T2
      where "Env\<turnstile>b\<Colon>-PrimT Boolean" and
            wt_e1: "Env\<turnstile>e1\<Colon>-PrimT Boolean" and
            wt_e2: "Env\<turnstile>e2\<Colon>-PrimT Boolean"
      by cases (auto dest: widen_Boolean2)
    show ?case
    proof (cases "the_Bool cb")
      case True
      from c1 wt_e1 
      have  "typeof empty_dt c1 = Some (PrimT Boolean)" 
	by (rule Cond.hyps)
      with True c cb c1 show ?thesis by simp
    next
      case False
      from c2 wt_e2 
      have "typeof empty_dt c2 = Some (PrimT Boolean)" 
	by (rule Cond.hyps)
      with False c cb c2 show ?thesis by simp
    qed
  next
    case Call hence False by simp thus ?case ..
  qed simp_all
  with const wt
  show ?thesis
    by rules
qed	
      
lemma assigns_if_good_approx:
  assumes
     eval: "prg Env\<turnstile> s0 \<midarrow>e-\<succ>b\<rightarrow> s1"   and
   normal: "normal s1" and
     bool: "Env\<turnstile> e\<Colon>-PrimT Boolean"
  shows "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
proof -
  -- {* To properly perform induction on the evaluation relation we have to
        generalize the lemma to terms not only expressions. *}
  { fix t val
   assume eval': "prg Env\<turnstile> s0 \<midarrow>t\<succ>\<rightarrow> (val,s1)"  
   assume bool': "Env\<turnstile> t\<Colon>Inl (PrimT Boolean)"
   assume expr:  "\<exists> expr. t=In1l expr"
   have "assigns_if (the_Bool (the_In1 val)) (the_In1l t) 
                \<subseteq> dom (locals (store s1))"
   using eval' normal bool' expr
   proof (induct)
     case Abrupt thus ?case by simp
   next
     case (NewC C a s0 s1 s2)
     have "Env\<turnstile>NewC C\<Colon>-PrimT Boolean" .
     hence False 
       by cases simp
     thus ?case ..
   next
     case (NewA T a e i s0 s1 s2 s3)
     have "Env\<turnstile>New T[e]\<Colon>-PrimT Boolean" .
     hence False 
       by cases simp
     thus ?case ..
   next
     case (Cast T e s0 s1 s2 b)
     have s2: "s2 = abupd (raise_if (\<not> prg Env,snd s1\<turnstile>b fits T) ClassCast) s1".
     have "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))" 
     proof -
       have "normal s2" .
       with s2 have "normal s1"
	 by (cases s1) simp
       moreover
       have "Env\<turnstile>Cast T e\<Colon>-PrimT Boolean" .
       hence "Env\<turnstile>e\<Colon>- PrimT Boolean" 
	 by (cases) (auto dest: cast_Boolean2)
       ultimately show ?thesis 
	 by (rule Cast.hyps [elim_format]) auto
     qed
     also from s2 
     have "\<dots> \<subseteq> dom (locals (store s2))"
       by simp
     finally show ?case by simp
   next
     case (Inst T b e s0 s1 v)
     have "prg Env\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" and "normal s1" .
     hence "assignsE e \<subseteq> dom (locals (store s1))"
       by (rule assignsE_good_approx)
     thus ?case
       by simp
   next
     case (Lit s v)
     have "Env\<turnstile>Lit v\<Colon>-PrimT Boolean" .
     hence "typeof empty_dt v = Some (PrimT Boolean)"
       by cases simp
     then obtain b where "v=Bool b"
       by (cases v) (simp_all add: empty_dt_def)
     thus ?case
       by simp
   next
     case (UnOp e s0 s1 unop v)
     have bool: "Env\<turnstile>UnOp unop e\<Colon>-PrimT Boolean" .
     hence bool_e: "Env\<turnstile>e\<Colon>-PrimT Boolean" 
       by cases (cases unop,simp_all)
     show ?case
     proof (cases "constVal (UnOp unop e)")
       case None
       have "normal s1" .
       moreover note bool_e
       ultimately have "assigns_if (the_Bool v) e \<subseteq> dom (locals (store s1))"
	 by (rule UnOp.hyps [elim_format]) auto
       moreover
       from bool have "unop = UNot"
	 by cases (cases unop, simp_all)
       moreover note None
       ultimately 
       have "assigns_if (the_Bool (eval_unop unop v)) (UnOp unop e) 
              \<subseteq> dom (locals (store s1))"
	 by simp
       thus ?thesis by simp
     next
       case (Some c)
       moreover
       have "prg Env\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<rightarrow> s1" .
       hence "prg Env\<turnstile>Norm s0 \<midarrow>UnOp unop e-\<succ>eval_unop unop v\<rightarrow> s1" 
	 by (rule eval.UnOp)
       with Some
       have "eval_unop unop v=c"
	 by (rule constVal_eval_elim) simp
       moreover
       from Some bool
       obtain b where "c=Bool b"
	 by (rule constVal_Boolean [elim_format])
	    (cases c, simp_all add: empty_dt_def)
       ultimately
       have "assigns_if (the_Bool (eval_unop unop v)) (UnOp unop e) = {}"
	 by simp
       thus ?thesis by simp
     qed
   next
     case (BinOp binop e1 e2 s0 s1 s2 v1 v2)
     have bool: "Env\<turnstile>BinOp binop e1 e2\<Colon>-PrimT Boolean" .
     show ?case
     proof (cases "constVal (BinOp binop e1 e2)") 
       case (Some c)
       moreover
       from BinOp.hyps
       have
	 "prg Env\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>eval_binop binop v1 v2\<rightarrow> s2"
	 by - (rule eval.BinOp) 
       with Some
       have "eval_binop binop v1 v2=c"
	 by (rule constVal_eval_elim) simp
       moreover
       from Some bool
       obtain b where "c = Bool b"
	 by (rule constVal_Boolean [elim_format])
	    (cases c, simp_all add: empty_dt_def)
       ultimately
       have "assigns_if (the_Bool (eval_binop binop v1 v2)) (BinOp binop e1 e2) 
             = {}"
	 by simp 
       thus ?thesis by simp
     next
       case None
       show ?thesis
       proof (cases "binop=CondAnd \<or> binop=CondOr")
	 case True
	 from bool obtain bool_e1: "Env\<turnstile>e1\<Colon>-PrimT Boolean" and
                          bool_e2: "Env\<turnstile>e2\<Colon>-PrimT Boolean"
	   using True by cases auto
	 have "assigns_if (the_Bool v1) e1 \<subseteq> dom (locals (store s1))"
	 proof -
	   from BinOp have "normal s1"
	     by - (erule eval_no_abrupt_lemma [rule_format])
	   from this bool_e1
	   show ?thesis
	     by (rule BinOp.hyps [elim_format]) auto
	 qed
	 also
	 from BinOp.hyps
	 have "\<dots> \<subseteq> dom (locals (store s2))"
	   by - (erule dom_locals_eval_mono_elim,simp)
	 finally
	 have e1_s2: "assigns_if (the_Bool v1) e1 \<subseteq> dom (locals (store s2))".
	 from True show ?thesis
	 proof
	   assume condAnd: "binop = CondAnd"
	   show ?thesis
	   proof (cases "the_Bool (eval_binop binop v1 v2)")
	     case True
	     with condAnd 
	     have need_second: "need_second_arg binop v1"
	       by (simp add: need_second_arg_def)
	     have "normal s2" . 
	     hence "assigns_if (the_Bool v2) e2 \<subseteq> dom (locals (store s2))"
	       by (rule BinOp.hyps [elim_format]) 
                  (simp add: need_second bool_e2)+
	     with e1_s2
	     have "assigns_if (the_Bool v1) e1 \<union> assigns_if (the_Bool v2) e2
		    \<subseteq> dom (locals (store s2))"
	       by (rule Un_least)
	     with True condAnd None show ?thesis
	       by simp
	   next
	     case False
	     note binop_False = this
	     show ?thesis
	     proof (cases "need_second_arg binop v1")
	       case True
	       with binop_False condAnd
	       obtain "the_Bool v1=True" and "the_Bool v2 = False"
		 by (simp add: need_second_arg_def)
	       moreover
	       have "normal s2" . 
	       hence "assigns_if (the_Bool v2) e2 \<subseteq> dom (locals (store s2))"
		 by (rule BinOp.hyps [elim_format]) (simp add: True bool_e2)+
	       with e1_s2
	       have "assigns_if (the_Bool v1) e1 \<union> assigns_if (the_Bool v2) e2
		      \<subseteq> dom (locals (store s2))"
		 by (rule Un_least)
	       moreover note binop_False condAnd None
	       ultimately show ?thesis
		 by auto
	     next
	       case False
	       with binop_False condAnd
	       have "the_Bool v1=False"
		 by (simp add: need_second_arg_def)
	       with e1_s2 
	       show ?thesis
		 using binop_False condAnd None by auto
	     qed
	   qed
	 next
	   assume condOr: "binop = CondOr"
	   show ?thesis
	   proof (cases "the_Bool (eval_binop binop v1 v2)")
	     case False
	     with condOr 
	     have need_second: "need_second_arg binop v1"
	       by (simp add: need_second_arg_def)
	     have "normal s2" . 
	     hence "assigns_if (the_Bool v2) e2 \<subseteq> dom (locals (store s2))"
	       by (rule BinOp.hyps [elim_format]) 
                  (simp add: need_second bool_e2)+
	     with e1_s2
	     have "assigns_if (the_Bool v1) e1 \<union> assigns_if (the_Bool v2) e2
		    \<subseteq> dom (locals (store s2))"
	       by (rule Un_least)
	     with False condOr None show ?thesis
	       by simp
	   next
	     case True
	     note binop_True = this
	     show ?thesis
	     proof (cases "need_second_arg binop v1")
	       case True
	       with binop_True condOr
	       obtain "the_Bool v1=False" and "the_Bool v2 = True"
		 by (simp add: need_second_arg_def)
	       moreover
	       have "normal s2" . 
	       hence "assigns_if (the_Bool v2) e2 \<subseteq> dom (locals (store s2))"
		 by (rule BinOp.hyps [elim_format]) (simp add: True bool_e2)+
	       with e1_s2
	       have "assigns_if (the_Bool v1) e1 \<union> assigns_if (the_Bool v2) e2
		      \<subseteq> dom (locals (store s2))"
		 by (rule Un_least)
	       moreover note binop_True condOr None
	       ultimately show ?thesis
		 by auto
	     next
	       case False
	       with binop_True condOr
	       have "the_Bool v1=True"
		 by (simp add: need_second_arg_def)
	       with e1_s2 
	       show ?thesis
		 using binop_True condOr None by auto
	     qed
	   qed
	 qed  
       next
	 case False
	 have "\<not> (binop = CondAnd \<or> binop = CondOr)" .
	 from BinOp.hyps
	 have
	  "prg Env\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>eval_binop binop v1 v2\<rightarrow> s2"
	   by - (rule eval.BinOp)  
	 moreover have "normal s2" .
	 ultimately
	 have "assignsE (BinOp binop e1 e2) \<subseteq> dom (locals (store s2))"
	   by (rule assignsE_good_approx)
	 with False None
	 show ?thesis 
	   by simp
       qed
     qed
   next     
     case Super 
     have "Env\<turnstile>Super\<Colon>-PrimT Boolean" .
     hence False 
       by cases simp
     thus ?case ..
   next
     case (Acc f s0 s1 v va)
     have "prg Env\<turnstile>Norm s0 \<midarrow>va=\<succ>(v, f)\<rightarrow> s1"  and "normal s1".
     hence "assignsV va \<subseteq> dom (locals (store s1))"
       by (rule assignsV_good_approx)
     thus ?case by simp
   next
     case (Ass e f s0 s1 s2 v va w)
     hence "prg Env\<turnstile>Norm s0 \<midarrow>va := e-\<succ>v\<rightarrow> assign f v s2"
       by - (rule eval.Ass)
     moreover have "normal (assign f v s2)" .
     ultimately 
     have "assignsE (va := e) \<subseteq> dom (locals (store (assign f v s2)))"
       by (rule assignsE_good_approx)
     thus ?case by simp
   next
     case (Cond b e0 e1 e2 s0 s1 s2 v)
     have "Env\<turnstile>e0 ? e1 : e2\<Colon>-PrimT Boolean" .
     then obtain wt_e1: "Env\<turnstile>e1\<Colon>-PrimT Boolean" and
                 wt_e2: "Env\<turnstile>e2\<Colon>-PrimT Boolean"
       by cases (auto dest: widen_Boolean2)
     have eval_e0: "prg Env\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1" .
     have e0_s2: "assignsE e0 \<subseteq> dom (locals (store s2))"
     proof -
       note eval_e0 
       moreover
       have "normal s2" .
       with Cond.hyps have "normal s1"
	 by - (erule eval_no_abrupt_lemma [rule_format],simp)
       ultimately
       have "assignsE e0 \<subseteq> dom (locals (store s1))"
	 by (rule assignsE_good_approx)
       also
       from Cond
       have "\<dots> \<subseteq> dom (locals (store s2))"
	 by - (erule dom_locals_eval_mono [elim_format],simp)
       finally show ?thesis .
     qed
     show ?case
     proof (cases "constVal e0")
       case None
       have "assigns_if (the_Bool v) e1 \<inter>  assigns_if (the_Bool v) e2 
	      \<subseteq> dom (locals (store s2))"
       proof (cases "the_Bool b")
	 case True
	 have "normal s2" .
	 hence "assigns_if (the_Bool v) e1 \<subseteq> dom (locals (store s2))"    
	   by (rule Cond.hyps [elim_format]) (simp_all add: wt_e1 True)
	 thus ?thesis
	   by blast
       next
	 case False
	 have "normal s2" .
	 hence "assigns_if (the_Bool v) e2 \<subseteq> dom (locals (store s2))"    
	   by (rule Cond.hyps [elim_format]) (simp_all add: wt_e2 False)
	 thus ?thesis
	   by blast
       qed
       with e0_s2
       have "assignsE e0 \<union> 
             (assigns_if (the_Bool v) e1 \<inter>  assigns_if (the_Bool v) e2)
	       \<subseteq> dom (locals (store s2))"
	 by (rule Un_least)
       with None show ?thesis
	 by simp
     next
       case (Some c)
       from this eval_e0 have eq_b_c: "b=c" 
	 by (rule constVal_eval_elim) 
       show ?thesis
       proof (cases "the_Bool c")
	 case True
	 have "normal s2" .
	 hence "assigns_if (the_Bool v) e1 \<subseteq> dom (locals (store s2))"    
	   by (rule Cond.hyps [elim_format]) (simp_all add: eq_b_c True)
	 with e0_s2
	 have "assignsE e0 \<union> assigns_if (the_Bool v) e1  \<subseteq> \<dots>"
	   by (rule Un_least)
	 with Some True show ?thesis
	   by simp
       next
	 case False
	 have "normal s2" .
	 hence "assigns_if (the_Bool v) e2 \<subseteq> dom (locals (store s2))"    
	   by (rule Cond.hyps [elim_format]) (simp_all add: eq_b_c False)
	 with e0_s2
	 have "assignsE e0 \<union> assigns_if (the_Bool v) e2  \<subseteq> \<dots>"
	   by (rule Un_least)
	 with Some False show ?thesis
	   by simp
       qed
     qed
   next
     case (Call D a accC args e mn mode pTs s0 s1 s2 s3 s3' s4 statT v vs)
     hence
     "prg Env\<turnstile>Norm s0 \<midarrow>({accC,statT,mode}e\<cdot>mn( {pTs}args))-\<succ>v\<rightarrow> 
                       (set_lvars (locals (store s2)) s4)"
       by - (rule eval.Call)
     hence "assignsE ({accC,statT,mode}e\<cdot>mn( {pTs}args)) 
              \<subseteq>  dom (locals (store ((set_lvars (locals (store s2))) s4)))"
       by (rule assignsE_good_approx)
     thus ?case by simp
   next
     case Methd show ?case by simp
   next
     case Body show ?case by simp
   qed simp+ -- {* all the statements and variables *}
 }
 note generalized = this
 from eval bool show ?thesis
   by (rule generalized [elim_format]) simp+
qed

lemma assigns_if_good_approx': 
  assumes   eval: "G\<turnstile>s0 \<midarrow>e-\<succ>b\<rightarrow> s1"  
     and  normal: "normal s1" 
     and    bool: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>e\<Colon>- (PrimT Boolean)"
  shows "assigns_if (the_Bool b) e \<subseteq> dom (locals (store s1))"
proof -
  from eval have "prg \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>s0 \<midarrow>e-\<succ>b\<rightarrow> s1" by simp
  from this normal bool show ?thesis
    by (rule assigns_if_good_approx)
qed

 
lemma subset_Intl: "A \<subseteq> C \<Longrightarrow> A \<inter> B \<subseteq> C" 
  by blast

lemma subset_Intr: "B \<subseteq> C \<Longrightarrow> A \<inter> B \<subseteq> C" 
  by blast

lemma da_good_approx: 
  assumes  eval: "prg Env\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" and
           wt: "Env\<turnstile>t\<Colon>T"     (is "?Wt Env t T") and
           da: "Env\<turnstile> dom (locals (store s0)) \<guillemotright>t\<guillemotright> A"  (is "?Da Env s0 t A") and 
           wf: "wf_prog (prg Env)" 
     shows "(normal s1 \<longrightarrow> (nrm A \<subseteq>  dom (locals (store s1)))) \<and>
            (\<forall> l. abrupt s1 = Some (Jump (Break l)) \<and> normal s0 
                       \<longrightarrow> (brk A l \<subseteq> dom (locals (store s1)))) \<and>
            (abrupt s1 = Some (Jump Ret) \<and> normal s0 
                       \<longrightarrow> Result \<in> dom (locals (store s1)))"
     (is "?NormalAssigned s1 A \<and> ?BreakAssigned s0 s1 A \<and> ?ResAssigned s0 s1")
proof -
  note inj_term_simps [simp]
  obtain G where G: "prg Env = G" by (cases Env) simp
  with eval have eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)" by simp
  from G wf have wf: "wf_prog G" by simp
  let ?HypObj = "\<lambda> t s0 s1.
      \<forall> Env T A. ?Wt Env t T \<longrightarrow>  ?Da Env s0 t A \<longrightarrow> prg Env = G 
       \<longrightarrow> ?NormalAssigned s1 A \<and> ?BreakAssigned s0 s1 A \<and> ?ResAssigned  s0 s1"
  -- {* Goal in object logic variant *} 
  from eval
  show "\<And> Env T A. \<lbrakk>?Wt Env t T; ?Da Env s0 t A; prg Env = G\<rbrakk> 
        \<Longrightarrow> ?NormalAssigned s1 A \<and> ?BreakAssigned s0 s1 A \<and> ?ResAssigned s0 s1"
        (is "PROP ?Hyp t s0 s1")
  proof (induct)
    case (Abrupt s t xc Env T A)
    have da: "Env\<turnstile> dom (locals s) \<guillemotright>t\<guillemotright> A" using Abrupt.prems by simp 
    have "?NormalAssigned (Some xc,s) A" 
      by simp
    moreover
    have "?BreakAssigned (Some xc,s) (Some xc,s) A"
      by simp
    moreover have "?ResAssigned (Some xc,s) (Some xc,s)"
      by simp
    ultimately show ?case by (intro conjI)
  next
    case (Skip s Env T A)
    have da: "Env\<turnstile> dom (locals (store (Norm s))) \<guillemotright>\<langle>Skip\<rangle>\<guillemotright> A" 
      using Skip.prems by simp
    hence "nrm A = dom (locals (store (Norm s)))"
      by (rule da_elim_cases) simp
    hence "?NormalAssigned (Norm s) A"
      by auto
    moreover
    have "?BreakAssigned (Norm s) (Norm s) A" 
      by simp
    moreover have "?ResAssigned (Norm s) (Norm s)"
      by simp
    ultimately show ?case by (intro conjI)
  next
    case (Expr e s0 s1 v Env T A)
    from Expr.prems
    show "?NormalAssigned s1 A \<and> ?BreakAssigned (Norm s0) s1 A 
           \<and> ?ResAssigned (Norm s0) s1"
      by (elim wt_elim_cases da_elim_cases) 
         (rule Expr.hyps, auto)
  next 
    case (Lab c j s0 s1 Env T A)
    have G: "prg Env = G" .
    from Lab.prems
    obtain C l where
      da_c: "Env\<turnstile> dom (locals (snd (Norm s0))) \<guillemotright>\<langle>c\<rangle>\<guillemotright> C" and
         A: "nrm A = nrm C \<inter> (brk C) l" "brk A = rmlab l (brk C)" and
         j: "j = Break l"
      by - (erule da_elim_cases, simp)
    from Lab.prems
    have wt_c: "Env\<turnstile>c\<Colon>\<surd>"
      by - (erule wt_elim_cases, simp)
    from wt_c da_c G and Lab.hyps
    have norm_c: "?NormalAssigned s1 C" and 
          brk_c: "?BreakAssigned (Norm s0) s1 C" and
          res_c: "?ResAssigned (Norm s0) s1"
      by simp_all
    have "?NormalAssigned (abupd (absorb j) s1) A"
    proof
      assume normal: "normal (abupd (absorb j) s1)"
      show "nrm A \<subseteq> dom (locals (store (abupd (absorb j) s1)))"
      proof (cases "abrupt s1")
	case None
	with norm_c A 
	show ?thesis
	  by auto
      next
	case Some
	with normal j 
	have "abrupt s1 = Some (Jump (Break l))"
	  by (auto dest: absorb_Some_NoneD)
	with brk_c A
  	show ?thesis
	  by auto
      qed
    qed
    moreover 
    have "?BreakAssigned (Norm s0) (abupd (absorb j) s1) A"
    proof -
      {
	fix l'
	assume break: "abrupt (abupd (absorb j) s1) = Some (Jump (Break l'))"
	with j 
	have "l\<noteq>l'"
	  by (cases s1) (auto dest!: absorb_Some_JumpD)
	hence "(rmlab l (brk C)) l'= (brk C) l'"
	  by (simp)
	with break brk_c A
	have 
          "(brk A l' \<subseteq> dom (locals (store (abupd (absorb j) s1))))"
	  by (cases s1) auto
      }
      then show ?thesis
	by simp
    qed
    moreover
    from res_c have "?ResAssigned (Norm s0) (abupd (absorb j) s1)"
      by (cases s1) (simp add: absorb_def)
    ultimately show ?case by (intro conjI)
  next
    case (Comp c1 c2 s0 s1 s2 Env T A)
    have G: "prg Env = G" .
    from Comp.prems
    obtain C1 C2
      where da_c1: "Env\<turnstile> dom (locals (snd (Norm s0))) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1" and 
            da_c2: "Env\<turnstile> nrm C1 \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2" and
                A: "nrm A = nrm C2" "brk A = (brk C1) \<Rightarrow>\<inter> (brk C2)"
      by (elim da_elim_cases) simp
    from Comp.prems
    obtain wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and
           wt_c2: "Env\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases) simp
    have "PROP ?Hyp (In1r c1) (Norm s0) s1" .
    with wt_c1 da_c1 G 
    obtain nrm_c1: "?NormalAssigned s1 C1" and 
           brk_c1: "?BreakAssigned (Norm s0) s1 C1" and
           res_c1: "?ResAssigned (Norm s0) s1"
      by simp
    show ?case
    proof (cases "normal s1")
      case True
      with nrm_c1 have "nrm C1 \<subseteq> dom (locals (snd s1))" by rules
      with da_c2 obtain C2' 
	where  da_c2': "Env\<turnstile> dom (locals (snd s1)) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
               nrm_c2: "nrm C2 \<subseteq> nrm C2'"                  and
               brk_c2: "\<forall> l. brk C2 l \<subseteq> brk C2' l"
        by (rule da_weakenE) rules
      have "PROP ?Hyp (In1r c2) s1 s2" .
      with wt_c2 da_c2' G
      obtain nrm_c2': "?NormalAssigned s2 C2'" and 
             brk_c2': "?BreakAssigned s1 s2 C2'" and
             res_c2 : "?ResAssigned s1 s2" 
	by simp
      from nrm_c2' nrm_c2 A
      have "?NormalAssigned s2 A" 
	by blast
      moreover from brk_c2' brk_c2 A
      have "?BreakAssigned s1 s2 A" 
	by fastsimp
      with True 
      have "?BreakAssigned (Norm s0) s2 A" by simp
      moreover from res_c2 True
      have "?ResAssigned (Norm s0) s2"
	by simp
      ultimately show ?thesis by (intro conjI)
    next
      case False
      have "G\<turnstile>s1 \<midarrow>c2\<rightarrow> s2" .
      with False have eq_s1_s2: "s2=s1" by auto
      with False have "?NormalAssigned s2 A" by blast
      moreover
      have "?BreakAssigned (Norm s0) s2 A"
      proof (cases "\<exists> l. abrupt s1 = Some (Jump (Break l))")
	case True
	then obtain l where l: "abrupt s1 = Some (Jump (Break l))" .. 
	with brk_c1
	have "brk C1 l \<subseteq> dom (locals (store s1))"
	  by simp
	with A eq_s1_s2 
	have "brk A l \<subseteq> dom (locals (store s2))" 
	  by auto
	with l eq_s1_s2
	show ?thesis by simp
      next
	case False
	with eq_s1_s2 show ?thesis by simp
      qed
      moreover from False res_c1 eq_s1_s2
      have "?ResAssigned (Norm s0) s2"
	by simp
      ultimately show ?thesis by (intro conjI)
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (If b c1 c2 e s0 s1 s2 Env T A)
    have G: "prg Env = G" .
    with If.hyps have eval_e: "prg Env \<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" by simp
    from If.prems
    obtain E C1 C2 where
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> E" and
     da_c1: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                   \<union> assigns_if True e) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1" and
     da_c2: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                   \<union> assigns_if False e) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2" and
     A: "nrm A = nrm C1 \<inter> nrm C2"  "brk A = brk C1 \<Rightarrow>\<inter> brk C2"
      by (elim da_elim_cases) 
    from If.prems
    obtain 
       wt_e:  "Env\<turnstile>e\<Colon>- PrimT Boolean" and 
       wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and
       wt_c2: "Env\<turnstile>c2\<Colon>\<surd>" 
      by (elim wt_elim_cases)
    from If.hyps have
     s0_s1:"dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by (elim dom_locals_eval_mono_elim)
    show ?case
    proof (cases "normal s1")
      case True
      note normal_s1 = this 
      show ?thesis
      proof (cases "the_Bool b")
	case True
	from eval_e normal_s1 wt_e
	have "assigns_if True e \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx [elim_format]) (simp add: True)
	with s0_s1
	have "dom (locals (store ((Norm s0)::state))) \<union> assigns_if True e \<subseteq> \<dots>"
	  by (rule Un_least)
	with da_c1 obtain C1'
	  where da_c1': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1'" and
	        nrm_c1: "nrm C1 \<subseteq> nrm C1'"                  and
                brk_c1: "\<forall> l. brk C1 l \<subseteq> brk C1' l"
          by (rule da_weakenE) rules
	from If.hyps True have "PROP ?Hyp (In1r c1) s1 s2" by simp
	with wt_c1 da_c1'
	obtain nrm_c1': "?NormalAssigned s2 C1'" and 
               brk_c1': "?BreakAssigned s1 s2 C1'" and
               res_c1: "?ResAssigned s1 s2"
	  using G by simp
	from nrm_c1' nrm_c1 A
	have "?NormalAssigned s2 A" 
	  by blast
	moreover from brk_c1' brk_c1 A
	have "?BreakAssigned s1 s2 A" 
	  by fastsimp
	with normal_s1
	have "?BreakAssigned (Norm s0) s2 A" by simp
	moreover from res_c1 normal_s1 have "?ResAssigned (Norm s0) s2"
	  by simp
	ultimately show ?thesis by (intro conjI)
      next
	case False
	from eval_e normal_s1 wt_e
	have "assigns_if False e \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx [elim_format]) (simp add: False)
	with s0_s1
	have "dom (locals (store ((Norm s0)::state)))\<union> assigns_if False e \<subseteq> \<dots>"
	  by (rule Un_least)
	with da_c2 obtain C2'
	  where da_c2': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
	        nrm_c2: "nrm C2 \<subseteq> nrm C2'"                  and
                brk_c2: "\<forall> l. brk C2 l \<subseteq> brk C2' l"
          by (rule da_weakenE) rules
	from If.hyps False have "PROP ?Hyp (In1r c2) s1 s2" by simp
	with wt_c2 da_c2'
	obtain nrm_c2': "?NormalAssigned s2 C2'" and 
               brk_c2': "?BreakAssigned s1 s2 C2'" and
	       res_c2: "?ResAssigned s1 s2"
	  using G by simp
	from nrm_c2' nrm_c2 A
	have "?NormalAssigned s2 A" 
	  by blast
	moreover from brk_c2' brk_c2 A
	have "?BreakAssigned s1 s2 A" 
	  by fastsimp
	with normal_s1
	have "?BreakAssigned (Norm s0) s2 A" by simp
	moreover from res_c2 normal_s1 have "?ResAssigned (Norm s0) s2"
	  by simp
	ultimately show ?thesis by (intro conjI)
      qed
    next
      case False 
      then obtain abr where abr: "abrupt s1 = Some abr"
	by (cases s1) auto
      moreover
      from eval_e _ wt_e have "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	by (rule eval_expression_no_jump) (simp_all add: G wf)
      moreover
      have "s2 = s1"
      proof -
	have "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<rightarrow> s2" .
        with abr show ?thesis  
	  by (cases s1) simp
      qed
      ultimately show ?thesis by simp
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Loop b c e l s0 s1 s2 s3 Env T A)
    have G: "prg Env = G" .
    with Loop.hyps have eval_e: "prg Env\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1" 
      by (simp (no_asm_simp))
    from Loop.prems
    obtain E C where
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> E" and
      da_c: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                   \<union> assigns_if True e) \<guillemotright>\<langle>c\<rangle>\<guillemotright> C" and
     A: "nrm A = nrm C \<inter> 
              (dom (locals (store ((Norm s0)::state))) \<union> assigns_if False e)"
        "brk A = brk C"
      by (elim da_elim_cases) 
    from Loop.prems
    obtain 
       wt_e: "Env\<turnstile>e\<Colon>-PrimT Boolean" and 
       wt_c: "Env\<turnstile>c\<Colon>\<surd>"
      by (elim wt_elim_cases)
    from wt_e da_e G
    obtain res_s1: "?ResAssigned (Norm s0) s1"  
      by (elim Loop.hyps [elim_format]) simp+
    from Loop.hyps have
      s0_s1:"dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by (elim dom_locals_eval_mono_elim)
    show ?case
    proof (cases "normal s1")
      case True
      note normal_s1 = this
      show ?thesis
      proof (cases "the_Bool b")
	case True  
	with Loop.hyps obtain
          eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" and 
          eval_while: "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	  by simp
	from Loop.hyps True 
	have "?HypObj (In1r c) s1 s2" by simp
	note hyp_c = this [rule_format]
	from Loop.hyps True
	have "?HypObj (In1r (l\<bullet> While(e) c)) (abupd (absorb (Cont l)) s2) s3"
	  by simp
	note hyp_while = this [rule_format]
	from eval_e normal_s1 wt_e
	have "assigns_if True e \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx [elim_format]) (simp add: True)
	with s0_s1
	have "dom (locals (store ((Norm s0)::state))) \<union> assigns_if True e \<subseteq> \<dots>"
	  by (rule Un_least)
	with da_c obtain C'
	  where da_c': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>c\<rangle>\<guillemotright> C'" and
	     nrm_C_C': "nrm C \<subseteq> nrm C'"                  and
             brk_C_C': "\<forall> l. brk C l \<subseteq> brk C' l"
          by (rule da_weakenE) rules
	from hyp_c wt_c da_c'
	obtain nrm_C': "?NormalAssigned s2 C'" and 
          brk_C': "?BreakAssigned s1 s2 C'" and
          res_s2: "?ResAssigned s1 s2"
	  using G by simp
	show ?thesis
	proof (cases "normal s2 \<or> abrupt s2 = Some (Jump (Cont l))")
	  case True
	  from Loop.prems obtain
	    wt_while: "Env\<turnstile>In1r (l\<bullet> While(e) c)\<Colon>T" and
            da_while: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) 
                           \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A"
	    by simp
	  have "dom (locals (store ((Norm s0)::state)))
                  \<subseteq> dom (locals (store (abupd (absorb (Cont l)) s2)))"
	  proof -
	    note s0_s1
	    also from eval_c 
	    have "dom (locals (store s1)) \<subseteq> dom (locals (store s2))"
	      by (rule dom_locals_eval_mono_elim)
	    also have "\<dots> \<subseteq> dom (locals (store (abupd (absorb (Cont l)) s2)))"
	      by simp
	    finally show ?thesis .
	  qed
	  with da_while obtain A'
	    where 
	    da_while': "Env\<turnstile> dom (locals (store (abupd (absorb (Cont l)) s2))) 
                       \<guillemotright>\<langle>l\<bullet> While(e) c\<rangle>\<guillemotright> A'" 
	    and  nrm_A_A': "nrm A \<subseteq> nrm A'"                  
            and  brk_A_A': "\<forall> l. brk A l \<subseteq> brk A' l"
	    by (rule da_weakenE) simp
	  with wt_while hyp_while
	  obtain nrm_A': "?NormalAssigned s3 A'" and
                 brk_A': "?BreakAssigned (abupd (absorb (Cont l)) s2) s3 A'" and
                 res_s3: "?ResAssigned (abupd (absorb (Cont l)) s2) s3"
	    using G by simp 
	  from nrm_A_A' nrm_A'
	  have "?NormalAssigned s3 A" 
	    by blast
	  moreover 
	  have "?BreakAssigned (Norm s0) s3 A" 
	  proof -
	    from brk_A_A' brk_A' 
	    have "?BreakAssigned (abupd (absorb (Cont l)) s2) s3 A" 
	      by fastsimp
	    moreover
	    from True have "normal (abupd (absorb (Cont l)) s2)"
	      by (cases s2) auto
	    ultimately show ?thesis
	      by simp
	  qed
	  moreover from res_s3 True have "?ResAssigned (Norm s0) s3"
	    by auto
	  ultimately show ?thesis by (intro conjI)
	next
	  case False
	  then obtain abr where 
	    "abrupt s2 = Some abr" and
	    "abrupt (abupd (absorb (Cont l)) s2) = Some abr"
	    by auto
	  with eval_while 
	  have eq_s3_s2: "s3=s2"
	    by auto
	  with nrm_C_C' nrm_C' A
	  have "?NormalAssigned s3 A"
	    by fastsimp
	  moreover
	  from eq_s3_s2 brk_C_C' brk_C' normal_s1 A
	  have "?BreakAssigned (Norm s0) s3 A"
	    by fastsimp
	  moreover 
	  from eq_s3_s2 res_s2 normal_s1 have "?ResAssigned (Norm s0) s3"
	    by simp
	  ultimately show ?thesis by (intro conjI)
	qed
      next
	case False
	with Loop.hyps have eq_s3_s1: "s3=s1"
	  by simp
	from eq_s3_s1 res_s1 
	have res_s3: "?ResAssigned (Norm s0) s3"
	  by simp
	from eval_e True wt_e
	have "assigns_if False e \<subseteq> dom (locals (store s1))"
	  by (rule assigns_if_good_approx [elim_format]) (simp add: False)
	with s0_s1
	have "dom (locals (store ((Norm s0)::state)))\<union>assigns_if False e \<subseteq> \<dots>"
	  by (rule Un_least)
	hence "nrm C \<inter> 
               (dom (locals (store ((Norm s0)::state))) \<union> assigns_if False e)
               \<subseteq> dom (locals (store s1))"
	  by (rule subset_Intr)
	with normal_s1 A eq_s3_s1
	have "?NormalAssigned s3 A"
	  by simp
	moreover
	from normal_s1 eq_s3_s1
	have "?BreakAssigned (Norm s0) s3 A"
	  by simp
	moreover note res_s3
	ultimately show ?thesis by (intro conjI)
      qed
    next
      case False
      then obtain abr where abr: "abrupt s1 = Some abr"
	by (cases s1) auto
      moreover
      from eval_e _ wt_e have no_jmp: "\<And> j. abrupt s1 \<noteq> Some (Jump j)"
	by (rule eval_expression_no_jump) (simp_all add: wf G)
      moreover
      have eq_s3_s1: "s3=s1"
      proof (cases "the_Bool b")
	case True  
	with Loop.hyps obtain
          eval_c: "G\<turnstile>s1 \<midarrow>c\<rightarrow> s2" and 
          eval_while: "G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3"
	  by simp
	from eval_c abr have "s2=s1" by auto
	moreover from calculation no_jmp have "abupd (absorb (Cont l)) s2=s2"
	  by (cases s1) (simp add: absorb_def)
	ultimately show ?thesis
	  using eval_while abr
	  by auto
      next
	case False
	with Loop.hyps show ?thesis by simp
      qed
      moreover
      from eq_s3_s1 res_s1 
      have res_s3: "?ResAssigned (Norm s0) s3"
	by simp
      ultimately show ?thesis
	by simp 
    qed
  next 
    case (Jmp j s Env T A)
    have "?NormalAssigned (Some (Jump j),s) A" by simp
    moreover
    from Jmp.prems
    obtain ret: "j = Ret \<longrightarrow> Result \<in> dom (locals (store (Norm s)))" and
           brk: "brk A = (case j of
                           Break l \<Rightarrow> \<lambda> k. if k=l 
                                     then dom (locals (store ((Norm s)::state)))
                                     else UNIV     
                         | Cont l  \<Rightarrow> \<lambda> k. UNIV
                         | Ret     \<Rightarrow> \<lambda> k. UNIV)"
      by (elim da_elim_cases) simp
    from brk have "?BreakAssigned (Norm s) (Some (Jump j),s) A"
      by simp
    moreover from ret have "?ResAssigned (Norm s) (Some (Jump j),s)"
      by simp
    ultimately show ?case by (intro conjI)
  next
    case (Throw a e s0 s1 Env T A)
    have G: "prg Env = G" .
    from Throw.prems obtain E where 
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> E"
      by (elim da_elim_cases)
    from Throw.prems
      obtain eT where wt_e: "Env\<turnstile>e\<Colon>-eT"
	by (elim wt_elim_cases)
    have "?NormalAssigned (abupd (throw a) s1) A"
      by (cases s1) (simp add: throw_def)
    moreover
    have "?BreakAssigned (Norm s0) (abupd (throw a) s1) A"
    proof -
      from G Throw.hyps have eval_e: "prg Env\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<rightarrow> s1" 
	by (simp (no_asm_simp))
      from eval_e _ wt_e 
      have "\<And> l. abrupt s1 \<noteq> Some (Jump (Break l))"
	by (rule eval_expression_no_jump) (simp_all add: wf G) 
      hence "\<And> l. abrupt (abupd (throw a) s1) \<noteq> Some (Jump (Break l))"
	by (cases s1) (simp add: throw_def abrupt_if_def)
      thus ?thesis
	by simp
    qed
    moreover
    from wt_e da_e G have "?ResAssigned (Norm s0) s1"
      by (elim Throw.hyps [elim_format]) simp+
    hence "?ResAssigned (Norm s0) (abupd (throw a) s1)"
      by (cases s1) (simp add: throw_def abrupt_if_def)
    ultimately show ?case by (intro conjI)
  next
    case (Try C c1 c2 s0 s1 s2 s3 vn Env T A)
    have G: "prg Env = G" .
    from Try.prems obtain C1 C2 where
      da_c1: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1"  and
      da_c2:
       "Env\<lparr>lcl := lcl Env(VName vn\<mapsto>Class C)\<rparr>
        \<turnstile> (dom (locals (store ((Norm s0)::state))) \<union> {VName vn}) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2" and
      A: "nrm A = nrm C1 \<inter> nrm C2" "brk A = brk C1 \<Rightarrow>\<inter> brk C2"
      by (elim da_elim_cases) simp
    from Try.prems obtain 
      wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "Env\<lparr>lcl := lcl Env(VName vn\<mapsto>Class C)\<rparr>\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases)
    have sxalloc: "prg Env\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" using Try.hyps G 
      by (simp (no_asm_simp))
    have "PROP ?Hyp (In1r c1) (Norm s0) s1" .
    with wt_c1 da_c1 G
    obtain nrm_C1: "?NormalAssigned s1 C1" and
           brk_C1: "?BreakAssigned (Norm s0) s1 C1" and
           res_s1: "?ResAssigned (Norm s0) s1"
      by simp
    show ?case
    proof (cases "normal s1")
      case True
      with nrm_C1 have "nrm C1 \<inter> nrm C2 \<subseteq> dom (locals (store s1))"
	by auto
      moreover
      have "s3=s1"
      proof -
	from sxalloc True have eq_s2_s1: "s2=s1"
	  by (cases s1) (auto elim: sxalloc_elim_cases)
	with True have "\<not>  G,s2\<turnstile>catch C"
	  by (simp add: catch_def)
	with Try.hyps have "s3=s2"
	  by simp
	with eq_s2_s1 show ?thesis by simp
      qed
      ultimately show ?thesis
	using True A res_s1 by simp
    next
      case False
      note not_normal_s1 = this
      show ?thesis
      proof (cases "\<exists> l. abrupt s1 = Some (Jump (Break l))")
	case True
	then obtain l where l: "abrupt s1 = Some (Jump (Break l))"
	  by auto
	with brk_C1 have "(brk C1 \<Rightarrow>\<inter> brk C2) l \<subseteq> dom (locals (store s1))"
	  by auto
	moreover have "s3=s1"
	proof -
	  from sxalloc l have eq_s2_s1: "s2=s1"
	    by (cases s1) (auto elim: sxalloc_elim_cases)
	  with l have "\<not>  G,s2\<turnstile>catch C"
	    by (simp add: catch_def)
	  with Try.hyps have "s3=s2"
	    by simp
	  with eq_s2_s1 show ?thesis by simp
	qed
	ultimately show ?thesis
	  using l A res_s1 by simp
      next
	case False
	note abrupt_no_break = this
	show ?thesis
	proof (cases "G,s2\<turnstile>catch C")
	  case True
	  with Try.hyps have "?HypObj (In1r c2) (new_xcpt_var vn s2) s3"
            by simp
          note hyp_c2 = this [rule_format]
          have "(dom (locals (store ((Norm s0)::state))) \<union> {VName vn}) 
                  \<subseteq> dom (locals (store (new_xcpt_var vn s2)))"
          proof -
            have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1" .
            hence "dom (locals (store ((Norm s0)::state))) 
                    \<subseteq> dom (locals (store s1))"
              by (rule dom_locals_eval_mono_elim)
            also
            from sxalloc
            have "\<dots> \<subseteq> dom (locals (store s2))"
              by (rule dom_locals_sxalloc_mono)
            also 
            have "\<dots> \<subseteq> dom (locals (store (new_xcpt_var vn s2)))" 
              by (cases s2) (simp add: new_xcpt_var_def, blast) 
            also
            have "{VName vn} \<subseteq> \<dots>"
              by (cases s2) simp
            ultimately show ?thesis
              by (rule Un_least)
          qed
          with da_c2 
          obtain C2' where
            da_C2': "Env\<lparr>lcl := lcl Env(VName vn\<mapsto>Class C)\<rparr>
                     \<turnstile> dom (locals (store (new_xcpt_var vn s2))) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'"
           and nrm_C2': "nrm C2 \<subseteq> nrm C2'" 
           and brk_C2': "\<forall> l. brk C2 l \<subseteq> brk C2' l"
            by (rule da_weakenE) simp
          from wt_c2 da_C2' G and hyp_c2
          obtain nrmAss_C2: "?NormalAssigned s3 C2'" and
                 brkAss_C2: "?BreakAssigned (new_xcpt_var vn s2) s3 C2'" and
                 resAss_s3: "?ResAssigned (new_xcpt_var vn s2) s3"
            by simp
          from nrmAss_C2 nrm_C2' A 
          have "?NormalAssigned s3 A"
            by auto
          moreover
          have "?BreakAssigned (Norm s0) s3 A"
          proof -
            from brkAss_C2 have "?BreakAssigned (Norm s0) s3 C2'"
              by (cases s2) (auto simp add: new_xcpt_var_def)
            with brk_C2' A show ?thesis 
              by fastsimp
          qed
	  moreover
	  from resAss_s3 have "?ResAssigned (Norm s0) s3"
	    by (cases s2) ( simp add: new_xcpt_var_def)
          ultimately show ?thesis by (intro conjI)
        next
          case False
          with Try.hyps 
          have eq_s3_s2: "s3=s2" by simp
          moreover from sxalloc not_normal_s1 abrupt_no_break
          obtain "\<not> normal s2" 
                 "\<forall> l. abrupt s2 \<noteq> Some (Jump (Break l))"
            by - (rule sxalloc_cases,auto)
	  ultimately obtain 
	    "?NormalAssigned s3 A" and "?BreakAssigned (Norm s0) s3 A"
	    by (cases s2) auto
	  moreover have "?ResAssigned (Norm s0) s3"
	  proof (cases "abrupt s1 = Some (Jump Ret)")
	    case True
	    with sxalloc have "s2=s1"
	      by (elim sxalloc_cases) auto
	    with res_s1 eq_s3_s2 show ?thesis by simp
	  next
	    case False
	    with sxalloc
	    have "abrupt s2 \<noteq> Some (Jump Ret)"
	      by (rule sxalloc_no_jump) 
	    with eq_s3_s2 show ?thesis
	      by simp
	  qed
          ultimately show ?thesis by (intro conjI)
        qed
      qed
    qed
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Fin c1 c2 s0 s1 s2 s3 x1 Env T A)
    have G: "prg Env = G" .
    from Fin.prems obtain C1 C2 where 
      da_C1: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>c1\<rangle>\<guillemotright> C1" and
      da_C2: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2" and
      nrm_A: "nrm A = nrm C1 \<union> nrm C2" and
      brk_A: "brk A = ((brk C1) \<Rightarrow>\<union>\<^sub>\<forall> (nrm C2)) \<Rightarrow>\<inter> (brk C2)"
      by (elim da_elim_cases) simp
    from Fin.prems obtain 
      wt_c1: "Env\<turnstile>c1\<Colon>\<surd>" and
      wt_c2: "Env\<turnstile>c2\<Colon>\<surd>"
      by (elim wt_elim_cases)
    have "PROP ?Hyp (In1r c1) (Norm s0) (x1,s1)" .
    with wt_c1 da_C1 G
    obtain nrmAss_C1: "?NormalAssigned (x1,s1) C1" and
           brkAss_C1: "?BreakAssigned (Norm s0) (x1,s1) C1" and
           resAss_s1: "?ResAssigned (Norm s0) (x1,s1)"
      by simp
    obtain nrmAss_C2: "?NormalAssigned s2 C2" and
           brkAss_C2: "?BreakAssigned (Norm s1) s2 C2" and
           resAss_s2: "?ResAssigned (Norm s1) s2"
    proof -
      from Fin.hyps
      have "dom (locals (store ((Norm s0)::state))) 
             \<subseteq> dom (locals (store (x1,s1)))"
        by - (rule dom_locals_eval_mono_elim) 
      with da_C2 obtain C2'
        where
        da_C2': "Env\<turnstile> dom (locals (store (x1,s1))) \<guillemotright>\<langle>c2\<rangle>\<guillemotright> C2'" and
        nrm_C2': "nrm C2 \<subseteq> nrm C2'" and
        brk_C2': "\<forall> l. brk C2 l \<subseteq> brk C2' l"
        by (rule da_weakenE) simp
      have "PROP ?Hyp (In1r c2) (Norm s1) s2" .
      with wt_c2 da_C2' G
      obtain nrmAss_C2': "?NormalAssigned s2 C2'" and
             brkAss_C2': "?BreakAssigned (Norm s1) s2 C2'" and
	     resAss_s2': "?ResAssigned (Norm s1) s2"
        by simp
      from nrmAss_C2' nrm_C2' have "?NormalAssigned s2 C2"
        by blast
      moreover
      from brkAss_C2' brk_C2' have "?BreakAssigned (Norm s1) s2 C2"
        by fastsimp
      ultimately
      show ?thesis
        using that resAss_s2' by simp
    qed
    have s3: "s3 = (if \<exists>err. x1 = Some (Error err) then (x1, s1)
                       else abupd (abrupt_if (x1 \<noteq> None) x1) s2)" .
    have s1_s2: "dom (locals s1) \<subseteq> dom (locals (store s2))"
    proof -  
      have "G\<turnstile>Norm s1 \<midarrow>c2\<rightarrow> s2" .
      thus ?thesis
        by (rule dom_locals_eval_mono_elim) simp
    qed

    have "?NormalAssigned s3 A"
    proof 
      assume normal_s3: "normal s3"
      show "nrm A \<subseteq> dom (locals (snd s3))"
      proof -
        have "nrm C1 \<subseteq> dom (locals (snd s3))"
        proof -
          from normal_s3 s3
          have "normal (x1,s1)"
            by (cases s2) (simp add: abrupt_if_def)
          with normal_s3 nrmAss_C1 s3 s1_s2
          show ?thesis
            by fastsimp
        qed
        moreover 
        have "nrm C2 \<subseteq> dom (locals (snd s3))"
        proof -
          from normal_s3 s3
          have "normal s2"
            by (cases s2) (simp add: abrupt_if_def)
          with normal_s3 nrmAss_C2 s3 s1_s2
          show ?thesis
            by fastsimp
        qed
        ultimately have "nrm C1 \<union> nrm C2 \<subseteq> \<dots>"
          by (rule Un_least)
        with nrm_A show ?thesis
          by simp
      qed
    qed
    moreover
    {
      fix l assume brk_s3: "abrupt s3 = Some (Jump (Break l))"
      have "brk A l \<subseteq> dom (locals (store s3))"
      proof (cases "normal s2")
        case True
        with brk_s3 s3 
        have s2_s3: "dom (locals (store s2)) \<subseteq> dom (locals (store s3))"
          by simp
        have "brk C1 l \<subseteq> dom (locals (store s3))"
        proof -
          from True brk_s3 s3 have "x1=Some (Jump (Break l))"
            by (cases s2) (simp add: abrupt_if_def)
          with brkAss_C1 s1_s2 s2_s3
          show ?thesis
            by simp (blast intro: subset_trans)
        qed
        moreover from True nrmAss_C2 s2_s3
        have "nrm C2 \<subseteq> dom (locals (store s3))"
          by - (rule subset_trans, simp_all)
        ultimately 
        have "((brk C1) \<Rightarrow>\<union>\<^sub>\<forall> (nrm C2)) l \<subseteq> \<dots>"
          by blast
        with brk_A show ?thesis
          by simp blast
      next
        case False
        note not_normal_s2 = this
        have "s3=s2"
        proof (cases "normal (x1,s1)")
          case True with not_normal_s2 s3 show ?thesis
            by (cases s2) (simp add: abrupt_if_def)
        next
          case False with not_normal_s2 s3 brk_s3 show ?thesis
            by (cases s2) (simp add: abrupt_if_def)
        qed
        with brkAss_C2 brk_s3
        have "brk C2 l \<subseteq> dom (locals (store s3))"
          by simp
        with brk_A show ?thesis
          by simp blast
      qed
    }
    hence "?BreakAssigned (Norm s0) s3 A"
      by simp
    moreover
    {
      assume abr_s3: "abrupt s3 = Some (Jump Ret)"
      have "Result \<in> dom (locals (store s3))"
      proof (cases "x1 = Some (Jump Ret)")
	case True
	note ret_x1 = this
	with resAss_s1 have res_s1: "Result \<in> dom (locals s1)"
	  by simp
	moreover have "dom (locals (store ((Norm s1)::state))) 
                         \<subseteq> dom (locals (store s2))"
	  by (rule dom_locals_eval_mono_elim)
	ultimately have "Result \<in> dom (locals (store s2))"
	  by - (rule subsetD,auto)
	with res_s1 s3 show ?thesis
	  by simp
      next
	case False
	with s3 abr_s3 obtain  "abrupt s2 = Some (Jump Ret)" and "s3=s2"
	  by (cases s2) (simp add: abrupt_if_def)
	with resAss_s2 show ?thesis
	  by simp
      qed
    }
    hence "?ResAssigned (Norm s0) s3"
      by simp
    ultimately show ?case by (intro conjI)
  next 
    case (Init C c s0 s1 s2 s3 Env T A)
    have G: "prg Env = G" .
    from Init.hyps
    have eval: "prg Env\<turnstile> Norm s0 \<midarrow>Init C\<rightarrow> s3"
      apply (simp only: G) 
      apply (rule eval.Init, assumption)
      apply (cases "inited C (globs s0) ")
      apply   simp
      apply (simp only: if_False )
      apply (elim conjE,intro conjI,assumption+,simp)
      done (* auto or simp alone always do too much *)
    have "the (class G C) = c" .
    with Init.prems 
    have c: "class G C = Some c"
      by (elim wt_elim_cases) auto
    from Init.prems obtain
       nrm_A: "nrm A = dom (locals (store ((Norm s0)::state)))"
      by (elim da_elim_cases) simp
    show ?case
    proof (cases "inited C (globs s0)")
      case True
      with Init.hyps have "s3=Norm s0" by simp
      thus ?thesis
	using nrm_A by simp
    next
      case False
      from Init.hyps False G
      obtain eval_initC: 
              "prg Env\<turnstile>Norm ((init_class_obj G C) s0) 
                       \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1" and
             eval_init: "prg Env\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<rightarrow> s2" and
             s3: "s3=(set_lvars (locals (store s1))) s2"
	by simp
      have "?NormalAssigned s3 A"
      proof
	show "nrm A \<subseteq> dom (locals (store s3))"
	proof -
	  from nrm_A have "nrm A \<subseteq> dom (locals (init_class_obj G C s0))"
	    by simp
	  also from eval_initC have "\<dots> \<subseteq> dom (locals (store s1))"
	    by (rule dom_locals_eval_mono_elim) simp
	  also from s3 have "\<dots> \<subseteq> dom (locals (store s3))"
	    by (cases s1) (cases s2, simp add: init_lvars_def2)
	  finally show ?thesis .
	qed
      qed
      moreover
      from eval 
      have "\<And> j. abrupt s3 \<noteq> Some (Jump j)"
	by (rule eval_statement_no_jump) (auto simp add: wf c G)
      then obtain "?BreakAssigned (Norm s0) s3 A" 
              and "?ResAssigned (Norm s0) s3"
	by simp
      ultimately show ?thesis by (intro conjI)
    qed
  next 
    case (NewC C a s0 s1 s2 Env T A)
    have G: "prg Env = G" .
    from NewC.prems
    obtain A: "nrm A = dom (locals (store ((Norm s0)::state)))"
              "brk A = (\<lambda> l. UNIV)"
      by (elim da_elim_cases) simp
    from wf NewC.prems 
    have wt_init: "Env\<turnstile>(Init C)\<Colon>\<surd>"
      by  (elim wt_elim_cases) (drule is_acc_classD,simp)
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s2))"
    proof -
      have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
        by (rule dom_locals_eval_mono_elim)
      also
      have "\<dots> \<subseteq> dom (locals (store s2))"
        by (rule dom_locals_halloc_mono)
      finally show ?thesis .
    qed
    with A have "?NormalAssigned s2 A"
      by simp
    moreover
    {
      fix j have "abrupt s2 \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile> Norm s0 \<midarrow>NewC C-\<succ>Addr a\<rightarrow> s2"
	  by (simp only: G) (rule eval.NewC)
        from NewC.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with NewC.prems have "Env\<turnstile>NewC C\<Colon>-T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    }
    hence "?BreakAssigned (Norm s0) s2 A" and "?ResAssigned (Norm s0) s2"
      by simp_all      
    ultimately show ?case by (intro conjI)
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (NewA elT a e i s0 s1 s2 s3 Env T A) 
    have G: "prg Env = G" .
    from NewA.prems obtain
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
      by (elim da_elim_cases)
    from NewA.prems obtain 
      wt_init: "Env\<turnstile>init_comp_ty elT\<Colon>\<surd>" and 
      wt_size: "Env\<turnstile>e\<Colon>-PrimT Integer"
      by (elim wt_elim_cases) (auto dest:  wt_init_comp_ty')
    have halloc:"G\<turnstile>abupd (check_neg i) s2\<midarrow>halloc Arr elT (the_Intg i)\<succ>a\<rightarrow>s3".
    have "dom (locals (store ((Norm s0)::state))) \<subseteq> dom (locals (store s1))"
      by (rule dom_locals_eval_mono_elim)
    with da_e obtain A' where
                da_e': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A'" 
        and  nrm_A_A': "nrm A \<subseteq> nrm A'"                  
        and  brk_A_A': "\<forall> l. brk A l \<subseteq> brk A' l"
      by (rule da_weakenE) simp
    have "PROP ?Hyp (In1l e) s1 s2" .
    with wt_size da_e' G obtain 
      nrmAss_A': "?NormalAssigned s2 A'" and
      brkAss_A': "?BreakAssigned s1 s2 A'"
      by simp
    have s2_s3: "dom (locals (store s2)) \<subseteq> dom (locals (store s3))"
    proof -
      have "dom (locals (store s2)) 
             \<subseteq> dom (locals (store (abupd (check_neg i) s2)))"
        by (simp)
      also have "\<dots> \<subseteq> dom (locals (store s3))"
        by (rule dom_locals_halloc_mono)
      finally show ?thesis .
    qed 
    have "?NormalAssigned s3 A"
    proof 
      assume normal_s3: "normal s3"
      show "nrm A \<subseteq> dom (locals (store s3))"
      proof -
        from halloc normal_s3 
        have "normal (abupd (check_neg i) s2)"
          by cases simp_all
        hence "normal s2"
          by (cases s2) simp
        with nrmAss_A' nrm_A_A' s2_s3 show ?thesis
          by blast
      qed
    qed
    moreover
    {
      fix j have "abrupt s3 \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile> Norm s0 \<midarrow>New elT[e]-\<succ>Addr a\<rightarrow> s3"
	  by (simp only: G) (rule eval.NewA)
        from NewA.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with NewA.prems have "Env\<turnstile>New elT[e]\<Colon>-T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    }
    hence "?BreakAssigned (Norm s0) s3 A" and "?ResAssigned (Norm s0) s3"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (Cast cT e s0 s1 s2 v Env T A)
    have G: "prg Env = G" .
    from Cast.prems obtain
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
      by (elim da_elim_cases)
    from Cast.prems obtain eT where
      wt_e: "Env\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases) 
    have "PROP ?Hyp (In1l e) (Norm s0) s1" .
    with wt_e da_e G obtain 
      nrmAss_A: "?NormalAssigned s1 A" and
      brkAss_A: "?BreakAssigned (Norm s0) s1 A"
      by simp
    have s2: "s2 = abupd (raise_if (\<not> G,snd s1\<turnstile>v fits cT) ClassCast) s1" .
    hence s1_s2: "dom (locals (store s1)) \<subseteq> dom (locals (store s2))"
      by simp
    have "?NormalAssigned s2 A"
    proof 
      assume "normal s2"
      with s2 have "normal s1"
        by (cases s1) simp
      with nrmAss_A s1_s2 
      show "nrm A \<subseteq> dom (locals (store s2))"
        by blast
    qed
    moreover
    {
      fix j have "abrupt s2 \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile> Norm s0 \<midarrow>Cast cT e-\<succ>v\<rightarrow> s2"
	  by (simp only: G) (rule eval.Cast)
        from Cast.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with Cast.prems have "Env\<turnstile>Cast cT e\<Colon>-T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    }
    hence "?BreakAssigned (Norm s0) s2 A" and "?ResAssigned (Norm s0) s2"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (Inst iT b e s0 s1 v Env T A)
    have G: "prg Env = G" .
    from Inst.prems obtain
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
      by (elim da_elim_cases)
    from Inst.prems obtain eT where
      wt_e: "Env\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases) 
    have "PROP ?Hyp (In1l e) (Norm s0) s1" .
    with wt_e da_e G obtain 
      "?NormalAssigned s1 A" and
      "?BreakAssigned (Norm s0) s1 A" and
      "?ResAssigned (Norm s0) s1"
      by simp
    thus ?case by (intro conjI)
  next
    case (Lit s v Env T A)
    from Lit.prems
    have "nrm A = dom (locals (store ((Norm s)::state)))"
      by (elim da_elim_cases) simp
    thus ?case by simp
  next
    case (UnOp e s0 s1 unop v Env T A)
     have G: "prg Env = G" .
    from UnOp.prems obtain
      da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
      by (elim da_elim_cases)
    from UnOp.prems obtain eT where
      wt_e: "Env\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases) 
    have "PROP ?Hyp (In1l e) (Norm s0) s1" .
    with wt_e da_e G obtain 
      "?NormalAssigned s1 A" and
      "?BreakAssigned (Norm s0) s1 A" and
      "?ResAssigned (Norm s0) s1"
      by simp
    thus ?case by (intro conjI)
  next
    case (BinOp binop e1 e2 s0 s1 s2 v1 v2 Env T A)
    have G: "prg Env = G". 
    from BinOp.hyps 
    have 
     eval: "prg Env\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>(eval_binop binop v1 v2)\<rightarrow> s2"
      by (simp only: G) (rule eval.BinOp)
    have s0_s1: "dom (locals (store ((Norm s0)::state))) 
                  \<subseteq> dom (locals (store s1))"
      by (rule dom_locals_eval_mono_elim)
    also have s1_s2: "dom (locals (store s1)) \<subseteq>  dom (locals (store s2))"
      by (rule dom_locals_eval_mono_elim)
    finally 
    have s0_s2: "dom (locals (store ((Norm s0)::state))) 
                  \<subseteq> dom (locals (store s2))" . 
    from BinOp.prems obtain e1T e2T
      where wt_e1: "Env\<turnstile>e1\<Colon>-e1T" 
       and  wt_e2: "Env\<turnstile>e2\<Colon>-e2T" 
       and  wt_binop: "wt_binop (prg Env) binop e1T e2T"
       and  T: "T=Inl (PrimT (binop_type binop))"
      by (elim wt_elim_cases) simp
    have "?NormalAssigned s2 A"
    proof 
      assume normal_s2: "normal s2"
      have   normal_s1: "normal s1"
        by (rule eval_no_abrupt_lemma [rule_format])
      show "nrm A \<subseteq> dom (locals (store s2))"
      proof (cases "binop=CondAnd")
        case True
        note CondAnd = this
        from BinOp.prems obtain
           nrm_A: "nrm A = dom (locals (store ((Norm s0)::state))) 
                            \<union> (assigns_if True (BinOp CondAnd e1 e2) \<inter> 
                                 assigns_if False (BinOp CondAnd e1 e2))"
          by (elim da_elim_cases) (simp_all add: CondAnd)
        from T BinOp.prems CondAnd
        have "Env\<turnstile>BinOp binop e1 e2\<Colon>-PrimT Boolean"
          by (simp)
        with eval normal_s2
        have ass_if: "assigns_if (the_Bool (eval_binop binop v1 v2)) 
                                 (BinOp binop e1 e2)
                        \<subseteq> dom (locals (store s2))"
          by (rule assigns_if_good_approx) 
        have "(assigns_if True (BinOp CondAnd e1 e2) \<inter> 
                         assigns_if False (BinOp CondAnd e1 e2)) \<subseteq> \<dots>"
        proof (cases "the_Bool (eval_binop binop v1 v2)")
          case True
          with ass_if CondAnd  
          have "assigns_if True (BinOp CondAnd e1 e2) 
                 \<subseteq> dom (locals (store s2))"
	    by simp
          thus ?thesis by blast
        next
          case False
          with ass_if CondAnd
          have "assigns_if False (BinOp CondAnd e1 e2) 
                 \<subseteq> dom (locals (store s2))"
            by (simp only: False)
          thus ?thesis by blast
        qed
        with s0_s2
        have "dom (locals (store ((Norm s0)::state))) 
                \<union> (assigns_if True (BinOp CondAnd e1 e2) \<inter> 
                   assigns_if False (BinOp CondAnd e1 e2)) \<subseteq> \<dots>"
          by (rule Un_least)
        thus ?thesis by (simp only: nrm_A)
      next
        case False
        note notCondAnd = this
        show ?thesis
        proof (cases "binop=CondOr")
          case True
          note CondOr = this
          from BinOp.prems obtain
            nrm_A: "nrm A = dom (locals (store ((Norm s0)::state))) 
                             \<union> (assigns_if True (BinOp CondOr e1 e2) \<inter> 
                                 assigns_if False (BinOp CondOr e1 e2))"
            by (elim da_elim_cases) (simp_all add: CondOr)
          from T BinOp.prems CondOr
          have "Env\<turnstile>BinOp binop e1 e2\<Colon>-PrimT Boolean"
            by (simp)
          with eval normal_s2
          have ass_if: "assigns_if (the_Bool (eval_binop binop v1 v2)) 
                                 (BinOp binop e1 e2)
                          \<subseteq> dom (locals (store s2))"
            by (rule assigns_if_good_approx) 
          have "(assigns_if True (BinOp CondOr e1 e2) \<inter> 
                         assigns_if False (BinOp CondOr e1 e2)) \<subseteq> \<dots>"
          proof (cases "the_Bool (eval_binop binop v1 v2)")
            case True
            with ass_if CondOr 
            have "assigns_if True (BinOp CondOr e1 e2) 
                    \<subseteq> dom (locals (store s2))"
              by (simp)
            thus ?thesis by blast
          next
            case False
            with ass_if CondOr
            have "assigns_if False (BinOp CondOr e1 e2) 
                    \<subseteq> dom (locals (store s2))"
              by (simp)
            thus ?thesis by blast
          qed
          with s0_s2
          have "dom (locals (store ((Norm s0)::state))) 
                 \<union> (assigns_if True (BinOp CondOr e1 e2) \<inter> 
                    assigns_if False (BinOp CondOr e1 e2)) \<subseteq> \<dots>"
            by (rule Un_least)
          thus ?thesis by (simp only: nrm_A)
        next
          case False
          with notCondAnd obtain notAndOr: "binop\<noteq>CondAnd" "binop\<noteq>CondOr"
            by simp
          from BinOp.prems obtain E1
            where da_e1: "Env\<turnstile> dom (locals (snd (Norm s0))) \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1"  
             and  da_e2: "Env\<turnstile> nrm E1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A"
            by (elim da_elim_cases) (simp_all add: notAndOr)
          have "PROP ?Hyp (In1l e1) (Norm s0) s1" .
          with wt_e1 da_e1 G normal_s1
          obtain "?NormalAssigned s1 E1"  
            by simp
          with normal_s1 have "nrm E1 \<subseteq> dom (locals (store s1))" by rules
          with da_e2 obtain A' 
            where  da_e2': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A'" and
                 nrm_A_A': "nrm A \<subseteq> nrm A'"                  
            by (rule da_weakenE) rules
          from notAndOr have "need_second_arg binop v1" by simp
          with BinOp.hyps 
          have "PROP ?Hyp (In1l e2) s1 s2" by simp
          with wt_e2 da_e2' G
          obtain "?NormalAssigned s2 A'"  
            by simp
          with nrm_A_A' normal_s2
          show "nrm A \<subseteq> dom (locals (store s2))" 
            by blast
        qed
      qed
    qed
    moreover
    {
      fix j have "abrupt s2 \<noteq> Some (Jump j)"
      proof -
        from BinOp.prems T 
        have "Env\<turnstile>In1l (BinOp binop e1 e2)\<Colon>Inl (PrimT (binop_type binop))"
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf) 
      qed
    }
    hence "?BreakAssigned (Norm s0) s2 A" and "?ResAssigned (Norm s0) s2"
      by simp_all
    ultimately show ?case by (intro conjI) 
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Super s Env T A)
    from Super.prems
    have "nrm A = dom (locals (store ((Norm s)::state)))"
      by (elim da_elim_cases) simp
    thus ?case by simp
  next
    case (Acc upd s0 s1 w v Env T A)
    show ?case
    proof (cases "\<exists> vn. v = LVar vn")
      case True
      then obtain vn where vn: "v=LVar vn"..
      from Acc.prems
      have "nrm A = dom (locals (store ((Norm s0)::state)))"
        by (simp only: vn) (elim da_elim_cases,simp_all)
      moreover have "G\<turnstile>Norm s0 \<midarrow>v=\<succ>(w, upd)\<rightarrow> s1" .
      hence "s1=Norm s0"
        by (simp only: vn) (elim eval_elim_cases,simp)
      ultimately show ?thesis by simp
    next
      case False
      have G: "prg Env = G" .
      from False Acc.prems
      have da_v: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>v\<rangle>\<guillemotright> A"
        by (elim da_elim_cases) simp_all 
      from Acc.prems obtain vT where
        wt_v: "Env\<turnstile>v\<Colon>=vT"
        by (elim wt_elim_cases) 
      have "PROP ?Hyp (In2 v) (Norm s0) s1" .
      with wt_v da_v G obtain 
        "?NormalAssigned s1 A" and
        "?BreakAssigned (Norm s0) s1 A" and
	"?ResAssigned (Norm s0) s1"
        by simp
      thus ?thesis by (intro conjI)
    qed
  next
    case (Ass e upd s0 s1 s2 v var w Env T A)
    have G: "prg Env = G" .
    from Ass.prems obtain varT eT where
      wt_var: "Env\<turnstile>var\<Colon>=varT" and
      wt_e:   "Env\<turnstile>e\<Colon>-eT"
      by (elim wt_elim_cases) simp
    have eval_var: "prg Env\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, upd)\<rightarrow> s1" 
      using Ass.hyps by (simp only: G)
    have "?NormalAssigned (assign upd v s2) A"
    proof 
      assume normal_ass_s2: "normal (assign upd v s2)"
      from normal_ass_s2 
      have normal_s2: "normal s2"
        by (cases s2) (simp add: assign_def Let_def)
      hence normal_s1: "normal s1"
        by - (rule eval_no_abrupt_lemma [rule_format])
      have hyp_var: "PROP ?Hyp (In2 var) (Norm s0) s1" .
      have hyp_e: "PROP ?Hyp (In1l e) s1 s2" .
      show "nrm A \<subseteq> dom (locals (store (assign upd v s2)))"
      proof (cases "\<exists> vn. var = LVar vn")
	case True
	then obtain vn where vn: "var=LVar vn"..
	from Ass.prems obtain E where
	  da_e: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>e\<rangle>\<guillemotright> E" and
	  nrm_A: "nrm A = nrm E \<union> {vn}"
	  by (elim da_elim_cases) (insert vn,auto)
	obtain E' where
	  da_e': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<guillemotright> E'" and
	  E_E': "nrm E \<subseteq> nrm E'"
	proof -
	  have "dom (locals (store ((Norm s0)::state))) 
                  \<subseteq> dom (locals (store s1))"
	    by (rule dom_locals_eval_mono_elim)
	  with da_e show ?thesis
	    by (rule da_weakenE)
	qed
	from G eval_var vn 
	have eval_lvar: "G\<turnstile>Norm s0 \<midarrow>LVar vn=\<succ>(w, upd)\<rightarrow> s1" 
	  by simp
	then have upd: "upd = snd (lvar vn (store s1))"
	  by cases (cases "lvar vn (store s1)",simp)
	have "nrm E \<subseteq> dom (locals (store (assign upd v s2)))"
	proof -
	  from hyp_e wt_e da_e' G normal_s2
	  have "nrm E' \<subseteq> dom (locals (store s2))"
	    by simp
	  also
	  from upd
	  have "dom (locals (store s2))  \<subseteq> dom (locals (store (upd v s2)))"
	    by (simp add: lvar_def) blast
	  hence "dom (locals (store s2)) 
	             \<subseteq> dom (locals (store (assign upd v s2)))"
	    by (rule dom_locals_assign_mono)
	  finally
	  show ?thesis using E_E' 
	    by blast
	qed
	moreover
	from upd normal_s2
	have "{vn} \<subseteq> dom (locals (store (assign upd v s2)))"
	  by (auto simp add: assign_def Let_def lvar_def upd split: split_split)
	ultimately
	show "nrm A \<subseteq> \<dots>"
	  by (rule Un_least [elim_format]) (simp add: nrm_A)
      next
	case False
	from Ass.prems obtain V where
	  da_var: "Env\<turnstile> dom (locals (store ((Norm s0)::state))) \<guillemotright>\<langle>var\<rangle>\<guillemotright> V" and
	  da_e:   "Env\<turnstile> nrm V \<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
	  by (elim da_elim_cases) (insert False,simp+)
        from hyp_var wt_var da_var G normal_s1
        have "nrm V \<subseteq> dom (locals (store s1))"
          by simp
        with da_e obtain A' 
          where  da_e': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A'" and
                 nrm_A_A': "nrm A \<subseteq> nrm A'"                  
          by (rule da_weakenE) rules
        from hyp_e wt_e da_e' G normal_s2
        obtain "nrm A' \<subseteq> dom (locals (store s2))"   
          by simp
        with nrm_A_A' have "nrm A \<subseteq> \<dots>" 
          by blast
        also have "\<dots> \<subseteq> dom (locals (store (assign upd v s2)))"
        proof -
          from eval_var normal_s1
          have "dom (locals (store s2)) \<subseteq> dom (locals (store (upd v s2)))"
            by (cases rule: dom_locals_eval_mono_elim)
               (cases s2, simp)
          thus ?thesis
            by (rule dom_locals_assign_mono)
        qed
        finally show ?thesis .
      qed
    qed
    moreover 
    {
      fix j have "abrupt (assign upd v s2) \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile>Norm s0 \<midarrow>var:=e-\<succ>v\<rightarrow> (assign upd v s2)"
          by (simp only: G) (rule eval.Ass)
        from Ass.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with Ass.prems have "Env\<turnstile>var:=e\<Colon>-T'" by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    }
    hence "?BreakAssigned (Norm s0) (assign upd v s2) A"
      and "?ResAssigned (Norm s0) (assign upd v s2)"       
      by simp_all
    ultimately show ?case by (intro conjI)
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (Cond b e0 e1 e2 s0 s1 s2 v Env T A)
    have G: "prg Env = G" .
    have "?NormalAssigned s2 A"
    proof 
      assume normal_s2: "normal s2"
      show "nrm A \<subseteq> dom (locals (store s2))"
      proof (cases "Env\<turnstile>(e0 ? e1 : e2)\<Colon>-(PrimT Boolean)")
        case True
        with Cond.prems 
        have nrm_A: "nrm A = dom (locals (store ((Norm s0)::state))) 
                             \<union> (assigns_if True  (e0 ? e1 : e2) \<inter> 
                                 assigns_if False (e0 ? e1 : e2))"
          by (elim da_elim_cases) simp_all
        have eval: "prg Env\<turnstile>Norm s0 \<midarrow>(e0 ? e1 : e2)-\<succ>v\<rightarrow> s2"
          by (simp only: G) (rule eval.Cond)
        from eval 
        have "dom (locals (store ((Norm s0)::state)))\<subseteq>dom (locals (store s2))"
          by (rule dom_locals_eval_mono_elim)
        moreover
        from eval normal_s2 True
        have ass_if: "assigns_if (the_Bool v) (e0 ? e1 : e2)
                        \<subseteq> dom (locals (store s2))"
          by (rule assigns_if_good_approx)
        have "assigns_if True  (e0 ? e1:e2) \<inter> assigns_if False (e0 ? e1:e2)
               \<subseteq> dom (locals (store s2))"
        proof (cases "the_Bool v")
          case True 
          from ass_if 
          have "assigns_if True  (e0 ? e1:e2) \<subseteq> dom (locals (store s2))"
            by (simp only: True)
          thus ?thesis by blast
        next
          case False 
          from ass_if 
          have "assigns_if False  (e0 ? e1:e2) \<subseteq> dom (locals (store s2))"
            by (simp only: False)
          thus ?thesis by blast
        qed
        ultimately show "nrm A \<subseteq> dom (locals (store s2))"
          by (simp only: nrm_A) (rule Un_least)
      next
        case False
        with Cond.prems obtain E1 E2 where
         da_e1: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                         \<union> assigns_if True e0) \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1" and
         da_e2: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))) 
                        \<union> assigns_if False e0) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2" and
         nrm_A: "nrm A = nrm E1 \<inter> nrm E2"
          by (elim da_elim_cases) simp_all
        from Cond.prems obtain e1T e2T where
          wt_e0: "Env\<turnstile>e0\<Colon>- PrimT Boolean" and
          wt_e1: "Env\<turnstile>e1\<Colon>-e1T" and
          wt_e2: "Env\<turnstile>e2\<Colon>-e2T" 
          by (elim wt_elim_cases)
        have s0_s1: "dom (locals (store ((Norm s0)::state))) 
                       \<subseteq> dom (locals (store s1))"
          by (rule dom_locals_eval_mono_elim)
        have eval_e0: "prg Env\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<rightarrow> s1" by (simp only: G)
        have normal_s1: "normal s1"
          by (rule eval_no_abrupt_lemma [rule_format])
        show ?thesis
        proof (cases "the_Bool b")
          case True
          from True Cond.hyps have "PROP ?Hyp (In1l e1) s1 s2" by simp
          moreover
          from eval_e0 normal_s1 wt_e0
          have "assigns_if True e0 \<subseteq> dom (locals (store s1))"
            by (rule assigns_if_good_approx [elim_format]) (simp only: True)
          with s0_s1 
          have "dom (locals (store ((Norm s0)::state))) 
                 \<union> assigns_if True e0 \<subseteq> \<dots>"
            by (rule Un_least)
          with da_e1 obtain E1' where
                  da_e1': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1'" and
              nrm_E1_E1': "nrm E1 \<subseteq> nrm E1'"
            by (rule da_weakenE) rules
          ultimately have "nrm E1' \<subseteq> dom (locals (store s2))"
            using wt_e1 G normal_s2 by simp 
          with nrm_E1_E1' show ?thesis
            by (simp only: nrm_A) blast
        next
          case False
          from False Cond.hyps have "PROP ?Hyp (In1l e2) s1 s2" by simp
          moreover
          from eval_e0 normal_s1 wt_e0
          have "assigns_if False e0 \<subseteq> dom (locals (store s1))"
            by (rule assigns_if_good_approx [elim_format]) (simp only: False)
          with s0_s1 
          have "dom (locals (store ((Norm s0)::state))) 
                 \<union> assigns_if False e0 \<subseteq> \<dots>"
            by (rule Un_least)
          with da_e2 obtain E2' where
                  da_e2': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> E2'" and
              nrm_E2_E2': "nrm E2 \<subseteq> nrm E2'"
            by (rule da_weakenE) rules
          ultimately have "nrm E2' \<subseteq> dom (locals (store s2))"
            using wt_e2 G normal_s2 by simp 
          with nrm_E2_E2' show ?thesis
            by (simp only: nrm_A) blast
        qed
      qed
    qed
    moreover
    {
      fix j have "abrupt s2 \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<rightarrow> s2"
          by (simp only: G) (rule eval.Cond)
        from Cond.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with Cond.prems have "Env\<turnstile>e0 ? e1 : e2\<Colon>-T'" by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    } 
    hence "?BreakAssigned (Norm s0) s2 A" and "?ResAssigned (Norm s0) s2"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (Call D a accC args e mn mode pTs s0 s1 s2 s3 s3' s4 statT v vs 
           Env T A)
    have G: "prg Env = G" .
    have "?NormalAssigned (restore_lvars s2 s4) A"
    proof 
      assume normal_restore_lvars: "normal (restore_lvars s2 s4)"
      show "nrm A \<subseteq> dom (locals (store (restore_lvars s2 s4)))"
      proof -
        from Call.prems obtain E where
             da_e: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>\<langle>e\<rangle>\<guillemotright> E" and
          da_args: "Env\<turnstile> nrm E \<guillemotright>\<langle>args\<rangle>\<guillemotright> A" 
          by (elim da_elim_cases)
        from Call.prems obtain eT argsT where
             wt_e: "Env\<turnstile>e\<Colon>-eT" and
          wt_args: "Env\<turnstile>args\<Colon>\<doteq>argsT"
          by (elim wt_elim_cases)
        have s3: "s3 = init_lvars G D \<lparr>name = mn, parTs = pTs\<rparr> mode a vs s2" .
        have s3': "s3' = check_method_access G accC statT mode 
                                           \<lparr>name=mn,parTs=pTs\<rparr> a s3" .
        have normal_s2: "normal s2"
        proof -
          from normal_restore_lvars have "normal s4"
            by simp
          then have "normal s3'"
            by - (rule eval_no_abrupt_lemma [rule_format])
          with s3' have "normal s3"
            by (cases s3) (simp add: check_method_access_def Let_def)
          with s3 show "normal s2"
            by (cases s2) (simp add: init_lvars_def Let_def)
        qed
        then have normal_s1: "normal s1"
          by  - (rule eval_no_abrupt_lemma [rule_format])
        have "PROP ?Hyp (In1l e) (Norm s0) s1" .
        with da_e wt_e G normal_s1
        have "nrm E \<subseteq> dom (locals (store s1))"
          by simp
        with da_args obtain A' where
          da_args': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>args\<rangle>\<guillemotright> A'" and
          nrm_A_A': "nrm A \<subseteq> nrm A'"
          by (rule da_weakenE) rules
        have "PROP ?Hyp (In3 args) s1 s2" .
        with da_args' wt_args G normal_s2
        have "nrm A' \<subseteq> dom (locals (store s2))"
          by simp
        with nrm_A_A' have "nrm A \<subseteq> dom (locals (store s2))"
          by blast
        also have "\<dots> \<subseteq> dom (locals (store (restore_lvars s2 s4)))"
          by (cases s4) simp
        finally show ?thesis .
      qed
    qed
    moreover
    {
      fix j have "abrupt (restore_lvars s2 s4) \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile>Norm s0 \<midarrow>({accC,statT,mode}e\<cdot>mn( {pTs}args))-\<succ>v
                            \<rightarrow> (restore_lvars s2 s4)"
          by (simp only: G) (rule eval.Call)
        from Call.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with Call.prems have "Env\<turnstile>({accC,statT,mode}e\<cdot>mn( {pTs}args))\<Colon>-T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_no_jump) (simp_all add: G wf)
      qed
    } 
    hence "?BreakAssigned (Norm s0) (restore_lvars s2 s4) A"
      and "?ResAssigned (Norm s0) (restore_lvars s2 s4)"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (Methd D s0 s1 sig v Env T A)
    have G: "prg Env = G". 
    from Methd.prems obtain m where
       m:      "methd (prg Env) D sig = Some m" and
       da_body: "Env\<turnstile>(dom (locals (store ((Norm s0)::state)))) 
                  \<guillemotright>\<langle>Body (declclass m) (stmt (mbody (mthd m)))\<rangle>\<guillemotright> A"
      by - (erule da_elim_cases)
    from Methd.prems m obtain
      isCls: "is_class (prg Env) D" and
      wt_body: "Env \<turnstile>In1l (Body (declclass m) (stmt (mbody (mthd m))))\<Colon>T"
      by - (erule wt_elim_cases,simp)
    have "PROP ?Hyp (In1l (body G D sig)) (Norm s0) s1" .
    moreover
    from wt_body have "Env\<turnstile>In1l (body G D sig)\<Colon>T"
      using isCls m G by (simp add: body_def2)
    moreover 
    from da_body have "Env\<turnstile>(dom (locals (store ((Norm s0)::state)))) 
                          \<guillemotright>\<langle>body G D sig\<rangle>\<guillemotright> A"
      using isCls m G by (simp add: body_def2)
    ultimately show ?case
      using G by simp
  next
    case (Body D c s0 s1 s2 s3 Env T A)
    have G: "prg Env = G" .
    from Body.prems 
    have nrm_A: "nrm A = dom (locals (store ((Norm s0)::state)))"
      by (elim da_elim_cases) simp
    have eval: "prg Env\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)
                        \<rightarrow>abupd (absorb Ret) s3"
      by (simp only: G) (rule eval.Body)
    hence "nrm A \<subseteq> dom (locals (store (abupd (absorb Ret) s3)))"
      by  (simp only: nrm_A) (rule dom_locals_eval_mono_elim)
    hence "?NormalAssigned (abupd (absorb Ret) s3) A"
      by simp
    moreover
    from eval have "\<And> j. abrupt (abupd (absorb Ret) s3) \<noteq> Some (Jump j)"
      by (rule Body_no_jump) simp
    hence "?BreakAssigned (Norm s0) (abupd (absorb Ret) s3) A" and
          "?ResAssigned (Norm s0) (abupd (absorb Ret) s3)"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
-- {* 
\par
*} (* dummy text command to break paragraph for latex;
              large paragraphs exhaust memory of debian pdflatex *)
    case (LVar s vn Env T A)
    from LVar.prems
    have "nrm A = dom (locals (store ((Norm s)::state)))"
      by (elim da_elim_cases) simp
    thus ?case by simp
  next
    case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v Env T A)
    have G: "prg Env = G" .
    have "?NormalAssigned s3 A"
    proof 
      assume normal_s3: "normal s3"
      show "nrm A \<subseteq> dom (locals (store s3))"
      proof -
        have fvar: "(v, s2') = fvar statDeclC stat fn a s2" and
               s3: "s3 = check_field_access G accC statDeclC fn stat a s2'" .
        from FVar.prems
        have da_e: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>\<langle>e\<rangle>\<guillemotright> A"
          by (elim da_elim_cases)
        from FVar.prems obtain eT where
          wt_e: "Env\<turnstile>e\<Colon>-eT"
          by (elim wt_elim_cases)
        have "(dom (locals (store ((Norm s0)::state)))) 
               \<subseteq> dom (locals (store s1))"
          by (rule dom_locals_eval_mono_elim)
        with da_e obtain A' where
          da_e': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e\<rangle>\<guillemotright> A'" and
          nrm_A_A': "nrm A \<subseteq> nrm A'"
          by (rule da_weakenE) rules
        have normal_s2: "normal s2"
        proof -
          from normal_s3 s3 
          have "normal s2'"
            by (cases s2') (simp add: check_field_access_def Let_def)
          with fvar 
          show "normal s2"
            by (cases s2) (simp add: fvar_def2)
        qed
        have "PROP ?Hyp (In1l e) s1 s2" . 
        with da_e' wt_e G normal_s2
        have "nrm A' \<subseteq> dom (locals (store s2))"
          by simp
        with nrm_A_A' have "nrm A \<subseteq> dom (locals (store s2))"
          by blast
        also have "\<dots> \<subseteq> dom (locals (store s3))"
        proof -
          from fvar have "s2' = snd (fvar statDeclC stat fn a s2)" 
            by (cases "fvar statDeclC stat fn a s2") simp
          hence "dom (locals (store s2)) \<subseteq>  dom (locals (store s2'))"
            by (simp) (rule dom_locals_fvar_mono)
          also from s3 have "\<dots> \<subseteq> dom (locals (store s3))"
            by (cases s2') (simp add: check_field_access_def Let_def)
          finally show ?thesis .
        qed
        finally show ?thesis .
      qed
    qed
    moreover
    {
      fix j have "abrupt s3 \<noteq> Some (Jump j)"
      proof -
        obtain w upd where v: "(w,upd)=v"
          by (cases v) auto
        have eval: "prg Env\<turnstile>Norm s0\<midarrow>({accC,statDeclC,stat}e..fn)=\<succ>(w,upd)\<rightarrow>s3"
          by (simp only: G v) (rule eval.FVar)
        from FVar.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with FVar.prems have "Env\<turnstile>({accC,statDeclC,stat}e..fn)\<Colon>=T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_var_no_jump [THEN conjunct1]) (simp_all add: G wf)
      qed
    } 
    hence "?BreakAssigned (Norm s0) s3 A" and "?ResAssigned (Norm s0) s3"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (AVar a e1 e2 i s0 s1 s2 s2' v Env T A)
    have G: "prg Env = G" .
    have "?NormalAssigned s2' A"
    proof 
      assume normal_s2': "normal s2'"
      show "nrm A \<subseteq> dom (locals (store s2'))"
      proof -
        have avar: "(v, s2') = avar G i a s2" .
        from AVar.prems obtain E1 where
          da_e1: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>\<langle>e1\<rangle>\<guillemotright> E1" and
          da_e2: "Env\<turnstile> nrm E1 \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A" 
          by (elim da_elim_cases)
        from AVar.prems obtain e1T e2T where
             wt_e1: "Env\<turnstile>e1\<Colon>-e1T" and
             wt_e2: "Env\<turnstile>e2\<Colon>-e2T"
          by (elim wt_elim_cases)
        from avar normal_s2' 
        have normal_s2: "normal s2"
          by (cases s2) (simp add: avar_def2)
        hence "normal s1"
          by - (rule eval_no_abrupt_lemma [rule_format])
        moreover have "PROP ?Hyp (In1l e1) (Norm s0) s1" .
        ultimately have "nrm E1 \<subseteq> dom (locals (store s1))" 
          using da_e1 wt_e1 G by simp
        with da_e2 obtain A' where
          da_e2': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>e2\<rangle>\<guillemotright> A'" and
          nrm_A_A': "nrm A \<subseteq> nrm A'"
          by (rule da_weakenE) rules
        have "PROP ?Hyp (In1l e2) s1 s2" .
        with da_e2' wt_e2 G normal_s2
        have "nrm A' \<subseteq> dom (locals (store s2))"
          by simp
        with nrm_A_A' have "nrm A \<subseteq> dom (locals (store s2))"
          by blast
        also have "\<dots> \<subseteq> dom (locals (store s2'))"
        proof -
           from avar have "s2' = snd (avar G i a s2)" 
            by (cases "(avar G i a s2)") simp
          thus "dom (locals (store s2)) \<subseteq>  dom (locals (store s2'))"
            by (simp) (rule dom_locals_avar_mono)
        qed
        finally show ?thesis .
      qed
    qed
    moreover
    {
      fix j have "abrupt s2' \<noteq> Some (Jump j)"
      proof -
        obtain w upd where v: "(w,upd)=v"
          by (cases v) auto
        have eval: "prg Env\<turnstile>Norm s0\<midarrow>(e1.[e2])=\<succ>(w,upd)\<rightarrow>s2'"
          by  (simp only: G v) (rule eval.AVar)
        from AVar.prems 
        obtain T' where  "T=Inl T'"
          by (elim wt_elim_cases) simp
        with AVar.prems have "Env\<turnstile>(e1.[e2])\<Colon>=T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_var_no_jump [THEN conjunct1]) (simp_all add: G wf)
      qed
    } 
    hence "?BreakAssigned (Norm s0) s2' A" and "?ResAssigned (Norm s0) s2'"
      by simp_all
    ultimately show ?case by (intro conjI)
  next
    case (Nil s0 Env T A)
    from Nil.prems
    have "nrm A = dom (locals (store ((Norm s0)::state)))"
      by (elim da_elim_cases) simp
    thus ?case by simp
  next 
    case (Cons e es s0 s1 s2 v vs Env T A)
    have G: "prg Env = G" .
    have "?NormalAssigned s2 A"
    proof 
      assume normal_s2: "normal s2"
      show "nrm A \<subseteq> dom (locals (store s2))"
      proof -
        from Cons.prems obtain E where
          da_e: "Env\<turnstile> (dom (locals (store ((Norm s0)::state))))\<guillemotright>\<langle>e\<rangle>\<guillemotright> E" and
          da_es: "Env\<turnstile> nrm E \<guillemotright>\<langle>es\<rangle>\<guillemotright> A" 
          by (elim da_elim_cases)
        from Cons.prems obtain eT esT where
             wt_e: "Env\<turnstile>e\<Colon>-eT" and
             wt_es: "Env\<turnstile>es\<Colon>\<doteq>esT"
          by (elim wt_elim_cases)
        have "normal s1"
          by - (rule eval_no_abrupt_lemma [rule_format])
        moreover have "PROP ?Hyp (In1l e) (Norm s0) s1" .
        ultimately have "nrm E \<subseteq> dom (locals (store s1))" 
          using da_e wt_e G by simp
        with da_es obtain A' where
          da_es': "Env\<turnstile> dom (locals (store s1)) \<guillemotright>\<langle>es\<rangle>\<guillemotright> A'" and
          nrm_A_A': "nrm A \<subseteq> nrm A'"
          by (rule da_weakenE) rules
        have "PROP ?Hyp (In3 es) s1 s2" .
        with da_es' wt_es G normal_s2
        have "nrm A' \<subseteq> dom (locals (store s2))"
          by simp
        with nrm_A_A' show "nrm A \<subseteq> dom (locals (store s2))"
          by blast
      qed
    qed
    moreover
    {
      fix j have "abrupt s2 \<noteq> Some (Jump j)"
      proof -
        have eval: "prg Env\<turnstile>Norm s0\<midarrow>(e # es)\<doteq>\<succ>v#vs\<rightarrow>s2"
          by (simp only: G) (rule eval.Cons)
        from Cons.prems 
        obtain T' where  "T=Inr T'"
          by (elim wt_elim_cases) simp
        with Cons.prems have "Env\<turnstile>(e # es)\<Colon>\<doteq>T'" 
          by simp
        from eval _ this
        show ?thesis
          by (rule eval_expression_list_no_jump) (simp_all add: G wf)
      qed
    } 
    hence "?BreakAssigned (Norm s0) s2 A" and "?ResAssigned (Norm s0) s2"
      by simp_all
    ultimately show ?case by (intro conjI)
  qed
qed

lemma da_good_approxE [consumes 4]:
  "\<lbrakk>prg Env\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v, s1); Env\<turnstile>t\<Colon>T; Env\<turnstile> dom (locals (store s0)) \<guillemotright>t\<guillemotright> A;
   wf_prog (prg Env);
   \<lbrakk>normal s1 \<Longrightarrow> nrm A \<subseteq> dom (locals (store s1));
     \<And> l. \<lbrakk>abrupt s1 = Some (Jump (Break l)); normal s0\<rbrakk>
           \<Longrightarrow> brk A l \<subseteq> dom (locals (store s1));
     \<lbrakk>abrupt s1 = Some (Jump Ret);normal s0\<rbrakk>\<Longrightarrow>Result \<in> dom (locals (store s1))
   \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
by (drule (3) da_good_approx) simp


(* Same as above but with explicit environment; 
   It would be nicer to find a "normalized" way to right down those things
   in Bali.
*)
lemma da_good_approxE' [consumes 4]:
  assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v, s1)"
     and    wt: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>t\<Colon>T"
     and    da: "\<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile> dom (locals (store s0)) \<guillemotright>t\<guillemotright> A"
     and    wf: "wf_prog G"
     and  elim: "\<lbrakk>normal s1 \<Longrightarrow> nrm A \<subseteq> dom (locals (store s1));
                 \<And> l. \<lbrakk>abrupt s1 = Some (Jump (Break l)); normal s0\<rbrakk>
                       \<Longrightarrow> brk A l \<subseteq> dom (locals (store s1));
                  \<lbrakk>abrupt s1 = Some (Jump Ret);normal s0\<rbrakk>
                  \<Longrightarrow>Result \<in> dom (locals (store s1))
                 \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from eval have "prg \<lparr>prg=G,cls=C,lcl=L\<rparr>\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v, s1)" by simp
  moreover note wt da
  moreover from wf have "wf_prog (prg \<lparr>prg=G,cls=C,lcl=L\<rparr>)" by simp
  ultimately show ?thesis
    using elim by (rule da_good_approxE) rules+
qed

ML {*
Addsimprocs [wt_expr_proc,wt_var_proc,wt_exprs_proc,wt_stmt_proc]
*}
end