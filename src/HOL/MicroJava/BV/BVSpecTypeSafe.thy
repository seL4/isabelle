(*  Title:      HOL/MicroJava/BV/BVSpecTypeSafe.thy
    ID:         $Id$
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{BV Type Safety Proof}\label{sec:BVSpecTypeSafe} *}

theory BVSpecTypeSafe = Correct:

text {*
  This theory contains proof that the specification of the bytecode
  verifier only admits type safe programs.  
*}

section {* Preliminaries *}

text {*
  Simp and intro setup for the type safety proof:
*}
lemmas defs1 = sup_state_conv correct_state_def correct_frame_def 
               wt_instr_def eff_def norm_eff_def 

lemmas widen_rules[intro] = approx_val_widen approx_loc_widen approx_stk_widen

lemmas [simp del] = split_paired_All


text {*
  If we have a welltyped program and a conforming state, we
  can directly infer that the current instruction is well typed:
*}
lemma wt_jvm_prog_impl_wt_instr_cor:
  "[| wt_jvm_prog G phi; method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
      G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
  ==> wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
apply (unfold correct_state_def Let_def correct_frame_def)
apply simp
apply (blast intro: wt_jvm_prog_impl_wt_instr)
done


section {* Exception Handling *}

text {*
  Exceptions don't touch anything except the stack:
*}
lemma exec_instr_xcpt:
  "(fst (exec_instr i G hp stk vars Cl sig pc frs) = Some xcp)
  = (\<exists>stk'. exec_instr i G hp stk vars Cl sig pc frs = 
            (Some xcp, hp, (stk', vars, Cl, sig, pc)#frs))"
  by (cases i, auto simp add: split_beta split: split_if_asm)


text {*
  Relates @{text match_any} from the Bytecode Verifier with 
  @{text match_exception_table} from the operational semantics:
*}
lemma in_match_any:
  "match_exception_table G xcpt pc et = Some pc' ==> 
  \<exists>C. C \<in> set (match_any G pc et) \<and> G \<turnstile> xcpt \<preceq>C C \<and> 
      match_exception_table G C pc et = Some pc'"
  (is "PROP ?P et" is "?match et ==> ?match_any et")
proof (induct et)  
  show "PROP ?P []" 
    by simp

  fix e es
  assume IH: "PROP ?P es"
  assume match: "?match (e#es)"

  obtain start_pc end_pc handler_pc catch_type where
    e [simp]: "e = (start_pc, end_pc, handler_pc, catch_type)"
    by (cases e) 

  from IH match
  show "?match_any (e#es)" 
  proof (cases "match_exception_entry G xcpt pc e")
    case False
    with match
    have "match_exception_table G xcpt pc es = Some pc'" by simp
    with IH
    obtain C where
      set: "C \<in> set (match_any G pc es)" and
      C:   "G \<turnstile> xcpt \<preceq>C C" and
      m:   "match_exception_table G C pc es = Some pc'" by blast

    from set
    have "C \<in> set (match_any G pc (e#es))" by simp
    moreover
    from False C
    have "\<not> match_exception_entry G C pc e"
      by - (erule contrapos_nn, 
            auto simp add: match_exception_entry_def elim: rtrancl_trans)
    with m
    have "match_exception_table G C pc (e#es) = Some pc'" by simp
    moreover note C
    ultimately
    show ?thesis by blast
  next
    case True with match
    have "match_exception_entry G catch_type pc e"
      by (simp add: match_exception_entry_def)
    moreover
    from True match
    obtain 
      "start_pc \<le> pc" 
      "pc < end_pc" 
      "G \<turnstile> xcpt \<preceq>C catch_type" 
      "handler_pc = pc'" 
      by (simp add: match_exception_entry_def)
    ultimately
    show ?thesis by auto
  qed
qed

text {*
  We can prove separately that the recursive search for exception
  handlers (@{text find_handler}) in the frame stack results in 
  a conforming state (if there was no matching exception handler 
  in the current frame). We require that the exception is a valid
  heap address, and that the state before the exception occured
  conforms. 
*}
lemma uncaught_xcpt_correct:
  "!!f. [| wt_jvm_prog G phi; xcp = Addr adr; hp adr = Some T;
      G,phi \<turnstile>JVM (None, hp, f#frs)\<surd> |]
  ==> G,phi \<turnstile>JVM (find_handler G (Some xcp) hp frs)\<surd>" 
  (is "!!f. [| ?wt; ?adr; ?hp; ?correct (None, hp, f#frs) |] ==> ?correct (?find frs)")
proof (induct frs) 
  -- "the base case is trivial, as it should be"
  show "?correct (?find [])" by (simp add: correct_state_def)

  -- "we will need both forms @{text wt_jvm_prog} and @{text wf_prog} later"
  assume wt: ?wt 
  then obtain mb where wf: "wf_prog mb G" by (simp add: wt_jvm_prog_def)

  -- "these two don't change in the induction:"
  assume adr: ?adr
  assume hp: ?hp
  
  -- "the assumption for the cons case:"
  fix f f' frs' 
  assume cr: "?correct (None, hp, f#f'#frs')" 

  -- "the induction hypothesis as produced by Isabelle, immediatly simplified
    with the fixed assumptions above"
  assume "\<And>f. [| ?wt; ?adr; ?hp; ?correct (None, hp, f#frs') |] ==> ?correct (?find frs')"  
  with wt adr hp 
  have IH: "\<And>f. ?correct (None, hp, f#frs') ==> ?correct (?find frs')" by blast

  from cr
  have cr': "?correct (None, hp, f'#frs')" by (auto simp add: correct_state_def)
    
  obtain stk loc C sig pc where f' [simp]: "f' = (stk,loc,C,sig,pc)"
    by (cases f') 

  from cr 
  obtain rT maxs maxl ins et where
    meth: "method (G,C) sig = Some (C,rT,maxs,maxl,ins,et)"
    by (simp add: correct_state_def, blast)

  hence [simp]: "ex_table_of (snd (snd (the (method (G, C) sig)))) = et"
    by simp

  show "?correct (?find (f'#frs'))" 
  proof (cases "match_exception_table G (cname_of hp xcp) pc et")
    case None
    with cr' IH 
    show ?thesis by simp
  next
    fix handler_pc 
    assume match: "match_exception_table G (cname_of hp xcp) pc et = Some handler_pc"
    (is "?match (cname_of hp xcp) = _")

    from wt meth cr' [simplified]
    have wti: "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc" 
      by (rule wt_jvm_prog_impl_wt_instr_cor)

    from cr meth
    obtain C' mn pts ST LT where
      ins: "ins!pc = Invoke C' mn pts" (is "_ = ?i") and
      phi: "phi C sig ! pc = Some (ST, LT)"
      by (simp add: correct_state_def) blast    

    from match
    obtain D where
      in_any: "D \<in> set (match_any G pc et)" and
      D:      "G \<turnstile> cname_of hp xcp \<preceq>C D" and
      match': "?match D = Some handler_pc"
      by (blast dest: in_match_any)

    from ins wti phi have 
      "\<forall>D\<in>set (match_any G pc et). the (?match D) < length ins \<and> 
      G \<turnstile> Some ([Class D], LT) <=' phi C sig!the (?match D)"
      by (simp add: wt_instr_def eff_def xcpt_eff_def)      
    with in_any match' obtain
      pc: "handler_pc < length ins" 
      "G \<turnstile> Some ([Class D], LT) <=' phi C sig ! handler_pc"
      by auto
    then obtain ST' LT' where
      phi': "phi C sig ! handler_pc = Some (ST',LT')" and
      less: "G \<turnstile> ([Class D], LT) <=s (ST',LT')"
      by auto    
    
    from cr' phi meth f'
    have "correct_frame G hp (ST, LT) maxl ins f'"
      by (unfold correct_state_def) auto
    then obtain
     len: "length loc = 1+length (snd sig)+maxl" and
     loc: "approx_loc G hp loc LT"
      by (unfold correct_frame_def) auto

    let ?f = "([xcp], loc, C, sig, handler_pc)"
    have "correct_frame G hp (ST', LT') maxl ins ?f" 
    proof -
      from wf less loc
      have "approx_loc G hp loc LT'" by (simp add: sup_state_conv) blast
      moreover
      from D adr hp
      have "G,hp \<turnstile> xcp ::\<preceq> Class D" by (simp add: conf_def obj_ty_def)
      with wf less loc
      have "approx_stk G hp [xcp] ST'"
        by (auto simp add: sup_state_conv approx_stk_def approx_val_def 
                 elim: conf_widen split: Err.split)
      moreover
      note len pc
      ultimately
      show ?thesis by (simp add: correct_frame_def)
    qed

    with cr' match phi' meth  
    show ?thesis by (unfold correct_state_def) auto
  qed
qed


text {*
  The requirement of lemma @{text uncaught_xcpt_correct} (that
  the exception is a valid reference on the heap) is always met
  for welltyped instructions and conformant states:
*}
lemma exec_instr_xcpt_hp:
  "[|  fst (exec_instr (ins!pc) G hp stk vars Cl sig pc frs) = Some xcp;
       wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc;
       G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
  ==> \<exists>adr T. xcp = Addr adr \<and> hp adr = Some T" 
  (is "[| ?xcpt; ?wt; ?correct |] ==> ?thesis")
proof -
  note [simp] = split_beta raise_system_xcpt_def
  note [split] = split_if_asm option.split_asm 
  
  assume wt: ?wt ?correct
  hence pre: "preallocated hp" by (simp add: correct_state_def)

  assume xcpt: ?xcpt with pre show ?thesis 
  proof (cases "ins!pc")
    case New with xcpt pre
    show ?thesis by (auto dest: new_Addr_OutOfMemory) 
  next
    case Throw with xcpt wt
    show ?thesis
      by (auto simp add: wt_instr_def correct_state_def correct_frame_def 
               dest: non_npD)
  qed auto
qed


text {*
  Finally we can state that, whenever an exception occurs, the
  resulting next state always conforms:
*}
lemma xcpt_correct:
  "[| wt_jvm_prog G phi;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
      wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
      fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = Some xcp; 
      Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
      G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
  ==> G,phi \<turnstile>JVM state'\<surd>"
proof -
  assume wtp: "wt_jvm_prog G phi"
  assume meth: "method (G,C) sig = Some (C,rT,maxs,maxl,ins,et)"
  assume wt: "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
  assume xp: "fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = Some xcp"
  assume s': "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume correct: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"

  from wtp obtain wfmb where wf: "wf_prog wfmb G" by (simp add: wt_jvm_prog_def)

  note xp' = meth s' xp

  note wtp
  moreover
  from xp wt correct
  obtain adr T where
    adr: "xcp = Addr adr" "hp adr = Some T"
    by (blast dest: exec_instr_xcpt_hp)
  moreover
  note correct
  ultimately
  have "G,phi \<turnstile>JVM find_handler G (Some xcp) hp frs \<surd>" by (rule uncaught_xcpt_correct)
  with xp'
  have "match_exception_table G (cname_of hp xcp) pc et = None \<Longrightarrow> ?thesis" 
    (is "?m (cname_of hp xcp) = _ \<Longrightarrow> _" is "?match = _ \<Longrightarrow> _")
    by (clarsimp simp add: exec_instr_xcpt split_beta)
  moreover
  { fix handler
    assume some_handler: "?match = Some handler"
    
    from correct meth
    obtain ST LT where
      hp_ok:  "G \<turnstile>h hp \<surd>" and
      prehp:  "preallocated hp" and
      class:  "is_class G C" and
      phi_pc: "phi C sig ! pc = Some (ST, LT)" and
      frame:  "correct_frame G hp (ST, LT) maxl ins (stk, loc, C, sig, pc)" and
      frames: "correct_frames G hp phi rT sig frs"
      by (unfold correct_state_def) auto

    from frame obtain 
      stk: "approx_stk G hp stk ST" and
      loc: "approx_loc G hp loc LT" and
      pc:  "pc < length ins" and
      len: "length loc = 1+length (snd sig)+maxl"
      by (unfold correct_frame_def) auto
    
    from wt obtain
      eff: "\<forall>(pc', s')\<in>set (xcpt_eff (ins!pc) G pc (phi C sig!pc) et).
             pc' < length ins \<and> G \<turnstile> s' <=' phi C sig!pc'"
      by (simp add: wt_instr_def eff_def)
    
    from some_handler xp'
    have state': 
      "state' = (None, hp, ([xcp], loc, C, sig, handler)#frs)"
      by (cases "ins!pc", auto simp add: raise_system_xcpt_def split_beta 
                               split: split_if_asm) (* takes long! *)

    let ?f' = "([xcp], loc, C, sig, handler)"
    from eff
    obtain ST' LT' where
      phi_pc': "phi C sig ! handler = Some (ST', LT')" and
      frame': "correct_frame G hp (ST',LT') maxl ins ?f'" 
    proof (cases "ins!pc")
      case Return -- "can't generate exceptions:"
      with xp' have False by (simp add: split_beta split: split_if_asm)
      thus ?thesis ..
    next
      case New
      with some_handler xp'
      have xcp: "xcp = Addr (XcptRef OutOfMemory)"
        by (simp add: raise_system_xcpt_def split_beta new_Addr_OutOfMemory)
      with prehp have "cname_of hp xcp = Xcpt OutOfMemory" by simp
      with New some_handler phi_pc eff 
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class (Xcpt OutOfMemory)], LT) <=s (ST', LT')" and
        pc':  "handler < length ins"
        by (simp add: xcpt_eff_def) blast
      note phi'
      moreover
      { from xcp prehp
        have "G,hp \<turnstile> xcp ::\<preceq> Class (Xcpt OutOfMemory)"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    next 
      case Getfield
      with some_handler xp'
      have xcp: "xcp = Addr (XcptRef NullPointer)"
        by (simp add: raise_system_xcpt_def split_beta split: split_if_asm)
      with prehp have "cname_of hp xcp = Xcpt NullPointer" by simp
      with Getfield some_handler phi_pc eff 
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class (Xcpt NullPointer)], LT) <=s (ST', LT')" and
        pc':  "handler < length ins"
        by (simp add: xcpt_eff_def) blast
      note phi'
      moreover
      { from xcp prehp
        have "G,hp \<turnstile> xcp ::\<preceq> Class (Xcpt NullPointer)"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    next
      case Putfield
      with some_handler xp'
      have xcp: "xcp = Addr (XcptRef NullPointer)"
        by (simp add: raise_system_xcpt_def split_beta split: split_if_asm)
      with prehp have "cname_of hp xcp = Xcpt NullPointer" by simp
      with Putfield some_handler phi_pc eff 
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class (Xcpt NullPointer)], LT) <=s (ST', LT')" and
        pc':  "handler < length ins"
        by (simp add: xcpt_eff_def) blast
      note phi'
      moreover
      { from xcp prehp
        have "G,hp \<turnstile> xcp ::\<preceq> Class (Xcpt NullPointer)"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    next
      case Checkcast
      with some_handler xp'
      have xcp: "xcp = Addr (XcptRef ClassCast)"
        by (simp add: raise_system_xcpt_def split_beta split: split_if_asm)
      with prehp have "cname_of hp xcp = Xcpt ClassCast" by simp
      with Checkcast some_handler phi_pc eff 
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class (Xcpt ClassCast)], LT) <=s (ST', LT')" and
        pc':  "handler < length ins"
        by (simp add: xcpt_eff_def) blast
      note phi'
      moreover
      { from xcp prehp
        have "G,hp \<turnstile> xcp ::\<preceq> Class (Xcpt ClassCast)"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    next
      case Invoke
      with phi_pc eff 
      have 
        "\<forall>D\<in>set (match_any G pc et). 
        the (?m D) < length ins \<and> G \<turnstile> Some ([Class D], LT) <=' phi C sig!the (?m D)"
        by (simp add: xcpt_eff_def)
      moreover
      from some_handler
      obtain D where
        "D \<in> set (match_any G pc et)" and
        D: "G \<turnstile> cname_of hp xcp \<preceq>C D" and
        "?m D = Some handler"
        by (blast dest: in_match_any)
      ultimately
      obtain 
        pc': "handler < length ins" and
        "G \<turnstile> Some ([Class D], LT) <=' phi C sig ! handler"
        by auto
      then
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class D], LT) <=s (ST', LT')" 
        by auto
      from xp wt correct
      obtain addr T where
        xcp: "xcp = Addr addr" "hp addr = Some T"
        by (blast dest: exec_instr_xcpt_hp)
      note phi'
      moreover
      { from xcp D
        have "G,hp \<turnstile> xcp ::\<preceq> Class D"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    next
      case Throw
      with phi_pc eff 
      have 
        "\<forall>D\<in>set (match_any G pc et). 
        the (?m D) < length ins \<and> G \<turnstile> Some ([Class D], LT) <=' phi C sig!the (?m D)"
        by (simp add: xcpt_eff_def)
      moreover
      from some_handler
      obtain D where
        "D \<in> set (match_any G pc et)" and
        D: "G \<turnstile> cname_of hp xcp \<preceq>C D" and
        "?m D = Some handler"
        by (blast dest: in_match_any)
      ultimately
      obtain 
        pc': "handler < length ins" and
        "G \<turnstile> Some ([Class D], LT) <=' phi C sig ! handler"
        by auto
      then
      obtain ST' LT' where
        phi': "phi C sig ! handler = Some (ST', LT')" and
        less: "G \<turnstile> ([Class D], LT) <=s (ST', LT')" 
        by auto
      from xp wt correct
      obtain addr T where
        xcp: "xcp = Addr addr" "hp addr = Some T"
        by (blast dest: exec_instr_xcpt_hp)
      note phi'
      moreover
      { from xcp D
        have "G,hp \<turnstile> xcp ::\<preceq> Class D"
          by (simp add: conf_def obj_ty_def)
        moreover
        from wf less loc
        have "approx_loc G hp loc LT'"
          by (simp add: sup_state_conv) blast        
        moreover
        note wf less pc' len 
        ultimately
        have "correct_frame G hp (ST',LT') maxl ins ?f'"
          by (unfold correct_frame_def) (auto simp add: sup_state_conv 
              approx_stk_def approx_val_def split: err.split elim: conf_widen)
      }
      ultimately
      show ?thesis by (rule that)
    qed (insert xp', auto) -- "the other instructions don't generate exceptions"

    from state' meth hp_ok class frames phi_pc' frame' 
    have ?thesis by (unfold correct_state_def) simp
  }
  ultimately
  show ?thesis by (cases "?match") blast+ 
qed



section {* Single Instructions *}

text {*
  In this section we look at each single (welltyped) instruction, and
  prove that the state after execution of the instruction still conforms.
  Since we have already handled exceptions above, we can now assume, that
  on exception occurs for this (single step) execution.
*}

lemmas [iff] = not_Err_eq

lemma Load_correct:
"[| wf_prog wt G;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
    ins!pc = Load idx; 
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: approx_loc_imp_approx_val_sup)
done

lemma Store_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et);
  ins!pc = Store idx;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc;
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: approx_loc_subst)
done


lemma LitPush_correct:
"[| wf_prog wt G;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
    ins!pc = LitPush v;
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs);
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>" 
apply (clarsimp simp add: defs1 sup_PTS_eq map_eq_Cons)
apply (blast dest: conf_litval intro: conf_widen)
done


lemma Cast_conf2:
  "[| wf_prog ok G; G,h\<turnstile>v::\<preceq>RefT rt; cast_ok G C h v; 
      G\<turnstile>Class C\<preceq>T; is_class G C|] 
  ==> G,h\<turnstile>v::\<preceq>T"
apply (unfold cast_ok_def)
apply (frule widen_Class)
apply (elim exE disjE) 
 apply (simp add: null)
apply (clarsimp simp add: conf_def obj_ty_def)
apply (cases v)
apply (auto intro: rtrancl_trans)
done

lemmas defs1 = defs1 raise_system_xcpt_def

lemma Checkcast_correct:
"[| wt_jvm_prog G phi;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
    ins!pc = Checkcast D; 
    wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
    Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
    G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
    fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 wt_jvm_prog_def map_eq_Cons split: split_if_asm)
apply (blast intro: Cast_conf2)
done


lemma Getfield_correct:
"[| wt_jvm_prog G phi;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins!pc = Getfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
  fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons wt_jvm_prog_def 
                split: option.split split_if_asm)
apply (frule conf_widen)
apply assumption+
apply (drule conf_RefTD)
apply (clarsimp simp add: defs1)
apply (rule conjI)
 apply (drule widen_cfs_fields)
 apply assumption+
 apply (erule conf_widen)
 prefer 2
  apply assumption
 apply (simp add: hconf_def oconf_def lconf_def)
 apply (elim allE)
 apply (erule impE, assumption)
 apply simp
 apply (elim allE)
 apply (erule impE, assumption)
 apply clarsimp
apply blast
done


lemma Putfield_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins!pc = Putfield F D; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
  fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 split_beta split: option.split List.split split_if_asm)
apply (frule conf_widen)
prefer 2
  apply assumption
 apply assumption
apply (drule conf_RefTD)
apply clarsimp
apply (blast 
       intro: 
         hext_upd_obj approx_stk_sup_heap
         approx_loc_sup_heap 
         hconf_field_update
         preallocated_field_update
         correct_frames_field_update conf_widen 
       dest: 
         widen_cfs_fields)
done
    

lemma New_correct:
"[| wf_prog wt G;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins!pc = New X; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
  fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>"
proof -
  assume wf:   "wf_prog wt G"
  assume meth: "method (G,C) sig = Some (C,rT,maxs,maxl,ins,et)"
  assume ins:  "ins!pc = New X"
  assume wt:   "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
  assume exec: "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume conf: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"
  assume no_x: "fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None"

  from ins conf meth
  obtain ST LT where
    heap_ok:    "G\<turnstile>h hp\<surd>" and
    prealloc:   "preallocated hp" and
    phi_pc:     "phi C sig!pc = Some (ST,LT)" and
    is_class_C: "is_class G C" and
    frame:      "correct_frame G hp (ST,LT) maxl ins (stk, loc, C, sig, pc)" and
    frames:     "correct_frames G hp phi rT sig frs"
    by (auto simp add: correct_state_def iff del: not_None_eq)

  from phi_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class G X" and
    maxs:       "length ST < maxs" and
    suc_pc:     "Suc pc < length ins" and
    phi_suc:    "phi C sig ! Suc pc = Some (ST', LT')" and
    less:       "G \<turnstile> (Class X # ST, LT) <=s (ST', LT')"
    by (unfold wt_instr_def eff_def norm_eff_def) auto
 
  obtain oref xp' where
    new_Addr: "new_Addr hp = (oref,xp')"
    by (cases "new_Addr hp") 
  with ins no_x
  obtain hp: "hp oref = None" and "xp' = None"
    by (auto dest: new_AddrD simp add: raise_system_xcpt_def)
  
  with exec ins meth new_Addr 
  have state':
    "state' = Norm (hp(oref\<mapsto>(X, init_vars (fields (G, X)))), 
              (Addr oref # stk, loc, C, sig, Suc pc) # frs)" 
    (is "state' = Norm (?hp', ?f # frs)")
    by simp    
  moreover
  from wf hp heap_ok is_class_X
  have hp': "G \<turnstile>h ?hp' \<surd>"
    by - (rule hconf_newref, auto simp add: oconf_def dest: fields_is_type)
  moreover
  from hp
  have sup: "hp \<le>| ?hp'" by (rule hext_new)
  from hp frame less suc_pc wf
  have "correct_frame G ?hp' (ST', LT') maxl ins ?f"
    apply (unfold correct_frame_def sup_state_conv)
    apply (clarsimp simp add: map_eq_Cons conf_def fun_upd_apply approx_val_def)
    apply (blast intro: approx_stk_sup_heap approx_loc_sup_heap sup)
    done      
  moreover
  from hp frames wf heap_ok is_class_X
  have "correct_frames G ?hp' phi rT sig frs"
    by - (rule correct_frames_newref, 
          auto simp add: oconf_def dest: fields_is_type)
  moreover
  from hp prealloc have "preallocated ?hp'" by (rule preallocated_newref)
  ultimately
  show ?thesis
    by (simp add: is_class_C meth phi_suc correct_state_def del: not_None_eq)
qed

lemmas [simp del] = split_paired_Ex


lemma Invoke_correct: 
"[| wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Invoke C' mn pTs; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
  fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>" 
proof -
  assume wtprog: "wt_jvm_prog G phi"
  assume method: "method (G,C) sig = Some (C,rT,maxs,maxl,ins,et)"
  assume ins:    "ins ! pc = Invoke C' mn pTs"
  assume wti:    "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
  assume state': "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume approx: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"
  assume no_xcp: "fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None"
  
  from wtprog 
  obtain wfmb where
    wfprog: "wf_prog wfmb G" 
    by (simp add: wt_jvm_prog_def)
      
  from ins method approx
  obtain s where
    heap_ok: "G\<turnstile>h hp\<surd>" and
    prealloc:"preallocated hp" and
    phi_pc:  "phi C sig!pc = Some s" and
    is_class_C: "is_class G C" and
    frame:   "correct_frame G hp s maxl ins (stk, loc, C, sig, pc)" and
    frames:  "correct_frames G hp phi rT sig frs"
    by (clarsimp simp add: correct_state_def iff del: not_None_eq)

  from ins wti phi_pc
  obtain apTs X ST LT D' rT body where 
    is_class: "is_class G C'" and
    s:  "s = (rev apTs @ X # ST, LT)" and
    l:  "length apTs = length pTs" and
    X:  "G\<turnstile> X \<preceq> Class C'" and
    w:  "\<forall>x\<in>set (zip apTs pTs). x \<in> widen G" and
    mC':"method (G, C') (mn, pTs) = Some (D', rT, body)" and
    pc: "Suc pc < length ins" and
    eff: "G \<turnstile> norm_eff (Invoke C' mn pTs) G (Some s) <=' phi C sig!Suc pc"
    by (simp add: wt_instr_def eff_def del: not_None_eq) 
       (elim exE conjE, rule that)

  from eff
  obtain ST' LT' where
    s': "phi C sig ! Suc pc = Some (ST', LT')"
    by (simp add: norm_eff_def split_paired_Ex) blast

  from X 
  obtain T where
    X_Ref: "X = RefT T"
    by - (drule widen_RefT2, erule exE, rule that)
  
  from s ins frame 
  obtain 
    a_stk: "approx_stk G hp stk (rev apTs @ X # ST)" and
    a_loc: "approx_loc G hp loc LT" and
    suc_l: "length loc = Suc (length (snd sig) + maxl)"
    by (simp add: correct_frame_def)

  from a_stk
  obtain opTs stk' oX where
    opTs:   "approx_stk G hp opTs (rev apTs)" and
    oX:     "approx_val G hp oX (OK X)" and
    a_stk': "approx_stk G hp stk' ST" and
    stk':   "stk = opTs @ oX # stk'" and
    l_o:    "length opTs = length apTs" 
            "length stk' = length ST"  
    by - (drule approx_stk_append, auto)

  from oX X_Ref
  have oX_conf: "G,hp \<turnstile> oX ::\<preceq> RefT T"
    by (simp add: approx_val_def)

  from stk' l_o l
  have oX_pos: "last (take (Suc (length pTs)) stk) = oX" by simp

  with state' method ins no_xcp oX_conf
  obtain ref where oX_Addr: "oX = Addr ref"
    by (auto simp add: raise_system_xcpt_def dest: conf_RefTD)

  with oX_conf X_Ref
  obtain obj D where
    loc:    "hp ref = Some obj" and
    obj_ty: "obj_ty obj = Class D" and
    D:      "G \<turnstile> Class D \<preceq> X"
    by (auto simp add: conf_def) blast
  
  with X_Ref obtain X' where X': "X = Class X'"
    by (blast dest: widen_Class)
      
  with X have X'_subcls: "G \<turnstile> X' \<preceq>C C'"  by simp

  with mC' wfprog
  obtain D0 rT0 maxs0 maxl0 ins0 et0 where
    mX: "method (G, X') (mn, pTs) = Some (D0, rT0, maxs0, maxl0, ins0, et0)" "G\<turnstile>rT0\<preceq>rT"
    by (auto dest: subtype_widen_methd intro: that)
    
  from X' D have D_subcls: "G \<turnstile> D \<preceq>C X'" by simp
  
  with wfprog mX
  obtain D'' rT' mxs' mxl' ins' et' where
    mD: "method (G, D) (mn, pTs) = Some (D'', rT', mxs', mxl', ins', et')" 
        "G \<turnstile> rT' \<preceq> rT0"
    by (auto dest: subtype_widen_methd intro: that)
  
  from mX mD have rT': "G \<turnstile> rT' \<preceq> rT" by - (rule widen_trans)
  
  from is_class X'_subcls D_subcls
  have is_class_D: "is_class G D" by (auto dest: subcls_is_class2)
  
  with mD wfprog
  obtain mD'': 
    "method (G, D'') (mn, pTs) = Some (D'', rT', mxs', mxl', ins', et')"
    "is_class G D''"
    by (auto dest: method_in_md)
      
  from loc obj_ty have "fst (the (hp ref)) = D" by (simp add: obj_ty_def)

  with oX_Addr oX_pos state' method ins stk' l_o l loc obj_ty mD no_xcp
  have state'_val:
    "state' =
     Norm (hp, ([], Addr ref # rev opTs @ replicate mxl' arbitrary, 
                D'', (mn, pTs), 0) # (opTs @ Addr ref # stk', loc, C, sig, pc) # frs)"
    (is "state' = Norm (hp, ?f # ?f' # frs)")
    by (simp add: raise_system_xcpt_def)
    
  from wtprog mD''
  have start: "wt_start G D'' pTs mxl' (phi D'' (mn, pTs)) \<and> ins' \<noteq> []"
    by (auto dest: wt_jvm_prog_impl_wt_start)
    
  then obtain LT0 where
    LT0: "phi D'' (mn, pTs) ! 0 = Some ([], LT0)"
    by (clarsimp simp add: wt_start_def sup_state_conv)

  have c_f: "correct_frame G hp ([], LT0) mxl' ins' ?f"
  proof -
    from start LT0
    have sup_loc: 
      "G \<turnstile> (OK (Class D'') # map OK pTs @ replicate mxl' Err) <=l LT0"
      (is "G \<turnstile> ?LT <=l LT0")
      by (simp add: wt_start_def sup_state_conv)

    have r: "approx_loc G hp (replicate mxl' arbitrary) (replicate mxl' Err)"
      by (simp add: approx_loc_def list_all2_def set_replicate_conv_if)
    
    from wfprog mD is_class_D
    have "G \<turnstile> Class D \<preceq> Class D''"
      by (auto dest: method_wf_mdecl)
    with obj_ty loc
    have a: "approx_val G hp (Addr ref) (OK (Class D''))"
      by (simp add: approx_val_def conf_def)

    from opTs w l l_o wfprog 
    have "approx_stk G hp opTs (rev pTs)" 
      by (auto elim!: approx_stk_all_widen simp add: zip_rev)
    hence "approx_stk G hp (rev opTs) pTs" by (subst approx_stk_rev)

    with r a l_o l
    have "approx_loc G hp (Addr ref # rev opTs @ replicate mxl' arbitrary) ?LT"
      (is "approx_loc G hp ?lt ?LT")
      by (auto simp add: approx_loc_append approx_stk_def)

    from this sup_loc wfprog
    have "approx_loc G hp ?lt LT0" by (rule approx_loc_widen)
    with start l_o l
    show ?thesis by (simp add: correct_frame_def)
  qed

  from state'_val heap_ok mD'' ins method phi_pc s X' l mX
       frames s' LT0 c_f is_class_C stk' oX_Addr frame prealloc
  show ?thesis by (simp add: correct_state_def) (intro exI conjI, blast)
qed

lemmas [simp del] = map_append

lemma Return_correct:
"[| wt_jvm_prog G phi; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Return; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |]
==> G,phi \<turnstile>JVM state'\<surd>"
proof -
  assume wt_prog: "wt_jvm_prog G phi"
  assume meth: "method (G,C) sig = Some (C,rT,maxs,maxl,ins,et)"
  assume ins: "ins ! pc = Return"
  assume wt: "wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
  assume s': "Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs)"
  assume correct: "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>"

  from wt_prog 
  obtain wfmb where wf: "wf_prog wfmb G" by (simp add: wt_jvm_prog_def)

  from meth ins s'
  have "frs = [] \<Longrightarrow> ?thesis" by (simp add: correct_state_def)
  moreover
  { fix f frs' 
    assume frs': "frs = f#frs'"
    moreover
    obtain stk' loc' C' sig' pc' where
      f: "f = (stk',loc',C',sig',pc')" by (cases f)
    moreover
    obtain mn pt where
      sig: "sig = (mn,pt)" by (cases sig)
    moreover
    note meth ins s'
    ultimately
    have state':
      "state' = (None,hp,(hd stk#(drop (1+length pt) stk'),loc',C',sig',pc'+1)#frs')"
      (is "state' = (None,hp,?f'#frs')")
      by simp
    
    from correct meth
    obtain ST LT where
      hp_ok:  "G \<turnstile>h hp \<surd>" and
      alloc:  "preallocated hp" and
      phi_pc: "phi C sig ! pc = Some (ST, LT)" and
      frame:  "correct_frame G hp (ST, LT) maxl ins (stk,loc,C,sig,pc)" and
      frames: "correct_frames G hp phi rT sig frs"
      by (simp add: correct_state_def, clarify, blast)    

    from phi_pc ins wt
    obtain T ST' where "ST = T # ST'" "G \<turnstile> T \<preceq> rT"
      by (simp add: wt_instr_def) blast    
    with wf frame 
    have hd_stk: "G,hp \<turnstile> (hd stk) ::\<preceq> rT"
      by (auto simp add: correct_frame_def elim: conf_widen)

    from f frs' frames sig
    obtain apTs ST0' ST' LT' D D' D'' rT' rT'' maxs' maxl' ins' et' body where
      phi':   "phi C' sig' ! pc' = Some (ST',LT')" and
      class': "is_class G C'" and
      meth':  "method (G,C') sig' = Some (C',rT',maxs',maxl',ins',et')" and
      ins':   "ins' ! pc' = Invoke D' mn pt" and
      frame': "correct_frame G hp (ST', LT') maxl' ins' f" and
      frames':"correct_frames G hp phi rT' sig' frs'" and
      rT'':   "G \<turnstile> rT \<preceq> rT''" and
      meth'': "method (G, D) sig = Some (D'', rT'', body)" and
      ST0':   "ST' = rev apTs @ Class D # ST0'" and
      len':   "length apTs = length pt" 
      by clarsimp blast    

    from f frame'
    obtain
      stk': "approx_stk G hp stk' ST'" and
      loc': "approx_loc G hp loc' LT'" and
      pc':  "pc' < length ins'" and
      lloc':"length loc' = Suc (length (snd sig') + maxl')"
      by (simp add: correct_frame_def)

    from wt_prog class' meth' pc'  
    have "wt_instr (ins'!pc') G rT' (phi C' sig') maxs' (length ins') et' pc'"
      by (rule wt_jvm_prog_impl_wt_instr)
    with ins' phi' sig
    obtain apTs ST0 X ST'' LT'' body' rT0 mD where
      phi_suc: "phi C' sig' ! Suc pc' = Some (ST'', LT'')" and
      ST0:     "ST' = rev apTs @ X # ST0" and
      len:     "length apTs = length pt" and
      less:    "G \<turnstile> (rT0 # ST0, LT') <=s (ST'', LT'')" and
      methD':  "method (G, D') sig = Some (mD, rT0, body')" and
      lessD':  "G \<turnstile> X \<preceq> Class D'" and
      suc_pc': "Suc pc' < length ins'"
      by (clarsimp simp add: wt_instr_def eff_def norm_eff_def) blast

    from len len' ST0 ST0'
    have "X = Class D" by simp
    with lessD'
    have "G \<turnstile> D \<preceq>C D'" by simp
    moreover
    note wf meth'' methD'
    ultimately
    have "G \<turnstile> rT'' \<preceq> rT0" by (auto dest: subcls_widen_methd)
    with wf hd_stk rT''
    have hd_stk': "G,hp \<turnstile> (hd stk) ::\<preceq> rT0" by (auto elim: conf_widen widen_trans)
        
    have frame'':
      "correct_frame G hp (ST'',LT'') maxl' ins' ?f'"
    proof -
      from wf hd_stk' len stk' less ST0
      have "approx_stk G hp (hd stk # drop (1+length pt) stk') ST''" 
        by (auto simp add: map_eq_Cons sup_state_conv
                 dest!: approx_stk_append elim: conf_widen)
      moreover
      from wf loc' less
      have "approx_loc G hp loc' LT''" by (simp add: sup_state_conv) blast
      moreover
      note suc_pc' lloc'
      ultimately
      show ?thesis by (simp add: correct_frame_def)
    qed

    with state' frs' f meth hp_ok hd_stk phi_suc frames' meth' phi' class' alloc
    have ?thesis by (simp add: correct_state_def)
  }
  ultimately
  show ?thesis by (cases frs) blast+
qed
  
lemmas [simp] = map_append

lemma Goto_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Goto branch; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done


lemma Ifcmpeq_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Ifcmpeq branch; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done

lemma Pop_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Pop;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1)
apply fast
done

lemma Dup_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Dup;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Dup_x1_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Dup_x1;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Dup_x2_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Dup_x2;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma Swap_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Swap;
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons)
apply (blast intro: conf_widen)
done

lemma IAdd_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = IAdd; 
  wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (clarsimp simp add: defs1 map_eq_Cons approx_val_def conf_def)
apply blast
done

lemma Throw_correct:
"[| wf_prog wt G; 
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); 
  ins ! pc = Throw; 
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs) ; 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd>;
  fst (exec_instr (ins!pc) G hp stk loc C sig pc frs) = None |] 
==> G,phi \<turnstile>JVM state'\<surd>"
  by simp


text {*
  The next theorem collects the results of the sections above,
  i.e.~exception handling and the execution step for each 
  instruction. It states type safety for single step execution:
  in welltyped programs, a conforming state is transformed
  into another conforming state when one instruction is executed.
*}
theorem instr_correct:
"[| wt_jvm_prog G phi;
  method (G,C) sig = Some (C,rT,maxs,maxl,ins,et);
  Some state' = exec (G, None, hp, (stk,loc,C,sig,pc)#frs); 
  G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> |] 
==> G,phi \<turnstile>JVM state'\<surd>"
apply (frule wt_jvm_prog_impl_wt_instr_cor)
apply assumption+
apply (cases "fst (exec_instr (ins!pc) G hp stk loc C sig pc frs)")
defer
apply (erule xcpt_correct, assumption+) 
apply (cases "ins!pc")
prefer 8
apply (rule Invoke_correct, assumption+)
prefer 8
apply (rule Return_correct, assumption+)
prefer 5
apply (rule Getfield_correct, assumption+)
prefer 6
apply (rule Checkcast_correct, assumption+)

apply (unfold wt_jvm_prog_def)
apply (rule Load_correct, assumption+)
apply (rule Store_correct, assumption+)
apply (rule LitPush_correct, assumption+)
apply (rule New_correct, assumption+)
apply (rule Putfield_correct, assumption+)
apply (rule Pop_correct, assumption+)
apply (rule Dup_correct, assumption+)
apply (rule Dup_x1_correct, assumption+)
apply (rule Dup_x2_correct, assumption+)
apply (rule Swap_correct, assumption+)
apply (rule IAdd_correct, assumption+)
apply (rule Goto_correct, assumption+)
apply (rule Ifcmpeq_correct, assumption+)
apply (rule Throw_correct, assumption+)
done

section {* Main *}

lemma correct_state_impl_Some_method:
  "G,phi \<turnstile>JVM (None, hp, (stk,loc,C,sig,pc)#frs)\<surd> 
  ==> \<exists>meth. method (G,C) sig = Some(C,meth)"
by (auto simp add: correct_state_def Let_def)


lemma BV_correct_1 [rule_format]:
"!!state. [| wt_jvm_prog G phi; G,phi \<turnstile>JVM state\<surd>|] 
 ==> exec (G,state) = Some state' --> G,phi \<turnstile>JVM state'\<surd>"
apply (simp only: split_tupled_all)
apply (rename_tac xp hp frs)
apply (case_tac xp)
 apply (case_tac frs)
  apply simp
 apply (simp only: split_tupled_all)
 apply hypsubst
 apply (frule correct_state_impl_Some_method)
 apply (force intro: instr_correct)
apply (case_tac frs)
apply simp_all
done



lemma L0:
  "[| xp=None; frs\<noteq>[] |] ==> (\<exists>state'. exec (G,xp,hp,frs) = Some state')"
by (clarsimp simp add: neq_Nil_conv split_beta)

lemma L1:
  "[|wt_jvm_prog G phi; G,phi \<turnstile>JVM (xp,hp,frs)\<surd>; xp=None; frs\<noteq>[]|] 
  ==> \<exists>state'. exec(G,xp,hp,frs) = Some state' \<and> G,phi \<turnstile>JVM state'\<surd>"
apply (drule L0)
apply assumption
apply (fast intro: BV_correct_1)
done

theorem BV_correct [rule_format]:
"[| wt_jvm_prog G phi; G \<turnstile> s -jvm-> t |] ==> G,phi \<turnstile>JVM s\<surd> --> G,phi \<turnstile>JVM t\<surd>"
apply (unfold exec_all_def)
apply (erule rtrancl_induct)
 apply simp
apply (auto intro: BV_correct_1)
done

theorem BV_correct_implies_approx:
"[| wt_jvm_prog G phi; 
    G \<turnstile> s0 -jvm-> (None,hp,(stk,loc,C,sig,pc)#frs); G,phi \<turnstile>JVM s0 \<surd>|] 
==> approx_stk G hp stk (fst (the (phi C sig ! pc))) \<and> 
    approx_loc G hp loc (snd (the (phi C sig ! pc)))"
apply (drule BV_correct)
apply assumption+
apply (simp add: correct_state_def correct_frame_def split_def 
            split: option.splits)
done

end
