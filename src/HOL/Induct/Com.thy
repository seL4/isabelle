(*  Title:      HOL/Induct/Com
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Example of Mutual Induction via Iteratived Inductive Definitions: Commands
*)

theory Com = Main:

typedecl loc

types  state = "loc => nat"
       n2n2n = "nat => nat => nat"

arities loc :: type

datatype
  exp = N nat
      | X loc
      | Op n2n2n exp exp
      | valOf com exp          ("VALOF _ RESULTIS _"  60)
and
  com = SKIP
      | ":="  loc exp          (infixl  60)
      | Semi  com com          ("_;;_"  [60, 60] 60)
      | Cond  exp com com      ("IF _ THEN _ ELSE _"  60)
      | While exp com          ("WHILE _ DO _"  60)

text{* Execution of commands *}
consts  exec    :: "((exp*state) * (nat*state)) set => ((com*state)*state)set"
       "@exec"  :: "((exp*state) * (nat*state)) set => 
                    [com*state,state] => bool"     ("_/ -[_]-> _" [50,0,50] 50)

translations  "csig -[eval]-> s" == "(csig,s) \<in> exec eval"

syntax  eval'   :: "[exp*state,nat*state] => 
		    ((exp*state) * (nat*state)) set => bool"
					   ("_/ -|[_]-> _" [50,0,50] 50)

translations
    "esig -|[eval]-> ns" => "(esig,ns) \<in> eval"

text{*Command execution.  Natural numbers represent Booleans: 0=True, 1=False*}
inductive "exec eval"
  intros
    Skip:    "(SKIP,s) -[eval]-> s"

    Assign:  "(e,s) -|[eval]-> (v,s') ==> (x := e, s) -[eval]-> s'(x:=v)"

    Semi:    "[| (c0,s) -[eval]-> s2; (c1,s2) -[eval]-> s1 |] 
             ==> (c0 ;; c1, s) -[eval]-> s1"

    IfTrue: "[| (e,s) -|[eval]-> (0,s');  (c0,s') -[eval]-> s1 |] 
             ==> (IF e THEN c0 ELSE c1, s) -[eval]-> s1"

    IfFalse: "[| (e,s) -|[eval]->  (Suc 0, s');  (c1,s') -[eval]-> s1 |] 
              ==> (IF e THEN c0 ELSE c1, s) -[eval]-> s1"

    WhileFalse: "(e,s) -|[eval]-> (Suc 0, s1) 
                 ==> (WHILE e DO c, s) -[eval]-> s1"

    WhileTrue:  "[| (e,s) -|[eval]-> (0,s1);
                    (c,s1) -[eval]-> s2;  (WHILE e DO c, s2) -[eval]-> s3 |] 
                 ==> (WHILE e DO c, s) -[eval]-> s3"

declare exec.intros [intro]


inductive_cases
	[elim!]: "(SKIP,s) -[eval]-> t"
    and [elim!]: "(x:=a,s) -[eval]-> t"
    and	[elim!]: "(c1;;c2, s) -[eval]-> t"
    and	[elim!]: "(IF e THEN c1 ELSE c2, s) -[eval]-> t"
    and	exec_WHILE_case: "(WHILE b DO c,s) -[eval]-> t"


text{*Justifies using "exec" in the inductive definition of "eval"*}
lemma exec_mono: "A<=B ==> exec(A) <= exec(B)"
apply (unfold exec.defs )
apply (rule lfp_mono)
apply (assumption | rule basic_monos)+
done

ML {*
Unify.trace_bound := 30;
Unify.search_bound := 60;
*}

text{*Command execution is functional (deterministic) provided evaluation is*}
theorem single_valued_exec: "single_valued ev ==> single_valued(exec ev)"
apply (simp add: single_valued_def)
apply (intro allI) 
apply (rule impI)
apply (erule exec.induct)
apply (blast elim: exec_WHILE_case)+
done


section {* Expressions *}

text{* Evaluation of arithmetic expressions *}
consts  eval    :: "((exp*state) * (nat*state)) set"
       "-|->"   :: "[exp*state,nat*state] => bool"         (infixl 50)

translations
    "esig -|-> (n,s)" <= "(esig,n,s) \<in> eval"
    "esig -|-> ns"    == "(esig,ns ) \<in> eval"
  
inductive eval
  intros 
    N [intro!]: "(N(n),s) -|-> (n,s)"

    X [intro!]: "(X(x),s) -|-> (s(x),s)"

    Op [intro]: "[| (e0,s) -|-> (n0,s0);  (e1,s0)  -|-> (n1,s1) |] 
                 ==> (Op f e0 e1, s) -|-> (f n0 n1, s1)"

    valOf [intro]: "[| (c,s) -[eval]-> s0;  (e,s0)  -|-> (n,s1) |] 
                    ==> (VALOF c RESULTIS e, s) -|-> (n, s1)"

  monos exec_mono


inductive_cases
	[elim!]: "(N(n),sigma) -|-> (n',s')"
    and [elim!]: "(X(x),sigma) -|-> (n,s')"
    and	[elim!]: "(Op f a1 a2,sigma)  -|-> (n,s')"
    and	[elim!]: "(VALOF c RESULTIS e, s) -|-> (n, s1)"


lemma var_assign_eval [intro!]: "(X x, s(x:=n)) -|-> (n, s(x:=n))"
by (rule fun_upd_same [THEN subst], fast)


text{* Make the induction rule look nicer -- though eta_contract makes the new
    version look worse than it is...*}

lemma split_lemma:
     "{((e,s),(n,s')). P e s n s'} = Collect (split (%v. split (split P v)))"
by auto

text{*New induction rule.  Note the form of the VALOF induction hypothesis*}
lemma eval_induct:
  "[| (e,s) -|-> (n,s');                                          
      !!n s. P (N n) s n s;                                       
      !!s x. P (X x) s (s x) s;                                   
      !!e0 e1 f n0 n1 s s0 s1.                                    
         [| (e0,s) -|-> (n0,s0); P e0 s n0 s0;                    
            (e1,s0) -|-> (n1,s1); P e1 s0 n1 s1                   
         |] ==> P (Op f e0 e1) s (f n0 n1) s1;                    
      !!c e n s s0 s1.                                            
         [| (c,s) -[eval Int {((e,s),(n,s')). P e s n s'}]-> s0;  
            (c,s) -[eval]-> s0;                                   
            (e,s0) -|-> (n,s1); P e s0 n s1 |]                    
         ==> P (VALOF c RESULTIS e) s n s1                        
   |] ==> P e s n s'"
apply (erule eval.induct, blast) 
apply blast 
apply blast 
apply (frule Int_lower1 [THEN exec_mono, THEN subsetD])
apply (auto simp add: split_lemma)
done


text{*Lemma for Function_eval.  The major premise is that (c,s) executes to s1
  using eval restricted to its functional part.  Note that the execution
  (c,s) -[eval]-> s2 can use unrestricted eval!  The reason is that 
  the execution (c,s) -[eval Int {...}]-> s1 assures us that execution is
  functional on the argument (c,s).
*}
lemma com_Unique:
 "(c,s) -[eval Int {((e,s),(n,t)). \<forall>nt'. (e,s) -|-> nt' --> (n,t)=nt'}]-> s1  
  ==> \<forall>s2. (c,s) -[eval]-> s2 --> s2=s1"
apply (erule exec.induct, simp_all)
      apply blast
     apply force
    apply blast
   apply blast
  apply blast
 apply (blast elim: exec_WHILE_case)
apply (erule_tac V = "(?c,s2) -[?ev]-> s3" in thin_rl)
apply clarify
apply (erule exec_WHILE_case, blast+) 
done


text{*Expression evaluation is functional, or deterministic*}
theorem single_valued_eval: "single_valued eval"
apply (unfold single_valued_def)
apply (intro allI, rule impI) 
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule eval_induct)
apply (drule_tac [4] com_Unique)
apply (simp_all (no_asm_use))
apply blast+
done


lemma eval_N_E_lemma: "(e,s) -|-> (v,s') ==> (e = N n) --> (v=n & s'=s)"
by (erule eval_induct, simp_all)

lemmas eval_N_E [dest!] = eval_N_E_lemma [THEN mp, OF _ refl]


text{*This theorem says that "WHILE TRUE DO c" cannot terminate*}
lemma while_true_E [rule_format]:
     "(c', s) -[eval]-> t ==> (c' = WHILE (N 0) DO c) --> False"
by (erule exec.induct, auto)


subsection{* Equivalence of IF e THEN c;;(WHILE e DO c) ELSE SKIP  and  
       WHILE e DO c *}

lemma while_if1 [rule_format]:
     "(c',s) -[eval]-> t 
      ==> (c' = WHILE e DO c) -->  
          (IF e THEN c;;c' ELSE SKIP, s) -[eval]-> t"
by (erule exec.induct, auto)

lemma while_if2 [rule_format]:
     "(c',s) -[eval]-> t
      ==> (c' = IF e THEN c;;(WHILE e DO c) ELSE SKIP) -->  
          (WHILE e DO c, s) -[eval]-> t"
by (erule exec.induct, auto)


theorem while_if:
     "((IF e THEN c;;(WHILE e DO c) ELSE SKIP, s) -[eval]-> t)  =   
      ((WHILE e DO c, s) -[eval]-> t)"
by (blast intro: while_if1 while_if2)



subsection{* Equivalence of  (IF e THEN c1 ELSE c2);;c
                         and  IF e THEN (c1;;c) ELSE (c2;;c)   *}

lemma if_semi1 [rule_format]:
     "(c',s) -[eval]-> t
      ==> (c' = (IF e THEN c1 ELSE c2);;c) -->  
          (IF e THEN (c1;;c) ELSE (c2;;c), s) -[eval]-> t"
by (erule exec.induct, auto)

lemma if_semi2 [rule_format]:
     "(c',s) -[eval]-> t
      ==> (c' = IF e THEN (c1;;c) ELSE (c2;;c)) -->  
          ((IF e THEN c1 ELSE c2);;c, s) -[eval]-> t"
by (erule exec.induct, auto)

theorem if_semi: "(((IF e THEN c1 ELSE c2);;c, s) -[eval]-> t)  =   
                  ((IF e THEN (c1;;c) ELSE (c2;;c), s) -[eval]-> t)"
by (blast intro: if_semi1 if_semi2)



subsection{* Equivalence of  VALOF c1 RESULTIS (VALOF c2 RESULTIS e)
                  and  VALOF c1;;c2 RESULTIS e
 *}

lemma valof_valof1 [rule_format]:
     "(e',s) -|-> (v,s')  
      ==> (e' = VALOF c1 RESULTIS (VALOF c2 RESULTIS e)) -->  
          (VALOF c1;;c2 RESULTIS e, s) -|-> (v,s')"
by (erule eval_induct, auto)


lemma valof_valof2 [rule_format]:
     "(e',s) -|-> (v,s')
      ==> (e' = VALOF c1;;c2 RESULTIS e) -->  
          (VALOF c1 RESULTIS (VALOF c2 RESULTIS e), s) -|-> (v,s')"
by (erule eval_induct, auto)

theorem valof_valof:
     "((VALOF c1 RESULTIS (VALOF c2 RESULTIS e), s) -|-> (v,s'))  =   
      ((VALOF c1;;c2 RESULTIS e, s) -|-> (v,s'))"
by (blast intro: valof_valof1 valof_valof2)


subsection{* Equivalence of  VALOF SKIP RESULTIS e  and  e *}

lemma valof_skip1 [rule_format]:
     "(e',s) -|-> (v,s')
      ==> (e' = VALOF SKIP RESULTIS e) -->  
          (e, s) -|-> (v,s')"
by (erule eval_induct, auto)

lemma valof_skip2:
     "(e,s) -|-> (v,s') ==> (VALOF SKIP RESULTIS e, s) -|-> (v,s')"
by blast

theorem valof_skip:
     "((VALOF SKIP RESULTIS e, s) -|-> (v,s'))  =  ((e, s) -|-> (v,s'))"
by (blast intro: valof_skip1 valof_skip2)


subsection{* Equivalence of  VALOF x:=e RESULTIS x  and  e *}

lemma valof_assign1 [rule_format]:
     "(e',s) -|-> (v,s'')
      ==> (e' = VALOF x:=e RESULTIS X x) -->  
          (\<exists>s'. (e, s) -|-> (v,s') & (s'' = s'(x:=v)))"
apply (erule eval_induct)
apply (simp_all del: fun_upd_apply, clarify, auto) 
done

lemma valof_assign2:
     "(e,s) -|-> (v,s') ==> (VALOF x:=e RESULTIS X x, s) -|-> (v,s'(x:=v))"
by blast


end
