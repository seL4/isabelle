
header {* \section{Generation of Verification Conditions} *}

theory OG_Tactics = OG_Hoare:

lemmas ann_hoare_intros=AnnBasic AnnSeq AnnCond1 AnnCond2 AnnWhile AnnAwait AnnConseq
lemmas oghoare_intros=Parallel Basic Seq Cond While Conseq

lemma ParallelConseqRule: 
 "\<lbrakk> p \<subseteq> (\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts ! i))));  
  \<parallel>- (\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts ! i)))) 
      (Parallel Ts) 
     (\<Inter>i\<in>{i. i<length Ts}. post(Ts ! i));  
  (\<Inter>i\<in>{i. i<length Ts}. post(Ts ! i)) \<subseteq> q \<rbrakk>  
  \<Longrightarrow> \<parallel>- p (Parallel Ts) q"
apply (rule Conseq)
prefer 2 
 apply fast
apply assumption+
done

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> \<parallel>- p (Basic id) q"
apply(rule oghoare_intros)
  prefer 2 apply(rule Basic)
 prefer 2 apply(rule subset_refl)
apply(simp add:Id_def)
done

lemma BasicRule: "p \<subseteq> {s. (f s)\<in>q} \<Longrightarrow> \<parallel>- p (Basic f) q"
apply(rule oghoare_intros)
  prefer 2 apply(rule oghoare_intros)
 prefer 2 apply(rule subset_refl)
apply assumption
done

lemma SeqRule: "\<lbrakk> \<parallel>- p c1 r; \<parallel>- r c2 q \<rbrakk> \<Longrightarrow> \<parallel>- p (Seq c1 c2) q"
apply(rule Seq)
apply fast+
done

lemma CondRule: 
 "\<lbrakk> p \<subseteq> {s. (s\<in>b \<longrightarrow> s\<in>w) \<and> (s\<notin>b \<longrightarrow> s\<in>w')}; \<parallel>- w c1 q; \<parallel>- w' c2 q \<rbrakk> 
  \<Longrightarrow> \<parallel>- p (Cond b c1 c2) q"
apply(rule Cond)
 apply(rule Conseq)
 prefer 4 apply(rule Conseq)
apply simp_all
apply force+
done

lemma WhileRule: "\<lbrakk> p \<subseteq> i; \<parallel>- (i \<inter> b) c i ; (i \<inter> (-b)) \<subseteq> q \<rbrakk>  
        \<Longrightarrow> \<parallel>- p (While b i c) q"
apply(rule Conseq)
 prefer 2 apply(rule While)
apply assumption+
done

text {* Three new proof rules for special instances of the @{text
AnnBasic} and the @{text AnnAwait} commands when the transformation
performed on the state is the identity, and for an @{text AnnAwait}
command where the boolean condition is @{text "{s. True}"}: *}

lemma AnnatomRule:
  "\<lbrakk> atom_com(c); \<parallel>- r c q \<rbrakk>  \<Longrightarrow> \<turnstile> (AnnAwait r {s. True} c) q"
apply(rule AnnAwait)
apply simp_all
done

lemma AnnskipRule:
  "r \<subseteq> q \<Longrightarrow> \<turnstile> (AnnBasic r id) q"
apply(rule AnnBasic)
apply simp
done

lemma AnnwaitRule:
  "\<lbrakk> (r \<inter> b) \<subseteq> q \<rbrakk> \<Longrightarrow> \<turnstile> (AnnAwait r b (Basic id)) q"
apply(rule AnnAwait)
 apply simp
apply(rule BasicRule)
apply simp
done

text {* Lemmata to avoid using the definition of @{text
map_ann_hoare}, @{text interfree_aux}, @{text interfree_swap} and
@{text interfree} by splitting it into different cases: *}

lemma interfree_aux_rule1: "interfree_aux(co, q, None)"
by(simp add:interfree_aux_def)

lemma interfree_aux_rule2: 
  "\<forall>(R,r)\<in>(atomics a). \<parallel>- (q \<inter> R) r q \<Longrightarrow> interfree_aux(None, q, Some a)"
apply(simp add:interfree_aux_def)
apply(force elim:oghoare_sound)
done

lemma interfree_aux_rule3: 
  "(\<forall>(R, r)\<in>(atomics a). \<parallel>- (q \<inter> R) r q \<and> (\<forall>p\<in>(assertions c). \<parallel>- (p \<inter> R) r p))
  \<Longrightarrow> interfree_aux(Some c, q, Some a)"
apply(simp add:interfree_aux_def)
apply(force elim:oghoare_sound)
done

lemma AnnBasic_assertions: 
  "\<lbrakk>interfree_aux(None, r, Some a); interfree_aux(None, q, Some a)\<rbrakk> \<Longrightarrow> 
    interfree_aux(Some (AnnBasic r f), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnSeq_assertions: 
  "\<lbrakk> interfree_aux(Some c1, q, Some a); interfree_aux(Some c2, q, Some a)\<rbrakk>\<Longrightarrow> 
   interfree_aux(Some (AnnSeq c1 c2), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond1_assertions: 
  "\<lbrakk> interfree_aux(None, r, Some a); interfree_aux(Some c1, q, Some a); 
  interfree_aux(Some c2, q, Some a)\<rbrakk>\<Longrightarrow> 
  interfree_aux(Some(AnnCond1 r b c1 c2), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond2_assertions: 
  "\<lbrakk> interfree_aux(None, r, Some a); interfree_aux(Some c, q, Some a)\<rbrakk>\<Longrightarrow> 
  interfree_aux(Some (AnnCond2 r b c), q, Some a)"
apply(simp add: interfree_aux_def)
by force

lemma AnnWhile_assertions: 
  "\<lbrakk> interfree_aux(None, r, Some a); interfree_aux(None, i, Some a); 
  interfree_aux(Some c, q, Some a)\<rbrakk>\<Longrightarrow> 
  interfree_aux(Some (AnnWhile r b i c), q, Some a)"
apply(simp add: interfree_aux_def)
by force
 
lemma AnnAwait_assertions: 
  "\<lbrakk> interfree_aux(None, r, Some a); interfree_aux(None, q, Some a)\<rbrakk>\<Longrightarrow> 
  interfree_aux(Some (AnnAwait r b c), q, Some a)"
apply(simp add: interfree_aux_def)
by force
 
lemma AnnBasic_atomics: 
  "\<parallel>- (q \<inter> r) (Basic f) q \<Longrightarrow> interfree_aux(None, q, Some (AnnBasic r f))"
by(simp add: interfree_aux_def oghoare_sound)

lemma AnnSeq_atomics: 
  "\<lbrakk> interfree_aux(Any, q, Some a1); interfree_aux(Any, q, Some a2)\<rbrakk>\<Longrightarrow> 
  interfree_aux(Any, q, Some (AnnSeq a1 a2))"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond1_atomics:
  "\<lbrakk> interfree_aux(Any, q, Some a1); interfree_aux(Any, q, Some a2)\<rbrakk>\<Longrightarrow> 
   interfree_aux(Any, q, Some (AnnCond1 r b a1 a2))"
apply(simp add: interfree_aux_def)
by force

lemma AnnCond2_atomics: 
  "interfree_aux (Any, q, Some a)\<Longrightarrow> interfree_aux(Any, q, Some (AnnCond2 r b a))"
by(simp add: interfree_aux_def)

lemma AnnWhile_atomics: "interfree_aux (Any, q, Some a) 
     \<Longrightarrow> interfree_aux(Any, q, Some (AnnWhile r b i a))"
by(simp add: interfree_aux_def)

lemma Annatom_atomics: 
  "\<parallel>- (q \<inter> r) a q \<Longrightarrow> interfree_aux (None, q, Some (AnnAwait r {x. True} a))"
by(simp add: interfree_aux_def oghoare_sound) 

lemma AnnAwait_atomics: 
  "\<parallel>- (q \<inter> (r \<inter> b)) a q \<Longrightarrow> interfree_aux (None, q, Some (AnnAwait r b a))"
by(simp add: interfree_aux_def oghoare_sound)

constdefs 
  interfree_swap :: "('a ann_triple_op * ('a ann_triple_op) list) \<Rightarrow> bool"
  "interfree_swap == \<lambda>(x, xs). \<forall>y\<in>set xs. interfree_aux (com x, post x, com y)
  \<and> interfree_aux(com y, post y, com x)"

lemma interfree_swap_Empty: "interfree_swap (x, [])"
by(simp add:interfree_swap_def)

lemma interfree_swap_List:  
  "\<lbrakk> interfree_aux (com x, post x, com y); 
  interfree_aux (com y, post y ,com x); interfree_swap (x, xs) \<rbrakk> 
  \<Longrightarrow> interfree_swap (x, y#xs)"
by(simp add:interfree_swap_def)

lemma interfree_swap_Map: "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> interfree_aux (com x, post x, c k) 
 \<and> interfree_aux (c k, Q k, com x)   
 \<Longrightarrow> interfree_swap (x, map (\<lambda>k. (c k, Q k)) [i..j(])"
by(force simp add: interfree_swap_def less_diff_conv)

lemma interfree_Empty: "interfree []"
by(simp add:interfree_def)

lemma interfree_List: 
  "\<lbrakk> interfree_swap(x, xs); interfree xs \<rbrakk> \<Longrightarrow> interfree (x#xs)"
apply(simp add:interfree_def interfree_swap_def)
apply clarify
apply(case_tac i)
 apply(case_tac j)
  apply simp_all
apply(case_tac j,simp+)
done

lemma interfree_Map: 
  "(\<forall>i j. a\<le>i \<and> i<b \<and> a\<le>j \<and> j<b  \<and> i\<noteq>j \<longrightarrow> interfree_aux (c i, Q i, c j))  
  \<Longrightarrow> interfree (map (\<lambda>k. (c k, Q k)) [a..b(])"
by(force simp add: interfree_def less_diff_conv)

constdefs map_ann_hoare :: "(('a ann_com_op * 'a assn) list) \<Rightarrow> bool " ("[\<turnstile>] _" [0] 45)
  "[\<turnstile>] Ts == (\<forall>i<length Ts. \<exists>c q. Ts!i=(Some c, q) \<and> \<turnstile> c q)"

lemma MapAnnEmpty: "[\<turnstile>] []"
by(simp add:map_ann_hoare_def)

lemma MapAnnList: "\<lbrakk> \<turnstile> c q ; [\<turnstile>] xs \<rbrakk> \<Longrightarrow> [\<turnstile>] (Some c,q)#xs"
apply(simp add:map_ann_hoare_def)
apply clarify
apply(case_tac i,simp+)
done

lemma MapAnnMap: 
  "\<forall>k. i\<le>k \<and> k<j \<longrightarrow> \<turnstile> (c k) (Q k) \<Longrightarrow> [\<turnstile>] map (\<lambda>k. (Some (c k), Q k)) [i..j(]"
apply(simp add: map_ann_hoare_def less_diff_conv)
done

lemma ParallelRule:"\<lbrakk> [\<turnstile>] Ts ; interfree Ts \<rbrakk>
  \<Longrightarrow> \<parallel>- (\<Inter>i\<in>{i. i<length Ts}. pre(the(com(Ts!i)))) 
          Parallel Ts 
        (\<Inter>i\<in>{i. i<length Ts}. post(Ts!i))"
apply(rule Parallel)
 apply(simp add:map_ann_hoare_def)
apply simp
done
(*
lemma ParamParallelRule:
 "\<lbrakk> \<forall>k<n. \<turnstile> (c k) (Q k); 
   \<forall>k l. k<n \<and> l<n  \<and> k\<noteq>l \<longrightarrow> interfree_aux (Some(c k), Q k, Some(c l)) \<rbrakk>
  \<Longrightarrow> \<parallel>- (\<Inter>i\<in>{i. i<n} . pre(c i)) COBEGIN SCHEME [0\<le>i<n] (c i) (Q i) COEND  (\<Inter>i\<in>{i. i<n} . Q i )"
apply(rule ParallelConseqRule)
  apply simp
  apply clarify
  apply force
 apply(rule ParallelRule)
  apply(rule MapAnnMap)
  apply simp
 apply(rule interfree_Map)
 apply simp
apply simp
apply clarify
apply force
done
*)

text {* The following are some useful lemmas and simplification
tactics to control which theorems are used to simplify at each moment,
so that the original input does not suffer any unexpected
transformation. *}

lemma Compl_Collect: "-(Collect b) = {x. \<not>(b x)}"
by fast
lemma list_length: "length []=0 \<and> length (x#xs) = Suc(length xs)"
by simp
lemma list_lemmas: "length []=0 \<and> length (x#xs) = Suc(length xs) 
\<and> (x#xs) ! 0=x \<and> (x#xs) ! Suc n = xs ! n"
by simp
lemma le_Suc_eq_insert: "{i. i <Suc n} = insert n {i. i< n}"
apply auto
by arith
lemmas primrecdef_list = "pre.simps" "assertions.simps" "atomics.simps" "atom_com.simps"
lemmas my_simp_list = list_lemmas fst_conv snd_conv
not_less0 refl le_Suc_eq_insert Suc_not_Zero Zero_not_Suc Suc_Suc_eq
Collect_mem_eq ball_simps option.simps primrecdef_list
lemmas ParallelConseq_list = INTER_def Collect_conj_eq length_map length_upt length_append list_length

ML {*
val before_interfree_simp_tac = (simp_tac (HOL_basic_ss addsimps [thm "com.simps", thm "post.simps"]))

val  interfree_simp_tac = (asm_simp_tac (HOL_ss addsimps [thm "split", thm "ball_Un", thm "ball_empty"]@(thms "my_simp_list")))

val ParallelConseq = (simp_tac (HOL_basic_ss addsimps (thms "ParallelConseq_list")@(thms "my_simp_list")))
*}

text {* The following tactic applies @{text tac} to each conjunct in a
subgoal of the form @{text "A \<Longrightarrow> a1 \<and> a2 \<and> .. \<and> an"}  returning
@{text n} subgoals, one for each conjunct: *}

ML {*
fun conjI_Tac tac i st = st |>
       ( (EVERY [rtac conjI i,
          conjI_Tac tac (i+1),
          tac i]) ORELSE (tac i) )
*}


subsubsection {* Tactic for the generation of the verification conditions *} 

text {* The tactic basically uses two subtactics:

\begin{description}

\item[HoareRuleTac] is called at the level of parallel programs, it        
 uses the ParallelTac to solve parallel composition of programs.         
 This verification has two parts, namely, (1) all component programs are 
 correct and (2) they are interference free.  @{text HoareRuleTac} is
 also called at the level of atomic regions, i.e.  @{text "\<langle> \<rangle>"} and
 @{text "AWAIT b THEN _ END"}, and at each interference freedom test.

\item[AnnHoareRuleTac] is for component programs which  
 are annotated programs and so, there are not unknown assertions         
 (no need to use the parameter precond, see NOTE).

 NOTE: precond(::bool) informs if the subgoal has the form @{text "\<parallel>- ?p c q"},
 in this case we have precond=False and the generated  verification     
 condition would have the form @{text "?p \<subseteq> \<dots>"} which can be solved by        
 @{text "rtac subset_refl"}, if True we proceed to simplify it using
 the simplification tactics above.

\end{description}
*}

ML {*

 fun WlpTac i = (rtac (thm "SeqRule") i) THEN (HoareRuleTac false (i+1))
and HoareRuleTac precond i st = st |>  
    ( (WlpTac i THEN HoareRuleTac precond i)
      ORELSE
      (FIRST[rtac (thm "SkipRule") i,
             rtac (thm "BasicRule") i,
             EVERY[rtac (thm "ParallelConseqRule") i,
                   ParallelConseq (i+2),
                   ParallelTac (i+1),
                   ParallelConseq i], 
             EVERY[rtac (thm "CondRule") i,
                   HoareRuleTac false (i+2),
                   HoareRuleTac false (i+1)],
             EVERY[rtac (thm "WhileRule") i,
                   HoareRuleTac true (i+1)],
             K all_tac i ]
       THEN (if precond then (K all_tac i) else (rtac (thm "subset_refl") i))))

and  AnnWlpTac i = (rtac (thm "AnnSeq") i) THEN (AnnHoareRuleTac (i+1))
and AnnHoareRuleTac i st = st |>  
    ( (AnnWlpTac i THEN AnnHoareRuleTac i )
     ORELSE
      (FIRST[(rtac (thm "AnnskipRule") i),
             EVERY[rtac (thm "AnnatomRule") i,
                   HoareRuleTac true (i+1)],
             (rtac (thm "AnnwaitRule") i),
             rtac (thm "AnnBasic") i,
             EVERY[rtac (thm "AnnCond1") i,
                   AnnHoareRuleTac (i+3),
                   AnnHoareRuleTac (i+1)],
             EVERY[rtac (thm "AnnCond2") i,
                   AnnHoareRuleTac (i+1)],
             EVERY[rtac (thm "AnnWhile") i,
                   AnnHoareRuleTac (i+2)],
             EVERY[rtac (thm "AnnAwait") i,
                   HoareRuleTac true (i+1)],
             K all_tac i]))

and ParallelTac i = EVERY[rtac (thm "ParallelRule") i,
                          interfree_Tac (i+1),
                           MapAnn_Tac i]

and MapAnn_Tac i st = st |>
    (FIRST[rtac (thm "MapAnnEmpty") i,
           EVERY[rtac (thm "MapAnnList") i,
                 MapAnn_Tac (i+1),
                 AnnHoareRuleTac i],
           EVERY[rtac (thm "MapAnnMap") i,
                 rtac (thm "allI") i,rtac (thm "impI") i,
                 AnnHoareRuleTac i]])

and interfree_swap_Tac i st = st |>
    (FIRST[rtac (thm "interfree_swap_Empty") i,
           EVERY[rtac (thm "interfree_swap_List") i,
                 interfree_swap_Tac (i+2),
                 interfree_aux_Tac (i+1),
                 interfree_aux_Tac i ],
           EVERY[rtac (thm "interfree_swap_Map") i,
                 rtac (thm "allI") i,rtac (thm "impI") i,
                 conjI_Tac (interfree_aux_Tac) i]])

and interfree_Tac i st = st |> 
   (FIRST[rtac (thm "interfree_Empty") i,
          EVERY[rtac (thm "interfree_List") i,
                interfree_Tac (i+1),
                interfree_swap_Tac i],
          EVERY[rtac (thm "interfree_Map") i,
                rtac (thm "allI") i,rtac (thm "allI") i,rtac (thm "impI") i,
                interfree_aux_Tac i ]])

and interfree_aux_Tac i = (before_interfree_simp_tac i ) THEN 
        (FIRST[rtac (thm "interfree_aux_rule1") i,
               dest_assertions_Tac i])

and dest_assertions_Tac i st = st |>
    (FIRST[EVERY[rtac (thm "AnnBasic_assertions") i,
                 dest_atomics_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnSeq_assertions") i,
                 dest_assertions_Tac (i+1),
                 dest_assertions_Tac i],
           EVERY[rtac (thm "AnnCond1_assertions") i,
                 dest_assertions_Tac (i+2),
                 dest_assertions_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnCond2_assertions") i,
                 dest_assertions_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnWhile_assertions") i,
                 dest_assertions_Tac (i+2),
                 dest_atomics_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnAwait_assertions") i,
                 dest_atomics_Tac (i+1),
                 dest_atomics_Tac i],
           dest_atomics_Tac i])

and dest_atomics_Tac i st = st |>
    (FIRST[EVERY[rtac (thm "AnnBasic_atomics") i,
                 HoareRuleTac true i],
           EVERY[rtac (thm "AnnSeq_atomics") i,
                 dest_atomics_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnCond1_atomics") i,
                 dest_atomics_Tac (i+1),
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnCond2_atomics") i,
                 dest_atomics_Tac i],
           EVERY[rtac (thm "AnnWhile_atomics") i,
                 dest_atomics_Tac i],
           EVERY[rtac (thm "Annatom_atomics") i,
                 HoareRuleTac true i],
           EVERY[rtac (thm "AnnAwait_atomics") i,
                 HoareRuleTac true i],
                 K all_tac i])
*}


text {* The final tactic is given the name @{text oghoare}: *}

ML {* 
fun oghoare_tac i thm = SUBGOAL (fn (term, _) =>
   (HoareRuleTac true i)) i thm
*}

text {* Notice that the tactic for parallel programs @{text
"oghoare_tac"} is initially invoked with the value @{text true} for
the parameter @{text precond}.

Parts of the tactic can be also individually used to generate the
verification conditions for annotated sequential programs and to
generate verification conditions out of interference freedom tests: *}

ML {* fun annhoare_tac i thm = SUBGOAL (fn (term, _) =>
  (AnnHoareRuleTac i)) i thm

fun interfree_aux_tac i thm = SUBGOAL (fn (term, _) =>
   (interfree_aux_Tac i)) i thm
*}

text {* The so defined ML tactics are then ``exported'' to be used in
Isabelle proofs. *}

method_setup oghoare = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (oghoare_tac)) *}
  "verification condition generator for the oghoare logic"

method_setup annhoare = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (annhoare_tac)) *}
  "verification condition generator for the ann_hoare logic"

method_setup interfree_aux = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (interfree_aux_tac)) *}
  "verification condition generator for interference freedom tests"

text {* Tactics useful for dealing with the generated verification conditions: *}

method_setup conjI_tac = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (conjI_Tac (K all_tac))) *}
  "verification condition generator for interference freedom tests"

ML {*
fun disjE_Tac tac i st = st |>
       ( (EVERY [etac disjE i,
          disjE_Tac tac (i+1),
          tac i]) ORELSE (tac i) )
*}

method_setup disjE_tac = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (disjE_Tac (K all_tac))) *}
  "verification condition generator for interference freedom tests"

end