(*  Title:      HOL/HOLCF/IOA/meta_theory/CompoScheds.thy
    Author:     Olaf Müller
*)

header {* Compositionality on Schedule level *}

theory CompoScheds
imports CompoExecs
begin

definition
  mkex2 :: "('a,'s)ioa => ('a,'t)ioa => 'a Seq ->
              ('a,'s)pairs -> ('a,'t)pairs ->
              ('s => 't => ('a,'s*'t)pairs)" where
  "mkex2 A B = (fix$(LAM h sch exA exB. (%s t. case sch of
       nil => nil
    | x##xs =>
      (case x of
        UU => UU
      | Def y =>
         (if y:act A then
             (if y:act B then
                (case HD$exA of
                   UU => UU
                 | Def a => (case HD$exB of
                              UU => UU
                            | Def b =>
                   (y,(snd a,snd b))>>
                     (h$xs$(TL$exA)$(TL$exB)) (snd a) (snd b)))
              else
                (case HD$exA of
                   UU => UU
                 | Def a =>
                   (y,(snd a,t))>>(h$xs$(TL$exA)$exB) (snd a) t)
              )
          else
             (if y:act B then
                (case HD$exB of
                   UU => UU
                 | Def b =>
                   (y,(s,snd b))>>(h$xs$exA$(TL$exB)) s (snd b))
             else
               UU
             )
         )
       ))))"

definition
  mkex :: "('a,'s)ioa => ('a,'t)ioa => 'a Seq =>
              ('a,'s)execution => ('a,'t)execution =>('a,'s*'t)execution" where
  "mkex A B sch exA exB =
       ((fst exA,fst exB),
        (mkex2 A B$sch$(snd exA)$(snd exB)) (fst exA) (fst exB))"

definition
  par_scheds ::"['a schedule_module,'a schedule_module] => 'a schedule_module" where
  "par_scheds SchedsA SchedsB =
      (let schA = fst SchedsA; sigA = snd SchedsA;
           schB = fst SchedsB; sigB = snd SchedsB
       in
       (    {sch. Filter (%a. a:actions sigA)$sch : schA}
        Int {sch. Filter (%a. a:actions sigB)$sch : schB}
        Int {sch. Forall (%x. x:(actions sigA Un actions sigB)) sch},
        asig_comp sigA sigB))"


subsection "mkex rewrite rules"


lemma mkex2_unfold:
"mkex2 A B = (LAM sch exA exB. (%s t. case sch of
      nil => nil
   | x##xs =>
     (case x of
       UU => UU
     | Def y =>
        (if y:act A then
            (if y:act B then
               (case HD$exA of
                  UU => UU
                | Def a => (case HD$exB of
                             UU => UU
                           | Def b =>
                  (y,(snd a,snd b))>>
                    (mkex2 A B$xs$(TL$exA)$(TL$exB)) (snd a) (snd b)))
             else
               (case HD$exA of
                  UU => UU
                | Def a =>
                  (y,(snd a,t))>>(mkex2 A B$xs$(TL$exA)$exB) (snd a) t)
             )
         else
            (if y:act B then
               (case HD$exB of
                  UU => UU
                | Def b =>
                  (y,(s,snd b))>>(mkex2 A B$xs$exA$(TL$exB)) s (snd b))
            else
              UU
            )
        )
      )))"
apply (rule trans)
apply (rule fix_eq2)
apply (simp only: mkex2_def)
apply (rule beta_cfun)
apply simp
done

lemma mkex2_UU: "(mkex2 A B$UU$exA$exB) s t = UU"
apply (subst mkex2_unfold)
apply simp
done

lemma mkex2_nil: "(mkex2 A B$nil$exA$exB) s t= nil"
apply (subst mkex2_unfold)
apply simp
done

lemma mkex2_cons_1: "[| x:act A; x~:act B; HD$exA=Def a|]
    ==> (mkex2 A B$(x>>sch)$exA$exB) s t =
        (x,snd a,t) >> (mkex2 A B$sch$(TL$exA)$exB) (snd a) t"
apply (rule trans)
apply (subst mkex2_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

lemma mkex2_cons_2: "[| x~:act A; x:act B; HD$exB=Def b|]
    ==> (mkex2 A B$(x>>sch)$exA$exB) s t =
        (x,s,snd b) >> (mkex2 A B$sch$exA$(TL$exB)) s (snd b)"
apply (rule trans)
apply (subst mkex2_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

lemma mkex2_cons_3: "[| x:act A; x:act B; HD$exA=Def a;HD$exB=Def b|]
    ==> (mkex2 A B$(x>>sch)$exA$exB) s t =
         (x,snd a,snd b) >>
            (mkex2 A B$sch$(TL$exA)$(TL$exB)) (snd a) (snd b)"
apply (rule trans)
apply (subst mkex2_unfold)
apply (simp add: Consq_def If_and_if)
apply (simp add: Consq_def)
done

declare mkex2_UU [simp] mkex2_nil [simp] mkex2_cons_1 [simp]
  mkex2_cons_2 [simp] mkex2_cons_3 [simp]


subsection {* mkex *}

lemma mkex_UU: "mkex A B UU  (s,exA) (t,exB) = ((s,t),UU)"
apply (simp add: mkex_def)
done

lemma mkex_nil: "mkex A B nil (s,exA) (t,exB) = ((s,t),nil)"
apply (simp add: mkex_def)
done

lemma mkex_cons_1: "[| x:act A; x~:act B |]
    ==> mkex A B (x>>sch) (s,a>>exA) (t,exB)  =
        ((s,t), (x,snd a,t) >> snd (mkex A B sch (snd a,exA) (t,exB)))"
apply (simp (no_asm) add: mkex_def)
apply (cut_tac exA = "a>>exA" in mkex2_cons_1)
apply auto
done

lemma mkex_cons_2: "[| x~:act A; x:act B |]
    ==> mkex A B (x>>sch) (s,exA) (t,b>>exB) =
        ((s,t), (x,s,snd b) >> snd (mkex A B sch (s,exA) (snd b,exB)))"
apply (simp (no_asm) add: mkex_def)
apply (cut_tac exB = "b>>exB" in mkex2_cons_2)
apply auto
done

lemma mkex_cons_3: "[| x:act A; x:act B |]
    ==>  mkex A B (x>>sch) (s,a>>exA) (t,b>>exB) =
         ((s,t), (x,snd a,snd b) >> snd (mkex A B sch (snd a,exA) (snd b,exB)))"
apply (simp (no_asm) add: mkex_def)
apply (cut_tac exB = "b>>exB" and exA = "a>>exA" in mkex2_cons_3)
apply auto
done

declare mkex2_UU [simp del] mkex2_nil [simp del]
  mkex2_cons_1 [simp del] mkex2_cons_2 [simp del] mkex2_cons_3 [simp del]

lemmas composch_simps = mkex_UU mkex_nil mkex_cons_1 mkex_cons_2 mkex_cons_3

declare composch_simps [simp]


subsection {* COMPOSITIONALITY on SCHEDULE Level *}

subsubsection "Lemmas for ==>"

(* --------------------------------------------------------------------- *)
(*    Lemma_2_1 :  tfilter(ex) and filter_act are commutative            *)
(* --------------------------------------------------------------------- *)

lemma lemma_2_1a:
   "filter_act$(Filter_ex2 (asig_of A)$xs)=
    Filter (%a. a:act A)$(filter_act$xs)"

apply (unfold filter_act_def Filter_ex2_def)
apply (simp (no_asm) add: MapFilter o_def)
done


(* --------------------------------------------------------------------- *)
(*    Lemma_2_2 : State-projections do not affect filter_act             *)
(* --------------------------------------------------------------------- *)

lemma lemma_2_1b:
   "filter_act$(ProjA2$xs) =filter_act$xs &
    filter_act$(ProjB2$xs) =filter_act$xs"
apply (tactic {* pair_induct_tac @{context} "xs" [] 1 *})
done


(* --------------------------------------------------------------------- *)
(*             Schedules of A||B have only  A- or B-actions              *)
(* --------------------------------------------------------------------- *)

(* very similar to lemma_1_1c, but it is not checking if every action element of
   an ex is in A or B, but after projecting it onto the action schedule. Of course, this
   is the same proposition, but we cannot change this one, when then rather lemma_1_1c  *)

lemma sch_actions_in_AorB: "!s. is_exec_frag (A||B) (s,xs)
   --> Forall (%x. x:act (A||B)) (filter_act$xs)"

apply (tactic {* pair_induct_tac @{context} "xs" [@{thm is_exec_frag_def}, @{thm Forall_def},
  @{thm sforall_def}] 1 *})
(* main case *)
apply auto
apply (simp add: trans_of_defs2 actions_asig_comp asig_of_par)
done


subsubsection "Lemmas for <=="

(*---------------------------------------------------------------------------
    Filtering actions out of mkex(sch,exA,exB) yields the oracle sch
                             structural induction
  --------------------------------------------------------------------------- *)

lemma Mapfst_mkex_is_sch: "! exA exB s t.
  Forall (%x. x:act (A||B)) sch  &
  Filter (%a. a:act A)$sch << filter_act$exA &
  Filter (%a. a:act B)$sch << filter_act$exB
  --> filter_act$(snd (mkex A B sch (s,exA) (t,exB))) = sch"

apply (tactic {* Seq_induct_tac @{context} "sch" [@{thm Filter_def}, @{thm Forall_def},
  @{thm sforall_def}, @{thm mkex_def}] 1 *})

(* main case *)
(* splitting into 4 cases according to a:A, a:B *)
apply auto

(* Case y:A, y:B *)
apply (tactic {* Seq_case_simp_tac @{context} "exA" 1 *})
(* Case exA=UU, Case exA=nil*)
(* These UU and nil cases are the only places where the assumption filter A sch<<f_act exA
   is used! --> to generate a contradiction using  ~a>>ss<< UU(nil), using theorems
   Cons_not_less_UU and Cons_not_less_nil  *)
apply (tactic {* Seq_case_simp_tac @{context} "exB" 1 *})
(* Case exA=a>>x, exB=b>>y *)
(* here it is important that Seq_case_simp_tac uses no !full!_simp_tac for the cons case,
   as otherwise mkex_cons_3 would  not be rewritten without use of rotate_tac: then tactic
   would not be generally applicable *)
apply simp

(* Case y:A, y~:B *)
apply (tactic {* Seq_case_simp_tac @{context} "exA" 1 *})
apply simp

(* Case y~:A, y:B *)
apply (tactic {* Seq_case_simp_tac @{context} "exB" 1 *})
apply simp

(* Case y~:A, y~:B *)
apply (simp add: asig_of_par actions_asig_comp)
done


(* generalizing the proof above to a proof method *)

ML {*

local
  val defs = [@{thm Filter_def}, @{thm Forall_def}, @{thm sforall_def}, @{thm mkex_def},
    @{thm stutter_def}]
  val asigs = [@{thm asig_of_par}, @{thm actions_asig_comp}]
in

fun mkex_induct_tac ctxt sch exA exB =
  let val ss = simpset_of ctxt in
    EVERY'[Seq_induct_tac ctxt sch defs,
           asm_full_simp_tac ss,
           SELECT_GOAL (safe_tac (Proof_Context.init_global @{theory Fun})),
           Seq_case_simp_tac ctxt exA,
           Seq_case_simp_tac ctxt exB,
           asm_full_simp_tac ss,
           Seq_case_simp_tac ctxt exA,
           asm_full_simp_tac ss,
           Seq_case_simp_tac ctxt exB,
           asm_full_simp_tac ss,
           asm_full_simp_tac (ss addsimps asigs)
          ]
  end

end
*}

method_setup mkex_induct = {*
  Scan.lift (Args.name -- Args.name -- Args.name)
    >> (fn ((sch, exA), exB) => fn ctxt => SIMPLE_METHOD' (mkex_induct_tac ctxt sch exA exB))
*}


(*---------------------------------------------------------------------------
               Projection of mkex(sch,exA,exB) onto A stutters on A
                             structural induction
  --------------------------------------------------------------------------- *)

lemma stutterA_mkex: "! exA exB s t.
  Forall (%x. x:act (A||B)) sch &
  Filter (%a. a:act A)$sch << filter_act$exA &
  Filter (%a. a:act B)$sch << filter_act$exB
  --> stutter (asig_of A) (s,ProjA2$(snd (mkex A B sch (s,exA) (t,exB))))"
  by (mkex_induct sch exA exB)

lemma stutter_mkex_on_A: "[|
  Forall (%x. x:act (A||B)) sch ;
  Filter (%a. a:act A)$sch << filter_act$(snd exA) ;
  Filter (%a. a:act B)$sch << filter_act$(snd exB) |]
  ==> stutter (asig_of A) (ProjA (mkex A B sch exA exB))"

apply (cut_tac stutterA_mkex)
apply (simp add: stutter_def ProjA_def mkex_def)
apply (erule allE)+
apply (drule mp)
prefer 2 apply (assumption)
apply simp
done


(*---------------------------------------------------------------------------
               Projection of mkex(sch,exA,exB) onto B stutters on B
                             structural induction
  --------------------------------------------------------------------------- *)

lemma stutterB_mkex: "! exA exB s t.
  Forall (%x. x:act (A||B)) sch &
  Filter (%a. a:act A)$sch << filter_act$exA &
  Filter (%a. a:act B)$sch << filter_act$exB
  --> stutter (asig_of B) (t,ProjB2$(snd (mkex A B sch (s,exA) (t,exB))))"
  by (mkex_induct sch exA exB)


lemma stutter_mkex_on_B: "[|
  Forall (%x. x:act (A||B)) sch ;
  Filter (%a. a:act A)$sch << filter_act$(snd exA) ;
  Filter (%a. a:act B)$sch << filter_act$(snd exB) |]
  ==> stutter (asig_of B) (ProjB (mkex A B sch exA exB))"
apply (cut_tac stutterB_mkex)
apply (simp add: stutter_def ProjB_def mkex_def)
apply (erule allE)+
apply (drule mp)
prefer 2 apply (assumption)
apply simp
done


(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto A is exA
        --  using zip$(proj1$exA)$(proj2$exA) instead of exA    --
        --           because of admissibility problems          --
                             structural induction
  --------------------------------------------------------------------------- *)

lemma filter_mkex_is_exA_tmp: "! exA exB s t.
  Forall (%x. x:act (A||B)) sch &
  Filter (%a. a:act A)$sch << filter_act$exA  &
  Filter (%a. a:act B)$sch << filter_act$exB
  --> Filter_ex2 (asig_of A)$(ProjA2$(snd (mkex A B sch (s,exA) (t,exB)))) =
      Zip$(Filter (%a. a:act A)$sch)$(Map snd$exA)"
  by (mkex_induct sch exB exA)

(*---------------------------------------------------------------------------
                      zip$(proj1$y)$(proj2$y) = y   (using the lift operations)
                    lemma for admissibility problems
  --------------------------------------------------------------------------- *)

lemma Zip_Map_fst_snd: "Zip$(Map fst$y)$(Map snd$y) = y"
apply (tactic {* Seq_induct_tac @{context} "y" [] 1 *})
done


(*---------------------------------------------------------------------------
      filter A$sch = proj1$ex   -->  zip$(filter A$sch)$(proj2$ex) = ex
         lemma for eliminating non admissible equations in assumptions
  --------------------------------------------------------------------------- *)

lemma trick_against_eq_in_ass: "!! sch ex.
  Filter (%a. a:act AB)$sch = filter_act$ex
  ==> ex = Zip$(Filter (%a. a:act AB)$sch)$(Map snd$ex)"
apply (simp add: filter_act_def)
apply (rule Zip_Map_fst_snd [symmetric])
done

(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto A is exA
                       using the above trick
  --------------------------------------------------------------------------- *)


lemma filter_mkex_is_exA: "!!sch exA exB.
  [| Forall (%a. a:act (A||B)) sch ;
  Filter (%a. a:act A)$sch = filter_act$(snd exA)  ;
  Filter (%a. a:act B)$sch = filter_act$(snd exB) |]
  ==> Filter_ex (asig_of A) (ProjA (mkex A B sch exA exB)) = exA"
apply (simp add: ProjA_def Filter_ex_def)
apply (tactic {* pair_tac @{context} "exA" 1 *})
apply (tactic {* pair_tac @{context} "exB" 1 *})
apply (rule conjI)
apply (simp (no_asm) add: mkex_def)
apply (simplesubst trick_against_eq_in_ass)
back
apply assumption
apply (simp add: filter_mkex_is_exA_tmp)
done


(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to B after projection onto B is exB
        --  using zip$(proj1$exB)$(proj2$exB) instead of exB    --
        --           because of admissibility problems          --
                             structural induction
  --------------------------------------------------------------------------- *)

lemma filter_mkex_is_exB_tmp: "! exA exB s t.
  Forall (%x. x:act (A||B)) sch &
  Filter (%a. a:act A)$sch << filter_act$exA  &
  Filter (%a. a:act B)$sch << filter_act$exB
  --> Filter_ex2 (asig_of B)$(ProjB2$(snd (mkex A B sch (s,exA) (t,exB)))) =
      Zip$(Filter (%a. a:act B)$sch)$(Map snd$exB)"

(* notice necessary change of arguments exA and exB *)
  by (mkex_induct sch exA exB)


(*---------------------------------------------------------------------------
     Filter of mkex(sch,exA,exB) to A after projection onto B is exB
                       using the above trick
  --------------------------------------------------------------------------- *)


lemma filter_mkex_is_exB: "!!sch exA exB.
  [| Forall (%a. a:act (A||B)) sch ;
  Filter (%a. a:act A)$sch = filter_act$(snd exA)  ;
  Filter (%a. a:act B)$sch = filter_act$(snd exB) |]
  ==> Filter_ex (asig_of B) (ProjB (mkex A B sch exA exB)) = exB"
apply (simp add: ProjB_def Filter_ex_def)
apply (tactic {* pair_tac @{context} "exA" 1 *})
apply (tactic {* pair_tac @{context} "exB" 1 *})
apply (rule conjI)
apply (simp (no_asm) add: mkex_def)
apply (simplesubst trick_against_eq_in_ass)
back
apply assumption
apply (simp add: filter_mkex_is_exB_tmp)
done

(* --------------------------------------------------------------------- *)
(*                    mkex has only  A- or B-actions                    *)
(* --------------------------------------------------------------------- *)


lemma mkex_actions_in_AorB: "!s t exA exB.
  Forall (%x. x : act (A || B)) sch &
  Filter (%a. a:act A)$sch << filter_act$exA  &
  Filter (%a. a:act B)$sch << filter_act$exB
   --> Forall (%x. fst x : act (A ||B))
         (snd (mkex A B sch (s,exA) (t,exB)))"
  by (mkex_induct sch exA exB)


(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    SCHEDULE      Level             *)
(*                          Main Theorem                              *)
(* ------------------------------------------------------------------ *)

lemma compositionality_sch:
"(sch : schedules (A||B)) =
  (Filter (%a. a:act A)$sch : schedules A &
   Filter (%a. a:act B)$sch : schedules B &
   Forall (%x. x:act (A||B)) sch)"
apply (simp (no_asm) add: schedules_def has_schedule_def)
apply auto
(* ==> *)
apply (rule_tac x = "Filter_ex (asig_of A) (ProjA ex) " in bexI)
prefer 2
apply (simp add: compositionality_ex)
apply (simp (no_asm) add: Filter_ex_def ProjA_def lemma_2_1a lemma_2_1b)
apply (rule_tac x = "Filter_ex (asig_of B) (ProjB ex) " in bexI)
prefer 2
apply (simp add: compositionality_ex)
apply (simp (no_asm) add: Filter_ex_def ProjB_def lemma_2_1a lemma_2_1b)
apply (simp add: executions_def)
apply (tactic {* pair_tac @{context} "ex" 1 *})
apply (erule conjE)
apply (simp add: sch_actions_in_AorB)

(* <== *)

(* mkex is exactly the construction of exA||B out of exA, exB, and the oracle sch,
   we need here *)
apply (rename_tac exA exB)
apply (rule_tac x = "mkex A B sch exA exB" in bexI)
(* mkex actions are just the oracle *)
apply (tactic {* pair_tac @{context} "exA" 1 *})
apply (tactic {* pair_tac @{context} "exB" 1 *})
apply (simp add: Mapfst_mkex_is_sch)

(* mkex is an execution -- use compositionality on ex-level *)
apply (simp add: compositionality_ex)
apply (simp add: stutter_mkex_on_A stutter_mkex_on_B filter_mkex_is_exB filter_mkex_is_exA)
apply (tactic {* pair_tac @{context} "exA" 1 *})
apply (tactic {* pair_tac @{context} "exB" 1 *})
apply (simp add: mkex_actions_in_AorB)
done


subsection {* COMPOSITIONALITY on SCHEDULE Level -- for Modules *}

lemma compositionality_sch_modules:
  "Scheds (A||B) = par_scheds (Scheds A) (Scheds B)"

apply (unfold Scheds_def par_scheds_def)
apply (simp add: asig_of_par)
apply (rule set_eqI)
apply (simp add: compositionality_sch actions_of_par)
done


declare compoex_simps [simp del]
declare composch_simps [simp del]

end
