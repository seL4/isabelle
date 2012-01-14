(*  Title:      ZF/Tools/inductive_package.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Fixedpoint definition module -- for Inductive/Coinductive Definitions

The functor will be instantiated for normal sums/products (inductive defs)
                         and non-standard sums/products (coinductive defs)

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

type inductive_result =
   {defs       : thm list,             (*definitions made in thy*)
    bnd_mono   : thm,                  (*monotonicity for the lfp definition*)
    dom_subset : thm,                  (*inclusion of recursive set in dom*)
    intrs      : thm list,             (*introduction rules*)
    elim       : thm,                  (*case analysis theorem*)
    induct     : thm,                  (*main induction rule*)
    mutual_induct : thm};              (*mutual induction rule*)


(*Functor's result signature*)
signature INDUCTIVE_PACKAGE =
sig
  (*Insert definitions for the recursive sets, which
     must *already* be declared as constants in parent theory!*)
  val add_inductive_i: bool -> term list * term ->
    ((binding * term) * attribute list) list ->
    thm list * thm list * thm list * thm list -> theory -> theory * inductive_result
  val add_inductive: string list * string ->
    ((binding * string) * Attrib.src list) list ->
    (Facts.ref * Attrib.src list) list * (Facts.ref * Attrib.src list) list *
    (Facts.ref * Attrib.src list) list * (Facts.ref * Attrib.src list) list ->
    theory -> theory * inductive_result
end;


(*Declares functions to add fixedpoint/constructor defs to a theory.
  Recursive sets must *already* be declared as constants.*)
functor Add_inductive_def_Fun
    (structure Fp: FP and Pr : PR and CP: CARTPROD and Su : SU val coind: bool)
 : INDUCTIVE_PACKAGE =
struct

val co_prefix = if coind then "co" else "";


(* utils *)

(*make distinct individual variables a1, a2, a3, ..., an. *)
fun mk_frees a [] = []
  | mk_frees a (T::Ts) = Free(a,T) :: mk_frees (Symbol.bump_string a) Ts;


(* add_inductive(_i) *)

(*internal version, accepting terms*)
fun add_inductive_i verbose (rec_tms, dom_sum)
  raw_intr_specs (monos, con_defs, type_intrs, type_elims) thy =
let
  val _ = Theory.requires thy "Inductive_ZF" "(co)inductive definitions";
  val ctxt = Proof_Context.init_global thy;

  val intr_specs = map (apfst (apfst Binding.name_of)) raw_intr_specs;
  val (intr_names, intr_tms) = split_list (map fst intr_specs);
  val case_names = Rule_Cases.case_names intr_names;

  (*recT and rec_params should agree for all mutually recursive components*)
  val rec_hds = map head_of rec_tms;

  val dummy = assert_all is_Const rec_hds
          (fn t => "Recursive set not previously declared as constant: " ^
                   Syntax.string_of_term ctxt t);

  (*Now we know they are all Consts, so get their names, type and params*)
  val rec_names = map (#1 o dest_Const) rec_hds
  and (Const(_,recT),rec_params) = strip_comb (hd rec_tms);

  val rec_base_names = map Long_Name.base_name rec_names;
  val dummy = assert_all Lexicon.is_identifier rec_base_names
    (fn a => "Base name of recursive set not an identifier: " ^ a);

  local (*Checking the introduction rules*)
    val intr_sets = map (#2 o Ind_Syntax.rule_concl_msg thy) intr_tms;
    fun intr_ok set =
        case head_of set of Const(a,recT) => member (op =) rec_names a | _ => false;
  in
    val dummy =  assert_all intr_ok intr_sets
       (fn t => "Conclusion of rule does not name a recursive set: " ^
                Syntax.string_of_term ctxt t);
  end;

  val dummy = assert_all is_Free rec_params
      (fn t => "Param in recursion term not a free variable: " ^
               Syntax.string_of_term ctxt t);

  (*** Construct the fixedpoint definition ***)
  val mk_variant = singleton (Name.variant_list (List.foldr Misc_Legacy.add_term_names [] intr_tms));

  val z' = mk_variant"z" and X' = mk_variant"X" and w' = mk_variant"w";

  fun dest_tprop (Const(@{const_name Trueprop},_) $ P) = P
    | dest_tprop Q = error ("Ill-formed premise of introduction rule: " ^
                            Syntax.string_of_term ctxt Q);

  (*Makes a disjunct from an introduction rule*)
  fun fp_part intr = (*quantify over rule's free vars except parameters*)
    let val prems = map dest_tprop (Logic.strip_imp_prems intr)
        val dummy = List.app (fn rec_hd => List.app (Ind_Syntax.chk_prem rec_hd) prems) rec_hds
        val exfrees = subtract (op =) rec_params (Misc_Legacy.term_frees intr)
        val zeq = FOLogic.mk_eq (Free(z', Ind_Syntax.iT), #1 (Ind_Syntax.rule_concl intr))
    in List.foldr FOLogic.mk_exists
             (Balanced_Tree.make FOLogic.mk_conj (zeq::prems)) exfrees
    end;

  (*The Part(A,h) terms -- compose injections to make h*)
  fun mk_Part (Bound 0) = Free(X', Ind_Syntax.iT) (*no mutual rec, no Part needed*)
    | mk_Part h = @{const Part} $ Free(X', Ind_Syntax.iT) $ Abs (w', Ind_Syntax.iT, h);

  (*Access to balanced disjoint sums via injections*)
  val parts = map mk_Part
    (Balanced_Tree.accesses {left = fn t => Su.inl $ t, right = fn t => Su.inr $ t, init = Bound 0}
      (length rec_tms));

  (*replace each set by the corresponding Part(A,h)*)
  val part_intrs = map (subst_free (rec_tms ~~ parts) o fp_part) intr_tms;

  val fp_abs =
    absfree (X', Ind_Syntax.iT)
        (Ind_Syntax.mk_Collect (z', dom_sum,
            Balanced_Tree.make FOLogic.mk_disj part_intrs));

  val fp_rhs = Fp.oper $ dom_sum $ fp_abs

  val dummy = List.app (fn rec_hd => (Logic.occs (rec_hd, fp_rhs) andalso
                             error "Illegal occurrence of recursion operator"; ()))
           rec_hds;

  (*** Make the new theory ***)

  (*A key definition:
    If no mutual recursion then it equals the one recursive set.
    If mutual recursion then it differs from all the recursive sets. *)
  val big_rec_base_name = space_implode "_" rec_base_names;
  val big_rec_name = Proof_Context.intern_const ctxt big_rec_base_name;


  val _ =
    if verbose then
      writeln ((if coind then "Coind" else "Ind") ^ "uctive definition " ^ quote big_rec_name)
    else ();

  (*Big_rec... is the union of the mutually recursive sets*)
  val big_rec_tm = list_comb(Const(big_rec_name,recT), rec_params);

  (*The individual sets must already be declared*)
  val axpairs = map Misc_Legacy.mk_defpair
        ((big_rec_tm, fp_rhs) ::
         (case parts of
             [_] => []                        (*no mutual recursion*)
           | _ => rec_tms ~~          (*define the sets as Parts*)
                  map (subst_atomic [(Free (X', Ind_Syntax.iT), big_rec_tm)]) parts));

  (*tracing: print the fixedpoint definition*)
  val dummy = if !Ind_Syntax.trace then
              writeln (cat_lines (map (Syntax.string_of_term ctxt o #2) axpairs))
          else ()

  (*add definitions of the inductive sets*)
  val (_, thy1) =
    thy
    |> Sign.add_path big_rec_base_name
    |> Global_Theory.add_defs false (map (Thm.no_attributes o apfst Binding.name) axpairs);

  val ctxt1 = Proof_Context.init_global thy1;


  (*fetch fp definitions from the theory*)
  val big_rec_def::part_rec_defs =
    map (Misc_Legacy.get_def thy1)
        (case rec_names of [_] => rec_names
                         | _   => big_rec_base_name::rec_names);


  (********)
  val dummy = writeln "  Proving monotonicity...";

  val bnd_mono =
    Goal.prove_global thy1 [] [] (FOLogic.mk_Trueprop (Fp.bnd_mono $ dom_sum $ fp_abs))
      (fn _ => EVERY
        [rtac (@{thm Collect_subset} RS @{thm bnd_monoI}) 1,
         REPEAT (ares_tac (@{thms basic_monos} @ monos) 1)]);

  val dom_subset = Drule.export_without_context (big_rec_def RS Fp.subs);

  val unfold = Drule.export_without_context ([big_rec_def, bnd_mono] MRS Fp.Tarski);

  (********)
  val dummy = writeln "  Proving the introduction rules...";

  (*Mutual recursion?  Helps to derive subset rules for the
    individual sets.*)
  val Part_trans =
      case rec_names of
           [_] => asm_rl
         | _   => Drule.export_without_context (@{thm Part_subset} RS @{thm subset_trans});

  (*To type-check recursive occurrences of the inductive sets, possibly
    enclosed in some monotonic operator M.*)
  val rec_typechecks =
     [dom_subset] RL (asm_rl :: ([Part_trans] RL monos))
     RL [@{thm subsetD}];

  (*Type-checking is hardest aspect of proof;
    disjIn selects the correct disjunct after unfolding*)
  fun intro_tacsf disjIn =
    [DETERM (stac unfold 1),
     REPEAT (resolve_tac [@{thm Part_eqI}, @{thm CollectI}] 1),
     (*Now 2-3 subgoals: typechecking, the disjunction, perhaps equality.*)
     rtac disjIn 2,
     (*Not ares_tac, since refl must be tried before equality assumptions;
       backtracking may occur if the premises have extra variables!*)
     DEPTH_SOLVE_1 (resolve_tac [@{thm refl}, @{thm exI}, @{thm conjI}] 2 APPEND assume_tac 2),
     (*Now solve the equations like Tcons(a,f) = Inl(?b4)*)
     rewrite_goals_tac con_defs,
     REPEAT (rtac @{thm refl} 2),
     (*Typechecking; this can fail*)
     if !Ind_Syntax.trace then print_tac "The type-checking subgoal:"
     else all_tac,
     REPEAT (FIRSTGOAL (        dresolve_tac rec_typechecks
                        ORELSE' eresolve_tac (asm_rl :: @{thm PartE} :: @{thm SigmaE2} ::
                                              type_elims)
                        ORELSE' hyp_subst_tac)),
     if !Ind_Syntax.trace then print_tac "The subgoal after monos, type_elims:"
     else all_tac,
     DEPTH_SOLVE (swap_res_tac (@{thm SigmaI} :: @{thm subsetI} :: type_intrs) 1)];

  (*combines disjI1 and disjI2 to get the corresponding nested disjunct...*)
  val mk_disj_rls = Balanced_Tree.accesses
    {left = fn rl => rl RS @{thm disjI1},
     right = fn rl => rl RS @{thm disjI2},
     init = @{thm asm_rl}};

  val intrs =
    (intr_tms, map intro_tacsf (mk_disj_rls (length intr_tms)))
    |> ListPair.map (fn (t, tacs) =>
      Goal.prove_global thy1 [] [] t
        (fn _ => EVERY (rewrite_goals_tac part_rec_defs :: tacs)));

  (********)
  val dummy = writeln "  Proving the elimination rule...";

  (*Breaks down logical connectives in the monotonic function*)
  val basic_elim_tac =
      REPEAT (SOMEGOAL (eresolve_tac (Ind_Syntax.elim_rls @ Su.free_SEs)
                ORELSE' bound_hyp_subst_tac))
      THEN prune_params_tac
          (*Mutual recursion: collapse references to Part(D,h)*)
      THEN (PRIMITIVE (fold_rule part_rec_defs));

  (*Elimination*)
  val elim = rule_by_tactic (Proof_Context.init_global thy1) basic_elim_tac
                 (unfold RS Ind_Syntax.equals_CollectD)

  (*Applies freeness of the given constructors, which *must* be unfolded by
      the given defs.  Cannot simply use the local con_defs because
      con_defs=[] for inference systems.
    Proposition A should have the form t:Si where Si is an inductive set*)
  fun make_cases ctxt A =
    rule_by_tactic ctxt
      (basic_elim_tac THEN ALLGOALS (asm_full_simp_tac (simpset_of ctxt)) THEN basic_elim_tac)
      (Thm.assume A RS elim)
      |> Drule.export_without_context_open;

  fun induction_rules raw_induct thy =
   let
     val dummy = writeln "  Proving the induction rule...";

     (*** Prove the main induction rule ***)

     val pred_name = "P";            (*name for predicate variables*)

     (*Used to make induction rules;
        ind_alist = [(rec_tm1,pred1),...] associates predicates with rec ops
        prem is a premise of an intr rule*)
     fun add_induct_prem ind_alist (prem as Const (@{const_name Trueprop}, _) $
                      (Const (@{const_name mem}, _) $ t $ X), iprems) =
          (case AList.lookup (op aconv) ind_alist X of
               SOME pred => prem :: FOLogic.mk_Trueprop (pred $ t) :: iprems
             | NONE => (*possibly membership in M(rec_tm), for M monotone*)
                 let fun mk_sb (rec_tm,pred) =
                             (rec_tm, @{const Collect} $ rec_tm $ pred)
                 in  subst_free (map mk_sb ind_alist) prem :: iprems  end)
       | add_induct_prem ind_alist (prem,iprems) = prem :: iprems;

     (*Make a premise of the induction rule.*)
     fun induct_prem ind_alist intr =
       let val xs = subtract (op =) rec_params (Misc_Legacy.term_frees intr)
           val iprems = List.foldr (add_induct_prem ind_alist) []
                              (Logic.strip_imp_prems intr)
           val (t,X) = Ind_Syntax.rule_concl intr
           val (SOME pred) = AList.lookup (op aconv) ind_alist X
           val concl = FOLogic.mk_Trueprop (pred $ t)
       in fold_rev Logic.all xs (Logic.list_implies (iprems,concl)) end
       handle Bind => error"Recursion term not found in conclusion";

     (*Minimizes backtracking by delivering the correct premise to each goal.
       Intro rules with extra Vars in premises still cause some backtracking *)
     fun ind_tac [] 0 = all_tac
       | ind_tac(prem::prems) i =
             DEPTH_SOLVE_1 (ares_tac [prem, @{thm refl}] i) THEN ind_tac prems (i-1);

     val pred = Free(pred_name, Ind_Syntax.iT --> FOLogic.oT);

     val ind_prems = map (induct_prem (map (rpair pred) rec_tms))
                         intr_tms;

     val dummy =
      if ! Ind_Syntax.trace then
        writeln (cat_lines
          (["ind_prems:"] @ map (Syntax.string_of_term ctxt1) ind_prems @
           ["raw_induct:", Display.string_of_thm ctxt1 raw_induct]))
      else ();


     (*We use a MINIMAL simpset. Even FOL_ss contains too many simpules.
       If the premises get simplified, then the proofs could fail.*)
     val min_ss =
           (Simplifier.global_context thy empty_ss
             |> Simplifier.set_mksimps (K (map mk_eq o ZF_atomize o gen_all)))
           setSolver (mk_solver "minimal"
                      (fn ss => resolve_tac (triv_rls @ Simplifier.prems_of ss)
                                   ORELSE' assume_tac
                                   ORELSE' etac @{thm FalseE}));

     val quant_induct =
       Goal.prove_global thy1 [] ind_prems
         (FOLogic.mk_Trueprop (Ind_Syntax.mk_all_imp (big_rec_tm, pred)))
         (fn {prems, ...} => EVERY
           [rewrite_goals_tac part_rec_defs,
            rtac (@{thm impI} RS @{thm allI}) 1,
            DETERM (etac raw_induct 1),
            (*Push Part inside Collect*)
            full_simp_tac (min_ss addsimps [@{thm Part_Collect}]) 1,
            (*This CollectE and disjE separates out the introduction rules*)
            REPEAT (FIRSTGOAL (eresolve_tac [@{thm CollectE}, @{thm disjE}])),
            (*Now break down the individual cases.  No disjE here in case
              some premise involves disjunction.*)
            REPEAT (FIRSTGOAL (eresolve_tac [@{thm CollectE}, @{thm exE}, @{thm conjE}]
                               ORELSE' bound_hyp_subst_tac)),
            ind_tac (rev (map (rewrite_rule part_rec_defs) prems)) (length prems)]);

     val dummy =
      if ! Ind_Syntax.trace then
        writeln ("quant_induct:\n" ^ Display.string_of_thm ctxt1 quant_induct)
      else ();


     (*** Prove the simultaneous induction rule ***)

     (*Make distinct predicates for each inductive set*)

     (*The components of the element type, several if it is a product*)
     val elem_type = CP.pseudo_type dom_sum;
     val elem_factors = CP.factors elem_type;
     val elem_frees = mk_frees "za" elem_factors;
     val elem_tuple = CP.mk_tuple Pr.pair elem_type elem_frees;

     (*Given a recursive set and its domain, return the "fsplit" predicate
       and a conclusion for the simultaneous induction rule.
       NOTE.  This will not work for mutually recursive predicates.  Previously
       a summand 'domt' was also an argument, but this required the domain of
       mutual recursion to invariably be a disjoint sum.*)
     fun mk_predpair rec_tm =
       let val rec_name = (#1 o dest_Const o head_of) rec_tm
           val pfree = Free(pred_name ^ "_" ^ Long_Name.base_name rec_name,
                            elem_factors ---> FOLogic.oT)
           val qconcl =
             List.foldr FOLogic.mk_all
               (FOLogic.imp $
                (@{const mem} $ elem_tuple $ rec_tm)
                      $ (list_comb (pfree, elem_frees))) elem_frees
       in  (CP.ap_split elem_type FOLogic.oT pfree,
            qconcl)
       end;

     val (preds,qconcls) = split_list (map mk_predpair rec_tms);

     (*Used to form simultaneous induction lemma*)
     fun mk_rec_imp (rec_tm,pred) =
         FOLogic.imp $ (@{const mem} $ Bound 0 $ rec_tm) $
                          (pred $ Bound 0);

     (*To instantiate the main induction rule*)
     val induct_concl =
         FOLogic.mk_Trueprop
           (Ind_Syntax.mk_all_imp
            (big_rec_tm,
             Abs("z", Ind_Syntax.iT,
                 Balanced_Tree.make FOLogic.mk_conj
                 (ListPair.map mk_rec_imp (rec_tms, preds)))))
     and mutual_induct_concl =
      FOLogic.mk_Trueprop (Balanced_Tree.make FOLogic.mk_conj qconcls);

     val dummy = if !Ind_Syntax.trace then
                 (writeln ("induct_concl = " ^
                           Syntax.string_of_term ctxt1 induct_concl);
                  writeln ("mutual_induct_concl = " ^
                           Syntax.string_of_term ctxt1 mutual_induct_concl))
             else ();


     val lemma_tac = FIRST' [eresolve_tac [@{thm asm_rl}, @{thm conjE}, @{thm PartE}, @{thm mp}],
                             resolve_tac [@{thm allI}, @{thm impI}, @{thm conjI}, @{thm Part_eqI}],
                             dresolve_tac [@{thm spec}, @{thm mp}, Pr.fsplitD]];

     val need_mutual = length rec_names > 1;

     val lemma = (*makes the link between the two induction rules*)
       if need_mutual then
          (writeln "  Proving the mutual induction rule...";
           Goal.prove_global thy1 [] []
             (Logic.mk_implies (induct_concl, mutual_induct_concl))
             (fn _ => EVERY
               [rewrite_goals_tac part_rec_defs,
                REPEAT (rewrite_goals_tac [Pr.split_eq] THEN lemma_tac 1)]))
       else (writeln "  [ No mutual induction rule needed ]"; @{thm TrueI});

     val dummy =
      if ! Ind_Syntax.trace then
        writeln ("lemma: " ^ Display.string_of_thm ctxt1 lemma)
      else ();


     (*Mutual induction follows by freeness of Inl/Inr.*)

     (*Simplification largely reduces the mutual induction rule to the
       standard rule*)
     val mut_ss =
         min_ss addsimps [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff];

     val all_defs = con_defs @ part_rec_defs;

     (*Removes Collects caused by M-operators in the intro rules.  It is very
       hard to simplify
         list({v: tf. (v : t --> P_t(v)) & (v : f --> P_f(v))})
       where t==Part(tf,Inl) and f==Part(tf,Inr) to  list({v: tf. P_t(v)}).
       Instead the following rules extract the relevant conjunct.
     *)
     val cmonos = [@{thm subset_refl} RS @{thm Collect_mono}] RL monos
                   RLN (2,[@{thm rev_subsetD}]);

     (*Minimizes backtracking by delivering the correct premise to each goal*)
     fun mutual_ind_tac [] 0 = all_tac
       | mutual_ind_tac(prem::prems) i =
           DETERM
            (SELECT_GOAL
               (
                (*Simplify the assumptions and goal by unfolding Part and
                  using freeness of the Sum constructors; proves all but one
                  conjunct by contradiction*)
                rewrite_goals_tac all_defs  THEN
                simp_tac (mut_ss addsimps [@{thm Part_iff}]) 1  THEN
                IF_UNSOLVED (*simp_tac may have finished it off!*)
                  ((*simplify assumptions*)
                   (*some risk of excessive simplification here -- might have
                     to identify the bare minimum set of rewrites*)
                   full_simp_tac
                      (mut_ss addsimps @{thms conj_simps} @ @{thms imp_simps} @ @{thms quant_simps}) 1
                   THEN
                   (*unpackage and use "prem" in the corresponding place*)
                   REPEAT (rtac @{thm impI} 1)  THEN
                   rtac (rewrite_rule all_defs prem) 1  THEN
                   (*prem must not be REPEATed below: could loop!*)
                   DEPTH_SOLVE (FIRSTGOAL (ares_tac [@{thm impI}] ORELSE'
                                           eresolve_tac (@{thm conjE} :: @{thm mp} :: cmonos))))
               ) i)
            THEN mutual_ind_tac prems (i-1);

     val mutual_induct_fsplit =
       if need_mutual then
         Goal.prove_global thy1 [] (map (induct_prem (rec_tms~~preds)) intr_tms)
           mutual_induct_concl
           (fn {prems, ...} => EVERY
             [rtac (quant_induct RS lemma) 1,
              mutual_ind_tac (rev prems) (length prems)])
       else @{thm TrueI};

     (** Uncurrying the predicate in the ordinary induction rule **)

     (*instantiate the variable to a tuple, if it is non-trivial, in order to
       allow the predicate to be "opened up".
       The name "x.1" comes from the "RS spec" !*)
     val inst =
         case elem_frees of [_] => I
            | _ => Drule.instantiate_normalize ([], [(cterm_of thy1 (Var(("x",1), Ind_Syntax.iT)),
                                      cterm_of thy1 elem_tuple)]);

     (*strip quantifier and the implication*)
     val induct0 = inst (quant_induct RS @{thm spec} RSN (2, @{thm rev_mp}));

     val Const (@{const_name Trueprop}, _) $ (pred_var $ _) = concl_of induct0

     val induct = CP.split_rule_var(pred_var, elem_type-->FOLogic.oT, induct0)
                  |> Drule.export_without_context
     and mutual_induct = CP.remove_split mutual_induct_fsplit

     val ([induct', mutual_induct'], thy') =
       thy
       |> Global_Theory.add_thms [((Binding.name (co_prefix ^ "induct"), induct),
             [case_names, Induct.induct_pred big_rec_name]),
           ((Binding.name "mutual_induct", mutual_induct), [case_names])];
    in ((thy', induct'), mutual_induct')
    end;  (*of induction_rules*)

  val raw_induct = Drule.export_without_context ([big_rec_def, bnd_mono] MRS Fp.induct)

  val ((thy2, induct), mutual_induct) =
    if not coind then induction_rules raw_induct thy1
    else
      (thy1
      |> Global_Theory.add_thms [((Binding.name (co_prefix ^ "induct"), raw_induct), [])]
      |> apfst hd |> Library.swap, @{thm TrueI})
  and defs = big_rec_def :: part_rec_defs


  val (([bnd_mono', dom_subset', elim'], [defs', intrs']), thy3) =
    thy2
    |> IndCases.declare big_rec_name make_cases
    |> Global_Theory.add_thms
      [((Binding.name "bnd_mono", bnd_mono), []),
       ((Binding.name "dom_subset", dom_subset), []),
       ((Binding.name "cases", elim), [case_names, Induct.cases_pred big_rec_name])]
    ||>> (Global_Theory.add_thmss o map Thm.no_attributes)
        [(Binding.name "defs", defs),
         (Binding.name "intros", intrs)];
  val (intrs'', thy4) =
    thy3
    |> Global_Theory.add_thms ((map Binding.name intr_names ~~ intrs') ~~ map #2 intr_specs)
    ||> Sign.parent_path;
  in
    (thy4,
      {defs = defs',
       bnd_mono = bnd_mono',
       dom_subset = dom_subset',
       intrs = intrs'',
       elim = elim',
       induct = induct,
       mutual_induct = mutual_induct})
  end;

(*source version*)
fun add_inductive (srec_tms, sdom_sum) intr_srcs
    (raw_monos, raw_con_defs, raw_type_intrs, raw_type_elims) thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val read_terms = map (Syntax.parse_term ctxt #> Type.constraint Ind_Syntax.iT)
      #> Syntax.check_terms ctxt;

    val intr_atts = map (map (Attrib.attribute thy) o snd) intr_srcs;
    val sintrs = map fst intr_srcs ~~ intr_atts;
    val rec_tms = read_terms srec_tms;
    val dom_sum = singleton read_terms sdom_sum;
    val intr_tms = Syntax.read_props ctxt (map (snd o fst) sintrs);
    val intr_specs = (map (fst o fst) sintrs ~~ intr_tms) ~~ map snd sintrs;
    val monos = Attrib.eval_thms ctxt raw_monos;
    val con_defs = Attrib.eval_thms ctxt raw_con_defs;
    val type_intrs = Attrib.eval_thms ctxt raw_type_intrs;
    val type_elims = Attrib.eval_thms ctxt raw_type_elims;
  in
    thy
    |> add_inductive_i true (rec_tms, dom_sum) intr_specs (monos, con_defs, type_intrs, type_elims)
  end;


(* outer syntax *)

val _ = List.app Keyword.keyword
  ["domains", "intros", "monos", "con_defs", "type_intros", "type_elims"];

fun mk_ind (((((doms, intrs), monos), con_defs), type_intrs), type_elims) =
  #1 o add_inductive doms (map Parse.triple_swap intrs) (monos, con_defs, type_intrs, type_elims);

val ind_decl =
  (Parse.$$$ "domains" |-- Parse.!!! (Parse.enum1 "+" Parse.term --
      ((Parse.$$$ "\<subseteq>" || Parse.$$$ "<=") |-- Parse.term))) --
  (Parse.$$$ "intros" |--
    Parse.!!! (Scan.repeat1 (Parse_Spec.opt_thm_name ":" -- Parse.prop))) --
  Scan.optional (Parse.$$$ "monos" |-- Parse.!!! Parse_Spec.xthms1) [] --
  Scan.optional (Parse.$$$ "con_defs" |-- Parse.!!! Parse_Spec.xthms1) [] --
  Scan.optional (Parse.$$$ "type_intros" |-- Parse.!!! Parse_Spec.xthms1) [] --
  Scan.optional (Parse.$$$ "type_elims" |-- Parse.!!! Parse_Spec.xthms1) []
  >> (Toplevel.theory o mk_ind);

val _ =
  Outer_Syntax.command (co_prefix ^ "inductive")
    ("define " ^ co_prefix ^ "inductive sets") Keyword.thy_decl ind_decl;

end;

