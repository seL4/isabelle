(*  Title:      HOL/Tools/datatype_realizer.ML
    Author:     Stefan Berghofer, TU Muenchen

Porgram extraction from proofs involving datatypes:
Realizers for induction and case analysis
*)

signature DATATYPE_REALIZER =
sig
  val add_dt_realizers: Datatype.config -> string list -> theory -> theory
  val setup: theory -> theory
end;

structure DatatypeRealizer : DATATYPE_REALIZER =
struct

open DatatypeAux;

fun subsets i j = if i <= j then
       let val is = subsets (i+1) j
       in map (fn ks => i::ks) is @ is end
     else [[]];

fun forall_intr_prf (t, prf) =
  let val (a, T) = (case t of Var ((a, _), T) => (a, T) | Free p => p)
  in Abst (a, SOME T, Proofterm.prf_abstract_over t prf) end;

fun prf_of thm =
  Reconstruct.reconstruct_proof (Thm.theory_of_thm thm) (Thm.prop_of thm) (Thm.proof_of thm);

fun prf_subst_vars inst =
  Proofterm.map_proof_terms (subst_vars ([], inst)) I;

fun is_unit t = snd (strip_type (fastype_of t)) = HOLogic.unitT;

fun tname_of (Type (s, _)) = s
  | tname_of _ = "";

fun mk_realizes T = Const ("realizes", T --> HOLogic.boolT --> HOLogic.boolT);

fun make_ind sorts ({descr, rec_names, rec_rewrites, induct, ...} : info) is thy =
  let
    val recTs = get_rec_types descr sorts;
    val pnames = if length descr = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr);

    val rec_result_Ts = map (fn ((i, _), P) =>
      if i mem is then TFree ("'" ^ P, HOLogic.typeS) else HOLogic.unitT)
        (descr ~~ pnames);

    fun make_pred i T U r x =
      if i mem is then
        Free (List.nth (pnames, i), T --> U --> HOLogic.boolT) $ r $ x
      else Free (List.nth (pnames, i), U --> HOLogic.boolT) $ x;

    fun mk_all i s T t =
      if i mem is then list_all_free ([(s, T)], t) else t;

    val (prems, rec_fns) = split_list (flat (fst (fold_map
      (fn ((i, (_, _, constrs)), T) => fold_map (fn (cname, cargs) => fn j =>
        let
          val Ts = map (typ_of_dtyp descr sorts) cargs;
          val tnames = Name.variant_list pnames (DatatypeProp.make_tnames Ts);
          val recs = filter (is_rec_type o fst o fst) (cargs ~~ tnames ~~ Ts);
          val frees = tnames ~~ Ts;

          fun mk_prems vs [] = 
                let
                  val rT = nth (rec_result_Ts) i;
                  val vs' = filter_out is_unit vs;
                  val f = mk_Free "f" (map fastype_of vs' ---> rT) j;
                  val f' = Envir.eta_contract (list_abs_free
                    (map dest_Free vs, if i mem is then list_comb (f, vs')
                      else HOLogic.unit));
                in (HOLogic.mk_Trueprop (make_pred i rT T (list_comb (f, vs'))
                  (list_comb (Const (cname, Ts ---> T), map Free frees))), f')
                end
            | mk_prems vs (((dt, s), T) :: ds) = 
                let
                  val k = body_index dt;
                  val (Us, U) = strip_type T;
                  val i = length Us;
                  val rT = nth (rec_result_Ts) k;
                  val r = Free ("r" ^ s, Us ---> rT);
                  val (p, f) = mk_prems (vs @ [r]) ds
                in (mk_all k ("r" ^ s) (Us ---> rT) (Logic.mk_implies
                  (list_all (map (pair "x") Us, HOLogic.mk_Trueprop
                    (make_pred k rT U (app_bnds r i)
                      (app_bnds (Free (s, T)) i))), p)), f)
                end

        in (apfst (curry list_all_free frees) (mk_prems (map Free frees) recs), j + 1) end)
          constrs) (descr ~~ recTs) 1)));
 
    fun mk_proj j [] t = t
      | mk_proj j (i :: is) t = if null is then t else
          if (j: int) = i then HOLogic.mk_fst t
          else mk_proj j is (HOLogic.mk_snd t);

    val tnames = DatatypeProp.make_tnames recTs;
    val fTs = map fastype_of rec_fns;
    val ps = map (fn ((((i, _), T), U), s) => Abs ("x", T, make_pred i U T
      (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Bound 0) (Bound 0)))
        (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names);
    val r = if null is then Extraction.nullt else
      foldr1 HOLogic.mk_prod (map_filter (fn (((((i, _), T), U), s), tname) =>
        if i mem is then SOME
          (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Free (tname, T))
        else NONE) (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names ~~ tnames));
    val concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn ((((i, _), T), U), tname) =>
        make_pred i U T (mk_proj i is r) (Free (tname, T)))
          (descr ~~ recTs ~~ rec_result_Ts ~~ tnames)));
    val cert = cterm_of thy;
    val inst = map (pairself cert) (map head_of (HOLogic.dest_conj
      (HOLogic.dest_Trueprop (concl_of induct))) ~~ ps);

    val thm = OldGoals.simple_prove_goal_cterm (cert (Logic.list_implies (prems, concl)))
      (fn prems =>
         [rewrite_goals_tac (map mk_meta_eq [fst_conv, snd_conv]),
          rtac (cterm_instantiate inst induct) 1,
          ALLGOALS ObjectLogic.atomize_prems_tac,
          rewrite_goals_tac (@{thm o_def} :: map mk_meta_eq rec_rewrites),
          REPEAT ((resolve_tac prems THEN_ALL_NEW (fn i =>
            REPEAT (etac allE i) THEN atac i)) 1)]);

    val ind_name = Thm.get_name induct;
    val vs = map (fn i => List.nth (pnames, i)) is;
    val (thm', thy') = thy
      |> Sign.root_path
      |> PureThy.store_thm
        (Binding.qualified_name (space_implode "_" (ind_name :: vs @ ["correctness"])), thm)
      ||> Sign.restore_naming thy;

    val ivs = rev (Term.add_vars (Logic.varify (DatatypeProp.make_ind [descr] sorts)) []);
    val rvs = rev (Thm.fold_terms Term.add_vars thm' []);
    val ivs1 = map Var (filter_out (fn (_, T) =>
      tname_of (body_type T) mem ["set", "bool"]) ivs);
    val ivs2 = map (fn (ixn, _) => Var (ixn, valOf (AList.lookup (op =) rvs ixn))) ivs;

    val prf = List.foldr forall_intr_prf
     (List.foldr (fn ((f, p), prf) =>
        (case head_of (strip_abs_body f) of
           Free (s, T) =>
             let val T' = Logic.varifyT T
             in Abst (s, SOME T', Proofterm.prf_abstract_over
               (Var ((s, 0), T')) (AbsP ("H", SOME p, prf)))
             end
         | _ => AbsP ("H", SOME p, prf)))
           (Proofterm.proof_combP
             (prf_of thm', map PBound (length prems - 1 downto 0))) (rec_fns ~~ prems_of thm)) ivs2;

    val r' = if null is then r else Logic.varify (List.foldr (uncurry lambda)
      r (map Logic.unvarify ivs1 @ filter_out is_unit
          (map (head_of o strip_abs_body) rec_fns)));

  in Extraction.add_realizers_i [(ind_name, (vs, r', prf))] thy' end;


fun make_casedists sorts ({index, descr, case_name, case_rewrites, exhaust, ...} : info) thy =
  let
    val cert = cterm_of thy;
    val rT = TFree ("'P", HOLogic.typeS);
    val rT' = TVar (("'P", 0), HOLogic.typeS);

    fun make_casedist_prem T (cname, cargs) =
      let
        val Ts = map (typ_of_dtyp descr sorts) cargs;
        val frees = Name.variant_list ["P", "y"] (DatatypeProp.make_tnames Ts) ~~ Ts;
        val free_ts = map Free frees;
        val r = Free ("r" ^ Long_Name.base_name cname, Ts ---> rT)
      in (r, list_all_free (frees, Logic.mk_implies (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (Free ("y", T), list_comb (Const (cname, Ts ---> T), free_ts))),
          HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $
            list_comb (r, free_ts)))))
      end;

    val SOME (_, _, constrs) = AList.lookup (op =) descr index;
    val T = List.nth (get_rec_types descr sorts, index);
    val (rs, prems) = split_list (map (make_casedist_prem T) constrs);
    val r = Const (case_name, map fastype_of rs ---> T --> rT);

    val y = Var (("y", 0), Logic.varifyT T);
    val y' = Free ("y", T);

    val thm = OldGoals.prove_goalw_cterm [] (cert (Logic.list_implies (prems,
      HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $
        list_comb (r, rs @ [y'])))))
      (fn prems =>
         [rtac (cterm_instantiate [(cert y, cert y')] exhaust) 1,
          ALLGOALS (EVERY'
            [asm_simp_tac (HOL_basic_ss addsimps case_rewrites),
             resolve_tac prems, asm_simp_tac HOL_basic_ss])]);

    val exh_name = Thm.get_name exhaust;
    val (thm', thy') = thy
      |> Sign.root_path
      |> PureThy.store_thm (Binding.qualified_name (exh_name ^ "_P_correctness"), thm)
      ||> Sign.restore_naming thy;

    val P = Var (("P", 0), rT' --> HOLogic.boolT);
    val prf = forall_intr_prf (y, forall_intr_prf (P,
      List.foldr (fn ((p, r), prf) =>
        forall_intr_prf (Logic.varify r, AbsP ("H", SOME (Logic.varify p),
          prf))) (Proofterm.proof_combP (prf_of thm',
            map PBound (length prems - 1 downto 0))) (prems ~~ rs)));
    val r' = Logic.varify (Abs ("y", T,
      list_abs (map dest_Free rs, list_comb (r,
        map Bound ((length rs - 1 downto 0) @ [length rs])))));

  in Extraction.add_realizers_i
    [(exh_name, (["P"], r', prf)),
     (exh_name, ([], Extraction.nullt, prf_of exhaust))] thy'
  end;

fun add_dt_realizers config names thy =
  if ! Proofterm.proofs < 2 then thy
  else let
    val _ = message config "Adding realizers for induction and case analysis ..."
    val infos = map (Datatype.the_info thy) names;
    val info :: _ = infos;
  in
    thy
    |> fold_rev (make_ind (#sorts info) info) (subsets 0 (length (#descr info) - 1))
    |> fold_rev (make_casedists (#sorts info)) infos
  end;

val setup = Datatype.interpretation add_dt_realizers;

end;
