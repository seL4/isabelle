(*  Title:      HOL/Tools/Datatype/datatype_realizer.ML
    Author:     Stefan Berghofer, TU Muenchen

Program extraction from proofs involving datatypes:
realizers for induction and case analysis.
*)

signature DATATYPE_REALIZER =
sig
  val add_dt_realizers: Datatype.config -> string list -> theory -> theory
  val setup: theory -> theory
end;

structure Datatype_Realizer : DATATYPE_REALIZER =
struct

fun subsets i j =
  if i <= j then
    let val is = subsets (i+1) j
    in map (fn ks => i::ks) is @ is end
  else [[]];

fun is_unit t = body_type (fastype_of t) = HOLogic.unitT;

fun tname_of (Type (s, _)) = s
  | tname_of _ = "";

fun make_ind ({descr, rec_names, rec_rewrites, induct, ...} : Datatype.info) is thy =
  let
    val recTs = Datatype_Aux.get_rec_types descr;
    val pnames =
      if length descr = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr);

    val rec_result_Ts = map (fn ((i, _), P) =>
        if member (op =) is i then TFree ("'" ^ P, HOLogic.typeS) else HOLogic.unitT)
      (descr ~~ pnames);

    fun make_pred i T U r x =
      if member (op =) is i then
        Free (nth pnames i, T --> U --> HOLogic.boolT) $ r $ x
      else Free (nth pnames i, U --> HOLogic.boolT) $ x;

    fun mk_all i s T t =
      if member (op =) is i then list_all_free ([(s, T)], t) else t;

    val (prems, rec_fns) = split_list (flat (fst (fold_map
      (fn ((i, (_, _, constrs)), T) => fold_map (fn (cname, cargs) => fn j =>
        let
          val Ts = map (Datatype_Aux.typ_of_dtyp descr) cargs;
          val tnames = Name.variant_list pnames (Datatype_Prop.make_tnames Ts);
          val recs = filter (Datatype_Aux.is_rec_type o fst o fst) (cargs ~~ tnames ~~ Ts);
          val frees = tnames ~~ Ts;

          fun mk_prems vs [] =
                let
                  val rT = nth (rec_result_Ts) i;
                  val vs' = filter_out is_unit vs;
                  val f = Datatype_Aux.mk_Free "f" (map fastype_of vs' ---> rT) j;
                  val f' =
                    Envir.eta_contract (fold_rev (absfree o dest_Free) vs
                      (if member (op =) is i then list_comb (f, vs') else HOLogic.unit));
                in
                  (HOLogic.mk_Trueprop (make_pred i rT T (list_comb (f, vs'))
                    (list_comb (Const (cname, Ts ---> T), map Free frees))), f')
                end
            | mk_prems vs (((dt, s), T) :: ds) =
                let
                  val k = Datatype_Aux.body_index dt;
                  val (Us, U) = strip_type T;
                  val i = length Us;
                  val rT = nth (rec_result_Ts) k;
                  val r = Free ("r" ^ s, Us ---> rT);
                  val (p, f) = mk_prems (vs @ [r]) ds;
                in
                  (mk_all k ("r" ^ s) (Us ---> rT) (Logic.mk_implies
                    (list_all (map (pair "x") Us, HOLogic.mk_Trueprop
                      (make_pred k rT U (Datatype_Aux.app_bnds r i)
                        (Datatype_Aux.app_bnds (Free (s, T)) i))), p)), f)
                end;
        in (apfst (curry list_all_free frees) (mk_prems (map Free frees) recs), j + 1) end)
          constrs) (descr ~~ recTs) 1)));

    fun mk_proj j [] t = t
      | mk_proj j (i :: is) t =
          if null is then t
          else if (j: int) = i then HOLogic.mk_fst t
          else mk_proj j is (HOLogic.mk_snd t);

    val tnames = Datatype_Prop.make_tnames recTs;
    val fTs = map fastype_of rec_fns;
    val ps = map (fn ((((i, _), T), U), s) => Abs ("x", T, make_pred i U T
      (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Bound 0) (Bound 0)))
        (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names);
    val r =
      if null is then Extraction.nullt
      else
        foldr1 HOLogic.mk_prod (map_filter (fn (((((i, _), T), U), s), tname) =>
          if member (op =) is i then SOME
            (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Free (tname, T))
          else NONE) (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names ~~ tnames));
    val concl =
      HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop @{const_name HOL.conj})
        (map (fn ((((i, _), T), U), tname) =>
          make_pred i U T (mk_proj i is r) (Free (tname, T)))
            (descr ~~ recTs ~~ rec_result_Ts ~~ tnames)));
    val cert = cterm_of thy;
    val inst = map (pairself cert) (map head_of (HOLogic.dest_conj
      (HOLogic.dest_Trueprop (concl_of induct))) ~~ ps);

    val thm =
      Goal.prove_internal (map cert prems) (cert concl)
        (fn prems =>
           EVERY [
            rewrite_goals_tac (map mk_meta_eq [@{thm fst_conv}, @{thm snd_conv}]),
            rtac (cterm_instantiate inst induct) 1,
            ALLGOALS Object_Logic.atomize_prems_tac,
            rewrite_goals_tac (@{thm o_def} :: map mk_meta_eq rec_rewrites),
            REPEAT ((resolve_tac prems THEN_ALL_NEW (fn i =>
              REPEAT (etac allE i) THEN atac i)) 1)])
      |> Drule.export_without_context;

    val ind_name = Thm.derivation_name induct;
    val vs = map (nth pnames) is;
    val (thm', thy') = thy
      |> Sign.root_path
      |> Global_Theory.store_thm
        (Binding.qualified_name (space_implode "_" (ind_name :: vs @ ["correctness"])), thm)
      ||> Sign.restore_naming thy;

    val ivs = rev (Term.add_vars (Logic.varify_global (Datatype_Prop.make_ind [descr])) []);
    val rvs = rev (Thm.fold_terms Term.add_vars thm' []);
    val ivs1 = map Var (filter_out (fn (_, T) => @{type_name bool} = tname_of (body_type T)) ivs);
    val ivs2 = map (fn (ixn, _) => Var (ixn, the (AList.lookup (op =) rvs ixn))) ivs;

    val prf =
      Extraction.abs_corr_shyps thy' induct vs ivs2
        (fold_rev (fn (f, p) => fn prf =>
            (case head_of (strip_abs_body f) of
              Free (s, T) =>
                let val T' = Logic.varifyT_global T in
                  Abst (s, SOME T', Proofterm.prf_abstract_over
                    (Var ((s, 0), T')) (AbsP ("H", SOME p, prf)))
                end
            | _ => AbsP ("H", SOME p, prf)))
          (rec_fns ~~ prems_of thm)
          (Proofterm.proof_combP
            (Reconstruct.proof_of thm', map PBound (length prems - 1 downto 0))));

    val r' =
      if null is then r
      else
        Logic.varify_global (fold_rev lambda
          (map Logic.unvarify_global ivs1 @ filter_out is_unit
              (map (head_of o strip_abs_body) rec_fns)) r);

  in Extraction.add_realizers_i [(ind_name, (vs, r', prf))] thy' end;


fun make_casedists ({index, descr, case_name, case_rewrites, exhaust, ...} : Datatype.info) thy =
  let
    val cert = cterm_of thy;
    val rT = TFree ("'P", HOLogic.typeS);
    val rT' = TVar (("'P", 0), HOLogic.typeS);

    fun make_casedist_prem T (cname, cargs) =
      let
        val Ts = map (Datatype_Aux.typ_of_dtyp descr) cargs;
        val frees = Name.variant_list ["P", "y"] (Datatype_Prop.make_tnames Ts) ~~ Ts;
        val free_ts = map Free frees;
        val r = Free ("r" ^ Long_Name.base_name cname, Ts ---> rT)
      in
        (r, list_all_free (frees, Logic.mk_implies (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (Free ("y", T), list_comb (Const (cname, Ts ---> T), free_ts))),
            HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $
              list_comb (r, free_ts)))))
      end;

    val SOME (_, _, constrs) = AList.lookup (op =) descr index;
    val T = nth (Datatype_Aux.get_rec_types descr) index;
    val (rs, prems) = split_list (map (make_casedist_prem T) constrs);
    val r = Const (case_name, map fastype_of rs ---> T --> rT);

    val y = Var (("y", 0), Logic.varifyT_global T);
    val y' = Free ("y", T);

    val thm =
      Goal.prove_internal (map cert prems)
        (cert (HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $ list_comb (r, rs @ [y']))))
        (fn prems =>
           EVERY [
            rtac (cterm_instantiate [(cert y, cert y')] exhaust) 1,
            ALLGOALS (EVERY'
              [asm_simp_tac (HOL_basic_ss addsimps case_rewrites),
               resolve_tac prems, asm_simp_tac HOL_basic_ss])])
      |> Drule.export_without_context;

    val exh_name = Thm.derivation_name exhaust;
    val (thm', thy') = thy
      |> Sign.root_path
      |> Global_Theory.store_thm (Binding.qualified_name (exh_name ^ "_P_correctness"), thm)
      ||> Sign.restore_naming thy;

    val P = Var (("P", 0), rT' --> HOLogic.boolT);
    val prf =
      Extraction.abs_corr_shyps thy' exhaust ["P"] [y, P]
        (fold_rev (fn (p, r) => fn prf =>
            Proofterm.forall_intr_proof' (Logic.varify_global r)
              (AbsP ("H", SOME (Logic.varify_global p), prf)))
          (prems ~~ rs)
          (Proofterm.proof_combP
            (Reconstruct.proof_of thm', map PBound (length prems - 1 downto 0))));
    val prf' =
      Extraction.abs_corr_shyps thy' exhaust []
        (map Var (Term.add_vars (prop_of exhaust) [])) (Reconstruct.proof_of exhaust);
    val r' =
      Logic.varify_global (Abs ("y", T,
        list_abs (map dest_Free rs, list_comb (r,
          map Bound ((length rs - 1 downto 0) @ [length rs])))));
  in
    Extraction.add_realizers_i
      [(exh_name, (["P"], r', prf)),
       (exh_name, ([], Extraction.nullt, prf'))] thy'
  end;

fun add_dt_realizers config names thy =
  if not (Proofterm.proofs_enabled ()) then thy
  else
    let
      val _ = Datatype_Aux.message config "Adding realizers for induction and case analysis ...";
      val infos = map (Datatype.the_info thy) names;
      val info :: _ = infos;
    in
      thy
      |> fold_rev (make_ind info) (subsets 0 (length (#descr info) - 1))
      |> fold_rev make_casedists infos
    end;

val setup = Datatype.interpretation add_dt_realizers;

end;
