(*  Title:      HOL/Tools/datatype_realizer.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Porgram extraction from proofs involving datatypes:
Realizers for induction and case analysis
*)

signature DATATYPE_REALIZER =
sig
  val add_dt_realizers: (string * sort) list ->
    DatatypeAux.datatype_info list -> theory -> theory
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
  in Abst (a, Some T, Proofterm.prf_abstract_over t prf) end;

fun prf_of thm =
  let val {sign, prop, der = (_, prf), ...} = rep_thm thm
  in Reconstruct.reconstruct_proof sign prop prf end;

fun prf_subst_vars inst =
  Proofterm.map_proof_terms (subst_vars ([], inst)) I;

fun is_unit t = snd (strip_type (fastype_of t)) = HOLogic.unitT;

fun tname_of (Type (s, _)) = s
  | tname_of _ = "";

fun mk_realizes T = Const ("realizes", T --> HOLogic.boolT --> HOLogic.boolT);

fun make_ind sorts ({descr, rec_names, rec_rewrites, induction, ...} : datatype_info) (is, thy) =
  let
    val sg = sign_of thy;
    val recTs = get_rec_types descr sorts;
    val pnames = if length descr = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr);

    val rec_result_Ts = map (fn ((i, _), P) =>
      if i mem is then TFree ("'" ^ P, HOLogic.typeS) else HOLogic.unitT)
        (descr ~~ pnames);

    fun make_pred i T U r x =
      if i mem is then
        Free (nth_elem (i, pnames), T --> U --> HOLogic.boolT) $ r $ x
      else Free (nth_elem (i, pnames), U --> HOLogic.boolT) $ x;

    fun mk_all i s T t =
      if i mem is then list_all_free ([(s, T)], t) else t;

    val (prems, rec_fns) = split_list (flat (snd (foldl_map
      (fn (j, ((i, (_, _, constrs)), T)) => foldl_map (fn (j, (cname, cargs)) =>
        let
          val Ts = map (typ_of_dtyp descr sorts) cargs;
          val tnames = variantlist (DatatypeProp.make_tnames Ts, pnames);
          val recs = filter (is_rec_type o fst o fst) (cargs ~~ tnames ~~ Ts);
          val frees = tnames ~~ Ts;

          fun mk_prems vs [] = 
                let
                  val rT = nth_elem (i, rec_result_Ts);
                  val vs' = filter_out is_unit vs;
                  val f = mk_Free "f" (map fastype_of vs' ---> rT) j;
                  val f' = Pattern.eta_contract (list_abs_free
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
                  val rT = nth_elem (k, rec_result_Ts);
                  val r = Free ("r" ^ s, Us ---> rT);
                  val (p, f) = mk_prems (vs @ [r]) ds
                in (mk_all k ("r" ^ s) (Us ---> rT) (Logic.mk_implies
                  (list_all (map (pair "x") Us, HOLogic.mk_Trueprop
                    (make_pred k rT U (app_bnds r i)
                      (app_bnds (Free (s, T)) i))), p)), f)
                end

        in (j + 1,
          apfst (curry list_all_free frees) (mk_prems (map Free frees) recs))
        end) (j, constrs)) (1, descr ~~ recTs))));
 
    fun mk_proj j [] t = t
      | mk_proj j (i :: is) t = if null is then t else
          if j = i then HOLogic.mk_fst t
          else mk_proj j is (HOLogic.mk_snd t);

    val tnames = DatatypeProp.make_tnames recTs;
    val fTs = map fastype_of rec_fns;
    val ps = map (fn ((((i, _), T), U), s) => Abs ("x", T, make_pred i U T
      (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Bound 0) (Bound 0)))
        (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names);
    val r = if null is then Extraction.nullt else
      foldr1 HOLogic.mk_prod (mapfilter (fn (((((i, _), T), U), s), tname) =>
        if i mem is then Some
          (list_comb (Const (s, fTs ---> T --> U), rec_fns) $ Free (tname, T))
        else None) (descr ~~ recTs ~~ rec_result_Ts ~~ rec_names ~~ tnames));
    val concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop "op &")
      (map (fn ((((i, _), T), U), tname) =>
        make_pred i U T (mk_proj i is r) (Free (tname, T)))
          (descr ~~ recTs ~~ rec_result_Ts ~~ tnames)));
    val cert = cterm_of sg;
    val inst = map (pairself cert) (map head_of (HOLogic.dest_conj
      (HOLogic.dest_Trueprop (concl_of induction))) ~~ ps);

    val thm = simple_prove_goal_cterm (cert (Logic.list_implies (prems, concl)))
      (fn prems =>
         [rewrite_goals_tac (map mk_meta_eq [fst_conv, snd_conv]),
          rtac (cterm_instantiate inst induction) 1,
          ALLGOALS ObjectLogic.atomize_tac,
          rewrite_goals_tac (o_def :: map mk_meta_eq rec_rewrites),
          REPEAT ((resolve_tac prems THEN_ALL_NEW (fn i =>
            REPEAT (etac allE i) THEN atac i)) 1)]);

    val {path, ...} = Sign.rep_sg sg;
    val ind_name = Thm.name_of_thm induction;
    val vs = map (fn i => nth_elem (i, pnames)) is;
    val (thy', thm') = thy
      |> Theory.absolute_path
      |> PureThy.store_thm
        ((space_implode "_" (ind_name :: vs @ ["correctness"]), thm), [])
      |>> Theory.add_path (NameSpace.pack (if_none path []));

    val ivs = Drule.vars_of_terms
      [Logic.varify (DatatypeProp.make_ind [descr] sorts)];
    val rvs = Drule.vars_of_terms [prop_of thm'];
    val ivs1 = map Var (filter_out (fn (_, T) =>
      tname_of (body_type T) mem ["set", "bool"]) ivs);
    val ivs2 = map (fn (ixn, _) => Var (ixn, the (assoc (rvs, ixn)))) ivs;

    val prf = foldr forall_intr_prf (ivs2,
      foldr (fn ((f, p), prf) =>
        (case head_of (strip_abs_body f) of
           Free (s, T) =>
             let val T' = Type.varifyT T
             in Abst (s, Some T', Proofterm.prf_abstract_over
               (Var ((s, 0), T')) (AbsP ("H", Some p, prf)))
             end
         | _ => AbsP ("H", Some p, prf)))
           (rec_fns ~~ prems_of thm, Proofterm.proof_combP
             (prf_of thm', map PBound (length prems - 1 downto 0))));

    val r' = if null is then r else Logic.varify (foldr (uncurry lambda)
      (map Logic.unvarify ivs1 @ filter_out is_unit
        (map (head_of o strip_abs_body) rec_fns), r));

  in Extraction.add_realizers_i [(ind_name, (vs, r', prf))] thy' end;


fun make_casedists sorts ({index, descr, case_name, case_rewrites, exhaustion, ...} : datatype_info, thy) =
  let
    val sg = sign_of thy;
    val sorts = map (rpair HOLogic.typeS) (distinct (flat (map
      (fn (_, (_, ds, _)) => mapfilter (try dest_DtTFree) ds) descr)));
    val cert = cterm_of sg;
    val rT = TFree ("'P", HOLogic.typeS);
    val rT' = TVar (("'P", 0), HOLogic.typeS);

    fun make_casedist_prem T (cname, cargs) =
      let
        val Ts = map (typ_of_dtyp descr sorts) cargs;
        val frees = variantlist
          (DatatypeProp.make_tnames Ts, ["P", "y"]) ~~ Ts;
        val free_ts = map Free frees;
        val r = Free ("r" ^ NameSpace.base cname, Ts ---> rT)
      in (r, list_all_free (frees, Logic.mk_implies (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (Free ("y", T), list_comb (Const (cname, Ts ---> T), free_ts))),
          HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $
            list_comb (r, free_ts)))))
      end;

    val Some (_, _, constrs) = assoc (descr, index);
    val T = nth_elem (index, get_rec_types descr sorts);
    val (rs, prems) = split_list (map (make_casedist_prem T) constrs);
    val r = Const (case_name, map fastype_of rs ---> T --> rT);

    val y = Var (("y", 0), Type.varifyT T);
    val y' = Free ("y", T);

    val thm = prove_goalw_cterm [] (cert (Logic.list_implies (prems,
      HOLogic.mk_Trueprop (Free ("P", rT --> HOLogic.boolT) $
        list_comb (r, rs @ [y'])))))
      (fn prems =>
         [rtac (cterm_instantiate [(cert y, cert y')] exhaustion) 1,
          ALLGOALS (EVERY'
            [asm_simp_tac (HOL_basic_ss addsimps case_rewrites),
             resolve_tac prems, asm_simp_tac HOL_basic_ss])]);

    val {path, ...} = Sign.rep_sg sg;
    val exh_name = Thm.name_of_thm exhaustion;
    val (thy', thm') = thy
      |> Theory.absolute_path
      |> PureThy.store_thm ((exh_name ^ "_P_correctness", thm), [])
      |>> Theory.add_path (NameSpace.pack (if_none path []));

    val P = Var (("P", 0), rT' --> HOLogic.boolT);
    val prf = forall_intr_prf (y, forall_intr_prf (P,
      foldr (fn ((p, r), prf) =>
        forall_intr_prf (Logic.varify r, AbsP ("H", Some (Logic.varify p),
          prf))) (prems ~~ rs, Proofterm.proof_combP (prf_of thm',
            map PBound (length prems - 1 downto 0)))));
    val r' = Logic.varify (Abs ("y", Type.varifyT T,
      list_abs (map dest_Free rs, list_comb (r,
        map Bound ((length rs - 1 downto 0) @ [length rs])))));

  in Extraction.add_realizers_i
    [(exh_name, (["P"], r', prf)),
     (exh_name, ([], Extraction.nullt, prf_of exhaustion))] thy'
  end;


fun add_dt_realizers sorts infos thy = if !proofs < 2 then thy else
  (message "Adding realizers for induction and case analysis ..."; thy
   |> curry (foldr (make_ind sorts (hd infos)))
     (subsets 0 (length (#descr (hd infos)) - 1))
   |> curry (foldr (make_casedists sorts)) infos);

end;
