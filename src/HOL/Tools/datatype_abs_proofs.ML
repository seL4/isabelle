(*  Title:      HOL/Tools/datatype_abs_proofs.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1998  TU Muenchen

Proofs and defintions independent of concrete representation
of datatypes  (i.e. requiring only abstract properties such as
injectivity / distinctness of constructors and induction)

 - case distinction (exhaustion) theorems
 - characteristic equations for primrec combinators
 - characteristic equations for case combinators
 - equations for splitting "P (case ...)" expressions
 - datatype size function
 - "nchotomy" and "case_cong" theorems for TFL

*)

signature DATATYPE_ABS_PROOFS =
sig
  val prove_casedist_thms : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      thm -> theory attribute list -> theory -> theory * thm list
  val prove_primrec_thms : bool -> string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      DatatypeAux.datatype_info Symtab.table -> thm list list -> thm list list ->
        simpset -> thm -> theory -> theory * (string list * thm list)
  val prove_case_thms : bool -> string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      string list -> thm list -> theory -> theory * (thm list list * string list)
  val prove_split_thms : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      thm list list -> thm list list -> thm list -> thm list list -> theory ->
        theory * (thm * thm) list
  val prove_size_thms : bool -> string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      string list -> thm list -> theory -> theory * thm list
  val prove_nchotomys : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      thm list -> theory -> theory * thm list
  val prove_weak_case_congs : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      theory -> theory * thm list
  val prove_case_congs : string list -> (int * (string * DatatypeAux.dtyp list *
    (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
      thm list -> thm list list -> theory -> theory * thm list
end;

structure DatatypeAbsProofs: DATATYPE_ABS_PROOFS =
struct

open DatatypeAux;

val thin = read_instantiate_sg (Theory.sign_of Set.thy) [("V", "?X : ?Y")] thin_rl;

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (prems_of distinct_lemma);

(************************ case distinction theorems ***************************)

fun prove_casedist_thms new_type_names descr sorts induct case_names_exhausts thy =
  let
    val _ = message "Proving case distinction theorems ...";

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);

    val {maxidx, ...} = rep_thm induct;
    val induct_Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct)));

    fun prove_casedist_thm ((i, t), T) =
      let
        val dummyPs = map (fn (Var (_, Type (_, [T', T'']))) =>
          Abs ("z", T', Const ("True", T''))) induct_Ps;
        val P = Abs ("z", T, HOLogic.imp $ HOLogic.mk_eq (Var (("a", maxidx+1), T), Bound 0) $
          Var (("P", 0), HOLogic.boolT))
        val insts = take (i, dummyPs) @ (P::(drop (i + 1, dummyPs)));
        val cert = cterm_of (Theory.sign_of thy);
        val insts' = (map cert induct_Ps) ~~ (map cert insts);
        val induct' = refl RS ((nth_elem (i,
          split_conj_thm (cterm_instantiate insts' induct))) RSN (2, rev_mp))

      in prove_goalw_cterm [] (cert t) (fn prems =>
        [rtac induct' 1,
         REPEAT (rtac TrueI 1),
         REPEAT ((rtac impI 1) THEN (eresolve_tac prems 1)),
         REPEAT (rtac TrueI 1)])
      end;

    val casedist_thms = map prove_casedist_thm ((0 upto (length newTs - 1)) ~~
      (DatatypeProp.make_casedists descr sorts) ~~ newTs)
  in thy |> store_thms_atts "exhaust" new_type_names (map single case_names_exhausts) casedist_thms end;


(*************************** primrec combinators ******************************)

fun prove_primrec_thms flat_names new_type_names descr sorts
    (dt_info : datatype_info Symtab.table) constr_inject dist_rewrites dist_ss induct thy =
  let
    val _ = message "Constructing primrec combinators ...";

    val fun_rel_comp_name = Sign.intern_const (sign_of Relation.thy) "fun_rel_comp";
    val [fun_rel_comp_def, o_def] =
      map (get_thm Relation.thy) ["fun_rel_comp_def", "o_def"];

    val big_name = space_implode "_" new_type_names;
    val thy0 = add_path flat_names big_name thy;

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names (recTs, []);
    val newTs = take (length (hd descr), recTs);

    val induct_Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct)));

    val big_rec_name' = big_name ^ "_rec_set";
    val rec_set_names = map (Sign.full_name (Theory.sign_of thy0))
      (if length descr' = 1 then [big_rec_name'] else
        (map ((curry (op ^) (big_rec_name' ^ "_")) o string_of_int)
          (1 upto (length descr'))));

    val rec_result_Ts = map TFree (variantlist (replicate (length descr') "'t", used) ~~
      replicate (length descr') HOLogic.termS);

    val reccomb_fn_Ts = flat (map (fn (i, (_, _, constrs)) =>
      map (fn (_, cargs) =>
        let
          val Ts = map (typ_of_dtyp descr' sorts) cargs;
          val recs = filter (is_rec_type o fst) (cargs ~~ Ts);

          fun mk_argT (DtRec k, _) = nth_elem (k, rec_result_Ts)
            | mk_argT (DtType ("fun", [_, DtRec k]), Type ("fun", [T, _])) =
               T --> nth_elem (k, rec_result_Ts);

          val argTs = Ts @ map mk_argT recs
        in argTs ---> nth_elem (i, rec_result_Ts)
        end) constrs) descr');

    val rec_set_Ts = map (fn (T1, T2) => reccomb_fn_Ts ---> HOLogic.mk_setT
      (HOLogic.mk_prodT (T1, T2))) (recTs ~~ rec_result_Ts);

    val rec_fns = map (uncurry (mk_Free "f"))
      (reccomb_fn_Ts ~~ (1 upto (length reccomb_fn_Ts)));
    val rec_sets = map (fn c => list_comb (Const c, rec_fns))
      (rec_set_names ~~ rec_set_Ts);

    (* introduction rules for graph of primrec function *)

    fun make_rec_intr T set_name ((rec_intr_ts, l), (cname, cargs)) =
      let
        fun mk_prem ((dt, U), (j, k, prems, t1s, t2s)) =
          let val free1 = mk_Free "x" U j
          in (case (dt, U) of
             (DtRec m, _) =>
               let val free2 = mk_Free "y" (nth_elem (m, rec_result_Ts)) k
               in (j + 1, k + 1, (HOLogic.mk_Trueprop (HOLogic.mk_mem
                 (HOLogic.mk_prod (free1, free2), nth_elem (m, rec_sets))))::prems,
                   free1::t1s, free2::t2s)
               end
           | (DtType ("fun", [_, DtRec m]), U' as Type ("fun", [T', _])) =>
               let val free2 = mk_Free "y" (T' --> nth_elem (m, rec_result_Ts)) k
               in (j + 1, k + 1, (HOLogic.mk_Trueprop (HOLogic.mk_mem (free2,
                 Const (fun_rel_comp_name, [U', snd (strip_type (nth_elem (m, rec_set_Ts)))] --->
                   HOLogic.mk_setT (T' --> nth_elem (m, rec_result_Ts))) $
                     free1 $ nth_elem (m, rec_sets))))::prems, free1::t1s, free2::t2s)
               end
           | _ => (j + 1, k, prems, free1::t1s, t2s))
          end;

        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val (_, _, prems, t1s, t2s) = foldr mk_prem (cargs ~~ Ts, (1, 1, [], [], []))

      in (rec_intr_ts @ [Logic.list_implies (prems, HOLogic.mk_Trueprop (HOLogic.mk_mem
        (HOLogic.mk_prod (list_comb (Const (cname, Ts ---> T), t1s),
          list_comb (nth_elem (l, rec_fns), t1s @ t2s)), set_name)))], l + 1)
      end;

    val (rec_intr_ts, _) = foldl (fn (x, ((d, T), set_name)) =>
      foldl (make_rec_intr T set_name) (x, #3 (snd d)))
        (([], 0), descr' ~~ recTs ~~ rec_sets);

    val (thy1, {intrs = rec_intrs, elims = rec_elims, ...}) =
      setmp InductivePackage.quiet_mode (!quiet_mode)
        (InductivePackage.add_inductive_i false true big_rec_name' false false true
           rec_sets [] (map (fn x => (("", x), [])) rec_intr_ts) [fun_rel_comp_mono] []) thy0;

    (* prove uniqueness and termination of primrec combinators *)

    val _ = message "Proving termination and uniqueness of primrec functions ...";

    fun mk_unique_tac ((tac, intrs), ((((i, (tname, _, constrs)), elim), T), T')) =
      let
        val distinct_tac = (etac Pair_inject 1) THEN
          (if i < length newTs then
             full_simp_tac (HOL_ss addsimps (nth_elem (i, dist_rewrites))) 1
           else full_simp_tac dist_ss 1);

        val inject = map (fn r => r RS iffD1)
          (if i < length newTs then nth_elem (i, constr_inject)
            else #inject (the (Symtab.lookup (dt_info, tname))));

        fun mk_unique_constr_tac n ((tac, intr::intrs, j), (cname, cargs)) =
          let
            val k = length (filter is_rec_type cargs)

          in (EVERY [DETERM tac,
                REPEAT (dtac fun_rel_comp_unique 1),
                REPEAT (etac ex1E 1), rtac ex1I 1,
                DEPTH_SOLVE_1 (ares_tac [intr] 1),
                REPEAT_DETERM_N k (etac thin 1),
                etac elim 1,
                REPEAT_DETERM_N j distinct_tac,
                etac Pair_inject 1, TRY (dresolve_tac inject 1),
                REPEAT (etac conjE 1), hyp_subst_tac 1,
                REPEAT (etac allE 1),
                REPEAT (dtac mp 1 THEN atac 1),
                TRY (hyp_subst_tac 1),
                rtac refl 1,
                REPEAT_DETERM_N (n - j - 1) distinct_tac],
              intrs, j + 1)
          end;

        val (tac', intrs', _) = foldl (mk_unique_constr_tac (length constrs))
          ((tac, intrs, 0), constrs);

      in (tac', intrs') end;

    val rec_unique_thms =
      let
        val rec_unique_ts = map (fn (((set_t, T1), T2), i) =>
          Const ("Ex1", (T2 --> HOLogic.boolT) --> HOLogic.boolT) $
            absfree ("y", T2, HOLogic.mk_mem (HOLogic.mk_prod
              (mk_Free "x" T1 i, Free ("y", T2)), set_t)))
                (rec_sets ~~ recTs ~~ rec_result_Ts ~~ (1 upto length recTs));
        val cert = cterm_of (Theory.sign_of thy1)
        val insts = map (fn ((i, T), t) => absfree ("x" ^ (string_of_int i), T, t))
          ((1 upto length recTs) ~~ recTs ~~ rec_unique_ts);
        val induct' = cterm_instantiate ((map cert induct_Ps) ~~
          (map cert insts)) induct;
        val (tac, _) = foldl mk_unique_tac
          ((rtac induct' 1, rec_intrs), descr' ~~ rec_elims ~~ recTs ~~ rec_result_Ts)

      in split_conj_thm (prove_goalw_cterm []
        (cert (HOLogic.mk_Trueprop (mk_conj rec_unique_ts))) (K [tac]))
      end;

    val rec_total_thms = map (fn r =>
      r RS ex1_implies_ex RS (select_eq_Ex RS iffD2)) rec_unique_thms;

    (* define primrec combinators *)

    val big_reccomb_name = (space_implode "_" new_type_names) ^ "_rec";
    val reccomb_names = map (Sign.full_name (Theory.sign_of thy1))
      (if length descr' = 1 then [big_reccomb_name] else
        (map ((curry (op ^) (big_reccomb_name ^ "_")) o string_of_int)
          (1 upto (length descr'))));
    val reccombs = map (fn ((name, T), T') => list_comb
      (Const (name, reccomb_fn_Ts @ [T] ---> T'), rec_fns))
        (reccomb_names ~~ recTs ~~ rec_result_Ts);

    val (thy2, reccomb_defs) = thy1 |>
      Theory.add_consts_i (map (fn ((name, T), T') =>
        (Sign.base_name name, reccomb_fn_Ts @ [T] ---> T', NoSyn))
          (reccomb_names ~~ recTs ~~ rec_result_Ts)) |>
      (PureThy.add_defs_i false o map Thm.no_attributes) (map (fn ((((name, comb), set), T), T') =>
        ((Sign.base_name name) ^ "_def", Logic.mk_equals (comb, absfree ("x", T,
           Const ("Eps", (T' --> HOLogic.boolT) --> T') $ absfree ("y", T',
             HOLogic.mk_mem (HOLogic.mk_prod (Free ("x", T), Free ("y", T')), set))))))
               (reccomb_names ~~ reccombs ~~ rec_sets ~~ recTs ~~ rec_result_Ts)) |>>
      parent_path flat_names;


    (* prove characteristic equations for primrec combinators *)

    val _ = message "Proving characteristic theorems for primrec combinators ..."

    val rec_thms = map (fn t => prove_goalw_cterm reccomb_defs
      (cterm_of (Theory.sign_of thy2) t) (fn _ =>
        [rtac select1_equality 1,
         resolve_tac rec_unique_thms 1,
         resolve_tac rec_intrs 1,
         rewrite_goals_tac [o_def, fun_rel_comp_def],
         REPEAT ((rtac CollectI 1 THEN rtac allI 1) ORELSE resolve_tac rec_total_thms 1)]))
           (DatatypeProp.make_primrecs new_type_names descr sorts thy2)

  in
    thy2 |> Theory.add_path (space_implode "_" new_type_names) |>
    PureThy.add_thmss [(("recs", rec_thms), [])] |>>
    Theory.parent_path |> apsnd (pair reccomb_names o flat)
  end;


(***************************** case combinators *******************************)

fun prove_case_thms flat_names new_type_names descr sorts reccomb_names primrec_thms thy =
  let
    val _ = message "Proving characteristic theorems for case combinators ...";

    val thy1 = add_path flat_names (space_implode "_" new_type_names) thy;

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val used = foldr add_typ_tfree_names (recTs, []);
    val newTs = take (length (hd descr), recTs);
    val T' = TFree (variant used "'t", HOLogic.termS);

    fun mk_dummyT (DtRec _) = T'
      | mk_dummyT (DtType ("fun", [T, _])) = typ_of_dtyp descr' sorts T --> T'

    val case_dummy_fns = map (fn (_, (_, _, constrs)) => map (fn (_, cargs) =>
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val Ts' = map mk_dummyT (filter is_rec_type cargs)
      in Const ("arbitrary", Ts @ Ts' ---> T')
      end) constrs) descr';

    val case_names = map (fn s =>
      Sign.full_name (Theory.sign_of thy1) (s ^ "_case")) new_type_names;

    (* define case combinators via primrec combinators *)

    val (case_defs, thy2) = foldl (fn ((defs, thy),
      ((((i, (_, _, constrs)), T), name), recname)) =>
        let
          val (fns1, fns2) = ListPair.unzip (map (fn ((_, cargs), j) =>
            let
              val Ts = map (typ_of_dtyp descr' sorts) cargs;
              val Ts' = Ts @ map mk_dummyT (filter is_rec_type cargs);
              val frees' = map (uncurry (mk_Free "x")) (Ts' ~~ (1 upto length Ts'));
              val frees = take (length cargs, frees');
              val free = mk_Free "f" (Ts ---> T') j
            in
             (free, list_abs_free (map dest_Free frees',
               list_comb (free, frees)))
            end) (constrs ~~ (1 upto length constrs)));

          val caseT = (map (snd o dest_Free) fns1) @ [T] ---> T';
          val fns = (flat (take (i, case_dummy_fns))) @
            fns2 @ (flat (drop (i + 1, case_dummy_fns)));
          val reccomb = Const (recname, (map fastype_of fns) @ [T] ---> T');
          val decl = (Sign.base_name name, caseT, NoSyn);
          val def = ((Sign.base_name name) ^ "_def",
            Logic.mk_equals (list_comb (Const (name, caseT), fns1),
              list_comb (reccomb, (flat (take (i, case_dummy_fns))) @
                fns2 @ (flat (drop (i + 1, case_dummy_fns))) )));
          val (thy', [def_thm]) = thy |>
            Theory.add_consts_i [decl] |> (PureThy.add_defs_i false o map Thm.no_attributes) [def];

        in (defs @ [def_thm], thy')
        end) (([], thy1), (hd descr) ~~ newTs ~~ case_names ~~
          (take (length newTs, reccomb_names)));

    val case_thms = map (map (fn t => prove_goalw_cterm (case_defs @
      (map mk_meta_eq primrec_thms)) (cterm_of (Theory.sign_of thy2) t)
        (fn _ => [rtac refl 1])))
          (DatatypeProp.make_cases new_type_names descr sorts thy2)

  in
    thy2 |> Theory.add_trrules_i
      (DatatypeProp.make_case_trrules new_type_names descr) |>
    parent_path flat_names |>
    store_thmss "cases" new_type_names case_thms |>
    apsnd (rpair case_names)
  end;


(******************************* case splitting *******************************)

fun prove_split_thms new_type_names descr sorts constr_inject dist_rewrites
    casedist_thms case_thms thy =
  let
    val _ = message "Proving equations for case splitting ...";

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);

    fun prove_split_thms ((((((t1, t2), inject), dist_rewrites'),
        exhaustion), case_thms'), T) =
      let
        val cert = cterm_of (Theory.sign_of thy);
        val _ $ (_ $ lhs $ _) = hd (Logic.strip_assums_hyp (hd (prems_of exhaustion)));
        val exhaustion' = cterm_instantiate
          [(cert lhs, cert (Free ("x", T)))] exhaustion;
        val tacsf = K [rtac exhaustion' 1, ALLGOALS (asm_simp_tac
          (HOL_ss addsimps (dist_rewrites' @ inject @ case_thms')))]
      in
        (prove_goalw_cterm [] (cert t1) tacsf,
         prove_goalw_cterm [] (cert t2) tacsf)
      end;

    val split_thm_pairs = map prove_split_thms
      ((DatatypeProp.make_splits new_type_names descr sorts thy) ~~ constr_inject ~~
        dist_rewrites ~~ casedist_thms ~~ case_thms ~~ newTs);

    val (split_thms, split_asm_thms) = ListPair.unzip split_thm_pairs

  in
    thy |> store_thms "split" new_type_names split_thms |>>>
      store_thms "split_asm" new_type_names split_asm_thms |> apsnd ListPair.zip
  end;

(******************************* size functions *******************************)

fun prove_size_thms flat_names new_type_names descr sorts reccomb_names primrec_thms thy =
  if exists (fn (_, (_, _, constrs)) => exists (fn (_, cargs) => exists
    (fn (DtType ("fun", [_, DtRec _])) => true | _ => false) cargs) constrs) (flat descr)
  then
    (thy, [])
  else
  let
    val _ = message "Proving equations for size function ...";

    val big_name = space_implode "_" new_type_names;
    val thy1 = add_path flat_names big_name thy;

    val descr' = flat descr;
    val recTs = get_rec_types descr' sorts;

    val size_name = Sign.intern_const (Theory.sign_of (theory "Arith")) "size";
    val size_names = replicate (length (hd descr)) size_name @
      map (Sign.full_name (Theory.sign_of thy1)) (DatatypeProp.indexify_names
        (map (fn T => name_of_typ T ^ "_size") (drop (length (hd descr), recTs))));
    val def_names = map (fn s => s ^ "_def") (DatatypeProp.indexify_names
      (map (fn T => name_of_typ T ^ "_size") recTs));

    fun plus (t1, t2) = Const ("op +", [HOLogic.natT, HOLogic.natT] ---> HOLogic.natT) $ t1 $ t2;

    fun make_sizefun (_, cargs) =
      let
        val Ts = map (typ_of_dtyp descr' sorts) cargs;
        val k = length (filter is_rec_type cargs);
        val t = if k = 0 then HOLogic.zero else
          foldl1 plus (map Bound (k - 1 downto 0) @ [HOLogic.mk_nat 1])
      in
        foldr (fn (T, t') => Abs ("x", T, t')) (Ts @ replicate k HOLogic.natT, t)
      end;

    val fs = flat (map (fn (_, (_, _, constrs)) => map make_sizefun constrs) descr');
    val fTs = map fastype_of fs;

    val (thy', size_def_thms) = thy1 |>
      Theory.add_consts_i (map (fn (s, T) =>
        (Sign.base_name s, T --> HOLogic.natT, NoSyn))
          (drop (length (hd descr), size_names ~~ recTs))) |>
      (PureThy.add_defs_i true o map Thm.no_attributes) (map (fn (((s, T), def_name), rec_name) =>
        (def_name, Logic.mk_equals (Const (s, T --> HOLogic.natT),
          list_comb (Const (rec_name, fTs @ [T] ---> HOLogic.natT), fs))))
            (size_names ~~ recTs ~~ def_names ~~ reccomb_names)) |>>
      parent_path flat_names;

    val rewrites = size_def_thms @ map mk_meta_eq primrec_thms;

    val size_thms = map (fn t => prove_goalw_cterm rewrites
      (cterm_of (Theory.sign_of thy') t) (fn _ => [rtac refl 1]))
        (DatatypeProp.make_size descr sorts thy')

  in
    thy' |> Theory.add_path big_name |>
    PureThy.add_thmss [(("size", size_thms), [])] |>>
    Theory.parent_path |> apsnd flat
  end;

fun prove_weak_case_congs new_type_names descr sorts thy =
  let
    fun prove_weak_case_cong t =
       prove_goalw_cterm [] (cterm_of (Theory.sign_of thy) t)
         (fn prems => [rtac ((hd prems) RS arg_cong) 1])

    val weak_case_congs = map prove_weak_case_cong (DatatypeProp.make_weak_case_congs
      new_type_names descr sorts thy)

  in thy |> store_thms "weak_case_cong" new_type_names weak_case_congs end;

(************************* additional theorems for TFL ************************)

fun prove_nchotomys new_type_names descr sorts casedist_thms thy =
  let
    val _ = message "Proving additional theorems for TFL ...";

    fun prove_nchotomy (t, exhaustion) =
      let
        (* For goal i, select the correct disjunct to attack, then prove it *)
        fun tac i 0 = EVERY [TRY (rtac disjI1 i),
              hyp_subst_tac i, REPEAT (rtac exI i), rtac refl i]
          | tac i n = rtac disjI2 i THEN tac i (n - 1)
      in 
        prove_goalw_cterm [] (cterm_of (Theory.sign_of thy) t) (fn _ =>
          [rtac allI 1,
           exh_tac (K exhaustion) 1,
           ALLGOALS (fn i => tac i (i-1))])
      end;

    val nchotomys =
      map prove_nchotomy (DatatypeProp.make_nchotomys descr sorts ~~ casedist_thms)

  in thy |> store_thms "nchotomy" new_type_names nchotomys end;

fun prove_case_congs new_type_names descr sorts nchotomys case_thms thy =
  let
    fun prove_case_cong ((t, nchotomy), case_rewrites) =
      let
        val (Const ("==>", _) $ tm $ _) = t;
        val (Const ("Trueprop", _) $ (Const ("op =", _) $ _ $ Ma)) = tm;
        val cert = cterm_of (Theory.sign_of thy);
        val nchotomy' = nchotomy RS spec;
        val nchotomy'' = cterm_instantiate
          [(cert (hd (add_term_vars (concl_of nchotomy', []))), cert Ma)] nchotomy'
      in
        prove_goalw_cterm [] (cert t) (fn prems => 
          let val simplify = asm_simp_tac (HOL_ss addsimps (prems @ case_rewrites))
          in [simp_tac (HOL_ss addsimps [hd prems]) 1,
              cut_facts_tac [nchotomy''] 1,
              REPEAT (etac disjE 1 THEN REPEAT (etac exE 1) THEN simplify 1),
              REPEAT (etac exE 1) THEN simplify 1 (* Get last disjunct *)]
          end)
      end;

    val case_congs = map prove_case_cong (DatatypeProp.make_case_congs
      new_type_names descr sorts thy ~~ nchotomys ~~ case_thms)

  in thy |> store_thms "case_cong" new_type_names case_congs end;

end;
