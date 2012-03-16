(*  Title:      HOL/Tools/Datatype/rep_datatype.ML
    Author:     Stefan Berghofer, TU Muenchen

Representation of existing types as datatypes: proofs and definitions
independent of concrete representation of datatypes (i.e. requiring
only abstract properties: injectivity / distinctness of constructors
and induction).
*)

signature REP_DATATYPE =
sig
  val derive_datatype_props : Datatype_Aux.config -> string list -> Datatype_Aux.descr list ->
    thm -> thm list list -> thm list list -> theory -> string list * theory
  val rep_datatype : Datatype_Aux.config -> (string list -> Proof.context -> Proof.context) ->
    term list -> theory -> Proof.state
  val rep_datatype_cmd : Datatype_Aux.config -> (string list -> Proof.context -> Proof.context) ->
    string list -> theory -> Proof.state
end;

structure Rep_Datatype: REP_DATATYPE =
struct

(** derived definitions and proofs **)

(* case distinction theorems *)

fun prove_casedist_thms (config : Datatype_Aux.config)
    new_type_names descr induct case_names_exhausts thy =
  let
    val _ = Datatype_Aux.message config "Proving case distinction theorems ...";

    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val newTs = take (length (hd descr)) recTs;

    val maxidx = Thm.maxidx_of induct;
    val induct_Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct)));

    fun prove_casedist_thm (i, (T, t)) =
      let
        val dummyPs = map (fn (Var (_, Type (_, [T', T'']))) =>
          Abs ("z", T', Const (@{const_name True}, T''))) induct_Ps;
        val P =
          Abs ("z", T, HOLogic.imp $ HOLogic.mk_eq (Var (("a", maxidx + 1), T), Bound 0) $
            Var (("P", 0), HOLogic.boolT));
        val insts = take i dummyPs @ (P :: drop (i + 1) dummyPs);
        val cert = cterm_of thy;
        val insts' = map cert induct_Ps ~~ map cert insts;
        val induct' =
          refl RS
            (nth (Datatype_Aux.split_conj_thm (cterm_instantiate insts' induct)) i RSN (2, rev_mp));
      in
        Skip_Proof.prove_global thy []
          (Logic.strip_imp_prems t)
          (Logic.strip_imp_concl t)
          (fn {prems, ...} =>
            EVERY
              [rtac induct' 1,
               REPEAT (rtac TrueI 1),
               REPEAT ((rtac impI 1) THEN (eresolve_tac prems 1)),
               REPEAT (rtac TrueI 1)])
      end;

    val casedist_thms =
      map_index prove_casedist_thm (newTs ~~ Datatype_Prop.make_casedists descr);
  in
    thy
    |> Datatype_Aux.store_thms_atts "exhaust" new_type_names
        (map single case_names_exhausts) casedist_thms
  end;


(* primrec combinators *)

fun prove_primrec_thms (config : Datatype_Aux.config) new_type_names descr
    injects_of constr_inject (dist_rewrites, other_dist_rewrites) induct thy =
  let
    val _ = Datatype_Aux.message config "Constructing primrec combinators ...";

    val big_name = space_implode "_" new_type_names;
    val thy0 = Sign.add_path big_name thy;

    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val used = fold Term.add_tfree_namesT recTs [];
    val newTs = take (length (hd descr)) recTs;

    val induct_Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of induct)));

    val big_rec_name' = big_name ^ "_rec_set";
    val rec_set_names' =
      if length descr' = 1 then [big_rec_name']
      else map (prefix (big_rec_name' ^ "_") o string_of_int) (1 upto length descr');
    val rec_set_names = map (Sign.full_bname thy0) rec_set_names';

    val (rec_result_Ts, reccomb_fn_Ts) = Datatype_Prop.make_primrec_Ts descr used;

    val rec_set_Ts =
      map (fn (T1, T2) => (reccomb_fn_Ts @ [T1, T2]) ---> HOLogic.boolT) (recTs ~~ rec_result_Ts);

    val rec_fns =
      map (uncurry (Datatype_Aux.mk_Free "f")) (reccomb_fn_Ts ~~ (1 upto length reccomb_fn_Ts));
    val rec_sets' =
      map (fn c => list_comb (Free c, rec_fns)) (rec_set_names' ~~ rec_set_Ts);
    val rec_sets =
      map (fn c => list_comb (Const c, rec_fns)) (rec_set_names ~~ rec_set_Ts);

    (* introduction rules for graph of primrec function *)

    fun make_rec_intr T rec_set (cname, cargs) (rec_intr_ts, l) =
      let
        fun mk_prem (dt, U) (j, k, prems, t1s, t2s) =
          let val free1 = Datatype_Aux.mk_Free "x" U j in
            (case (Datatype_Aux.strip_dtyp dt, strip_type U) of
              ((_, Datatype_Aux.DtRec m), (Us, _)) =>
                let
                  val free2 = Datatype_Aux.mk_Free "y" (Us ---> nth rec_result_Ts m) k;
                  val i = length Us;
                in
                  (j + 1, k + 1,
                    HOLogic.mk_Trueprop (HOLogic.list_all
                      (map (pair "x") Us, nth rec_sets' m $
                        Datatype_Aux.app_bnds free1 i $ Datatype_Aux.app_bnds free2 i)) :: prems,
                    free1 :: t1s, free2 :: t2s)
                end
            | _ => (j + 1, k, prems, free1 :: t1s, t2s))
          end;

        val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
        val (_, _, prems, t1s, t2s) = fold_rev mk_prem (cargs ~~ Ts) (1, 1, [], [], []);

      in
        (rec_intr_ts @
          [Logic.list_implies (prems, HOLogic.mk_Trueprop
            (rec_set $ list_comb (Const (cname, Ts ---> T), t1s) $
              list_comb (nth rec_fns l, t1s @ t2s)))], l + 1)
      end;

    val (rec_intr_ts, _) =
      fold (fn ((d, T), set_name) =>
        fold (make_rec_intr T set_name) (#3 (snd d))) (descr' ~~ recTs ~~ rec_sets') ([], 0);

    val ({intrs = rec_intrs, elims = rec_elims, ...}, thy1) =
      thy0
      |> Sign.map_naming Name_Space.conceal
      |> Inductive.add_inductive_global
          {quiet_mode = #quiet config, verbose = false, alt_name = Binding.name big_rec_name',
            coind = false, no_elim = false, no_ind = true, skip_mono = true, fork_mono = false}
          (map (fn (s, T) => ((Binding.name s, T), NoSyn)) (rec_set_names' ~~ rec_set_Ts))
          (map dest_Free rec_fns)
          (map (fn x => (Attrib.empty_binding, x)) rec_intr_ts) []
      ||> Sign.restore_naming thy0
      ||> Theory.checkpoint;

    (* prove uniqueness and termination of primrec combinators *)

    val _ = Datatype_Aux.message config "Proving termination and uniqueness of primrec functions ...";

    fun mk_unique_tac ((((i, (tname, _, constrs)), elim), T), T') (tac, intrs) =
      let
        val distinct_tac =
          if i < length newTs then
            full_simp_tac (HOL_ss addsimps (nth dist_rewrites i)) 1
          else full_simp_tac (HOL_ss addsimps (flat other_dist_rewrites)) 1;

        val inject =
          map (fn r => r RS iffD1)
            (if i < length newTs then nth constr_inject i else injects_of tname);

        fun mk_unique_constr_tac n (cname, cargs) (tac, intr :: intrs, j) =
          let
            val k = length (filter Datatype_Aux.is_rec_type cargs);
          in
            (EVERY
              [DETERM tac,
                REPEAT (etac ex1E 1), rtac ex1I 1,
                DEPTH_SOLVE_1 (ares_tac [intr] 1),
                REPEAT_DETERM_N k (etac thin_rl 1 THEN rotate_tac 1 1),
                etac elim 1,
                REPEAT_DETERM_N j distinct_tac,
                TRY (dresolve_tac inject 1),
                REPEAT (etac conjE 1), hyp_subst_tac 1,
                REPEAT (EVERY [etac allE 1, dtac mp 1, atac 1]),
                TRY (hyp_subst_tac 1),
                rtac refl 1,
                REPEAT_DETERM_N (n - j - 1) distinct_tac],
              intrs, j + 1)
          end;

        val (tac', intrs', _) =
          fold (mk_unique_constr_tac (length constrs)) constrs (tac, intrs, 0);
      in (tac', intrs') end;

    val rec_unique_thms =
      let
        val rec_unique_ts =
          map (fn (((set_t, T1), T2), i) =>
            Const (@{const_name Ex1}, (T2 --> HOLogic.boolT) --> HOLogic.boolT) $
              absfree ("y", T2) (set_t $ Datatype_Aux.mk_Free "x" T1 i $ Free ("y", T2)))
                (rec_sets ~~ recTs ~~ rec_result_Ts ~~ (1 upto length recTs));
        val cert = cterm_of thy1;
        val insts =
          map (fn ((i, T), t) => absfree ("x" ^ string_of_int i, T) t)
            ((1 upto length recTs) ~~ recTs ~~ rec_unique_ts);
        val induct' = cterm_instantiate (map cert induct_Ps ~~ map cert insts) induct;
        val (tac, _) =
          fold mk_unique_tac (descr' ~~ rec_elims ~~ recTs ~~ rec_result_Ts)
            (((rtac induct' THEN_ALL_NEW Object_Logic.atomize_prems_tac) 1 THEN
                rewrite_goals_tac [mk_meta_eq @{thm choice_eq}], rec_intrs));
      in
        Datatype_Aux.split_conj_thm (Skip_Proof.prove_global thy1 [] []
          (HOLogic.mk_Trueprop (Datatype_Aux.mk_conj rec_unique_ts)) (K tac))
      end;

    val rec_total_thms = map (fn r => r RS @{thm theI'}) rec_unique_thms;

    (* define primrec combinators *)

    val big_reccomb_name = space_implode "_" new_type_names ^ "_rec";
    val reccomb_names =
      map (Sign.full_bname thy1)
        (if length descr' = 1 then [big_reccomb_name]
         else map (prefix (big_reccomb_name ^ "_") o string_of_int) (1 upto length descr'));
    val reccombs =
      map (fn ((name, T), T') => Const (name, reccomb_fn_Ts @ [T] ---> T'))
        (reccomb_names ~~ recTs ~~ rec_result_Ts);

    val (reccomb_defs, thy2) =
      thy1
      |> Sign.add_consts_i (map (fn ((name, T), T') =>
            (Binding.name (Long_Name.base_name name), reccomb_fn_Ts @ [T] ---> T', NoSyn))
            (reccomb_names ~~ recTs ~~ rec_result_Ts))
      |> (Global_Theory.add_defs false o map Thm.no_attributes)
          (map
            (fn ((((name, comb), set), T), T') =>
              (Binding.name (Thm.def_name (Long_Name.base_name name)),
                Logic.mk_equals (comb, fold_rev lambda rec_fns (absfree ("x", T)
                 (Const (@{const_name The}, (T' --> HOLogic.boolT) --> T') $ absfree ("y", T')
                   (set $ Free ("x", T) $ Free ("y", T')))))))
            (reccomb_names ~~ reccombs ~~ rec_sets ~~ recTs ~~ rec_result_Ts))
      ||> Sign.parent_path
      ||> Theory.checkpoint;


    (* prove characteristic equations for primrec combinators *)

    val _ = Datatype_Aux.message config "Proving characteristic theorems for primrec combinators ...";

    val rec_thms =
      map (fn t =>
        Skip_Proof.prove_global thy2 [] [] t
          (fn _ => EVERY
            [rewrite_goals_tac reccomb_defs,
             rtac @{thm the1_equality} 1,
             resolve_tac rec_unique_thms 1,
             resolve_tac rec_intrs 1,
             REPEAT (rtac allI 1 ORELSE resolve_tac rec_total_thms 1)]))
       (Datatype_Prop.make_primrecs reccomb_names descr thy2);
  in
    thy2
    |> Sign.add_path (space_implode "_" new_type_names)
    |> Global_Theory.note_thmss ""
      [((Binding.name "recs", [Nitpick_Simps.add]), [(rec_thms, [])])]
    ||> Sign.parent_path
    ||> Theory.checkpoint
    |-> (fn thms => pair (reccomb_names, maps #2 thms))
  end;


(* case combinators *)

fun prove_case_thms (config : Datatype_Aux.config)
    new_type_names descr reccomb_names primrec_thms thy =
  let
    val _ = Datatype_Aux.message config "Proving characteristic theorems for case combinators ...";

    val thy1 = Sign.add_path (space_implode "_" new_type_names) thy;

    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val used = fold Term.add_tfree_namesT recTs [];
    val newTs = take (length (hd descr)) recTs;
    val T' = TFree (singleton (Name.variant_list used) "'t", HOLogic.typeS);

    fun mk_dummyT dt = binder_types (Datatype_Aux.typ_of_dtyp descr' dt) ---> T';

    val case_dummy_fns =
      map (fn (_, (_, _, constrs)) => map (fn (_, cargs) =>
        let
          val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
          val Ts' = map mk_dummyT (filter Datatype_Aux.is_rec_type cargs)
        in Const (@{const_name undefined}, Ts @ Ts' ---> T') end) constrs) descr';

    val case_names = map (fn s => Sign.full_bname thy1 (s ^ "_case")) new_type_names;

    (* define case combinators via primrec combinators *)

    val (case_defs, thy2) =
      fold (fn ((((i, (_, _, constrs)), T), name), recname) => fn (defs, thy) =>
          let
            val (fns1, fns2) = split_list (map (fn ((_, cargs), j) =>
              let
                val Ts = map (Datatype_Aux.typ_of_dtyp descr') cargs;
                val Ts' = Ts @ map mk_dummyT (filter Datatype_Aux.is_rec_type cargs);
                val frees' = map2 (Datatype_Aux.mk_Free "x") Ts' (1 upto length Ts');
                val frees = take (length cargs) frees';
                val free = Datatype_Aux.mk_Free "f" (Ts ---> T') j;
              in
                (free, fold_rev (absfree o dest_Free) frees' (list_comb (free, frees)))
              end) (constrs ~~ (1 upto length constrs)));

            val caseT = map (snd o dest_Free) fns1 @ [T] ---> T';
            val fns = flat (take i case_dummy_fns) @ fns2 @ flat (drop (i + 1) case_dummy_fns);
            val reccomb = Const (recname, (map fastype_of fns) @ [T] ---> T');
            val decl = ((Binding.name (Long_Name.base_name name), caseT), NoSyn);
            val def =
              (Binding.name (Thm.def_name (Long_Name.base_name name)),
                Logic.mk_equals (Const (name, caseT),
                  fold_rev lambda fns1
                    (list_comb (reccomb,
                      flat (take i case_dummy_fns) @ fns2 @ flat (drop (i + 1) case_dummy_fns)))));
            val ([def_thm], thy') =
              thy
              |> Sign.declare_const_global decl |> snd
              |> (Global_Theory.add_defs false o map Thm.no_attributes) [def];

          in (defs @ [def_thm], thy') end)
        (hd descr ~~ newTs ~~ case_names ~~ take (length newTs) reccomb_names) ([], thy1)
      ||> Theory.checkpoint;

    val case_thms =
      (map o map) (fn t =>
          Skip_Proof.prove_global thy2 [] [] t
            (fn _ =>
              EVERY [rewrite_goals_tac (case_defs @ map mk_meta_eq primrec_thms), rtac refl 1]))
        (Datatype_Prop.make_cases case_names descr thy2);
  in
    thy2
    |> Context.theory_map ((fold o fold) Nitpick_Simps.add_thm case_thms)
    |> Sign.parent_path
    |> Datatype_Aux.store_thmss "cases" new_type_names case_thms
    |-> (fn thmss => pair (thmss, case_names))
  end;


(* case splitting *)

fun prove_split_thms (config : Datatype_Aux.config)
    new_type_names case_names descr constr_inject dist_rewrites casedist_thms case_thms thy =
  let
    val _ = Datatype_Aux.message config "Proving equations for case splitting ...";

    val descr' = flat descr;
    val recTs = Datatype_Aux.get_rec_types descr';
    val newTs = take (length (hd descr)) recTs;

    fun prove_split_thms ((((((t1, t2), inject), dist_rewrites'), exhaustion), case_thms'), T) =
      let
        val cert = cterm_of thy;
        val _ $ (_ $ lhs $ _) = hd (Logic.strip_assums_hyp (hd (prems_of exhaustion)));
        val exhaustion' = cterm_instantiate [(cert lhs, cert (Free ("x", T)))] exhaustion;
        val tac =
          EVERY [rtac exhaustion' 1,
            ALLGOALS (asm_simp_tac (HOL_ss addsimps (dist_rewrites' @ inject @ case_thms')))];
      in
        (Skip_Proof.prove_global thy [] [] t1 (K tac),
         Skip_Proof.prove_global thy [] [] t2 (K tac))
      end;

    val split_thm_pairs =
      map prove_split_thms
        (Datatype_Prop.make_splits case_names descr thy ~~ constr_inject ~~
          dist_rewrites ~~ casedist_thms ~~ case_thms ~~ newTs);

    val (split_thms, split_asm_thms) = split_list split_thm_pairs

  in
    thy
    |> Datatype_Aux.store_thms "split" new_type_names split_thms
    ||>> Datatype_Aux.store_thms "split_asm" new_type_names split_asm_thms
    |-> (fn (thms1, thms2) => pair (thms1 ~~ thms2))
  end;

fun prove_weak_case_congs new_type_names case_names descr thy =
  let
    fun prove_weak_case_cong t =
     Skip_Proof.prove_global thy [] (Logic.strip_imp_prems t) (Logic.strip_imp_concl t)
       (fn {prems, ...} => EVERY [rtac (hd prems RS arg_cong) 1]);

    val weak_case_congs =
      map prove_weak_case_cong (Datatype_Prop.make_weak_case_congs case_names descr thy);

  in thy |> Datatype_Aux.store_thms "weak_case_cong" new_type_names weak_case_congs end;


(* additional theorems for TFL *)

fun prove_nchotomys (config : Datatype_Aux.config) new_type_names descr casedist_thms thy =
  let
    val _ = Datatype_Aux.message config "Proving additional theorems for TFL ...";

    fun prove_nchotomy (t, exhaustion) =
      let
        (* For goal i, select the correct disjunct to attack, then prove it *)
        fun tac i 0 = EVERY [TRY (rtac disjI1 i), hyp_subst_tac i, REPEAT (rtac exI i), rtac refl i]
          | tac i n = rtac disjI2 i THEN tac i (n - 1);
      in
        Skip_Proof.prove_global thy [] [] t
          (fn _ =>
            EVERY [rtac allI 1,
             Datatype_Aux.exh_tac (K exhaustion) 1,
             ALLGOALS (fn i => tac i (i - 1))])
      end;

    val nchotomys =
      map prove_nchotomy (Datatype_Prop.make_nchotomys descr ~~ casedist_thms);

  in thy |> Datatype_Aux.store_thms "nchotomy" new_type_names nchotomys end;

fun prove_case_congs new_type_names case_names descr nchotomys case_thms thy =
  let
    fun prove_case_cong ((t, nchotomy), case_rewrites) =
      let
        val Const ("==>", _) $ tm $ _ = t;
        val Const (@{const_name Trueprop}, _) $ (Const (@{const_name HOL.eq}, _) $ _ $ Ma) = tm;
        val cert = cterm_of thy;
        val nchotomy' = nchotomy RS spec;
        val [v] = Term.add_vars (concl_of nchotomy') [];
        val nchotomy'' = cterm_instantiate [(cert (Var v), cert Ma)] nchotomy';
      in
        Skip_Proof.prove_global thy [] (Logic.strip_imp_prems t) (Logic.strip_imp_concl t)
          (fn {prems, ...} =>
            let val simplify = asm_simp_tac (HOL_ss addsimps (prems @ case_rewrites)) in
              EVERY [
                simp_tac (HOL_ss addsimps [hd prems]) 1,
                cut_tac nchotomy'' 1,
                REPEAT (etac disjE 1 THEN REPEAT (etac exE 1) THEN simplify 1),
                REPEAT (etac exE 1) THEN simplify 1 (* Get last disjunct *)]
            end)
      end;

    val case_congs =
      map prove_case_cong
        (Datatype_Prop.make_case_congs case_names descr thy ~~ nchotomys ~~ case_thms);

  in thy |> Datatype_Aux.store_thms "case_cong" new_type_names case_congs end;



(** derive datatype props **)

local

fun make_dt_info descr induct inducts rec_names rec_rewrites
    (index, (((((((((((_, (tname, _, _))), inject), distinct),
      exhaust), nchotomy), case_name), case_rewrites), case_cong), weak_case_cong),
        (split, split_asm))) =
  (tname,
   {index = index,
    descr = descr,
    inject = inject,
    distinct = distinct,
    induct = induct,
    inducts = inducts,
    exhaust = exhaust,
    nchotomy = nchotomy,
    rec_names = rec_names,
    rec_rewrites = rec_rewrites,
    case_name = case_name,
    case_rewrites = case_rewrites,
    case_cong = case_cong,
    weak_case_cong = weak_case_cong,
    split = split,
    split_asm = split_asm});

in

fun derive_datatype_props config dt_names descr induct inject distinct thy1 =
  let
    val thy2 = thy1 |> Theory.checkpoint;
    val flat_descr = flat descr;
    val new_type_names = map Long_Name.base_name dt_names;
    val _ =
      Datatype_Aux.message config
        ("Deriving properties for datatype(s) " ^ commas_quote new_type_names);

    val (exhaust, thy3) = thy2
      |> prove_casedist_thms config new_type_names descr induct
        (Datatype_Data.mk_case_names_exhausts flat_descr dt_names);
    val (nchotomys, thy4) = thy3
      |> prove_nchotomys config new_type_names descr exhaust;
    val ((rec_names, rec_rewrites), thy5) = thy4
      |> prove_primrec_thms config new_type_names descr
        (#inject o the o Symtab.lookup (Datatype_Data.get_all thy4)) inject
        (distinct, Datatype_Data.all_distincts thy2 (Datatype_Aux.get_rec_types flat_descr)) induct;
    val ((case_rewrites, case_names), thy6) = thy5
      |> prove_case_thms config new_type_names descr rec_names rec_rewrites;
    val (case_congs, thy7) = thy6
      |> prove_case_congs new_type_names case_names descr nchotomys case_rewrites;
    val (weak_case_congs, thy8) = thy7
      |> prove_weak_case_congs new_type_names case_names descr;
    val (splits, thy9) = thy8
      |> prove_split_thms config new_type_names case_names descr
        inject distinct exhaust case_rewrites;

    val inducts = Project_Rule.projections (Proof_Context.init_global thy2) induct;
    val dt_infos =
      map_index
        (make_dt_info flat_descr induct inducts rec_names rec_rewrites)
        (hd descr ~~ inject ~~ distinct ~~ exhaust ~~ nchotomys ~~
          case_names ~~ case_rewrites ~~ case_congs ~~ weak_case_congs ~~ splits);
    val dt_names = map fst dt_infos;
    val prfx = Binding.qualify true (space_implode "_" new_type_names);
    val simps = flat (inject @ distinct @ case_rewrites) @ rec_rewrites;
    val named_rules = flat (map_index (fn (i, tname) =>
      [((Binding.empty, [Induct.induct_type tname]), [([nth inducts i], [])]),
       ((Binding.empty, [Induct.cases_type tname]), [([nth exhaust i], [])])]) dt_names);
    val unnamed_rules = map (fn induct =>
      ((Binding.empty, [Rule_Cases.inner_rule, Induct.induct_type ""]), [([induct], [])]))
        (drop (length dt_names) inducts);
  in
    thy9
    |> Global_Theory.note_thmss ""
      ([((prfx (Binding.name "simps"), []), [(simps, [])]),
        ((prfx (Binding.name "inducts"), []), [(inducts, [])]),
        ((prfx (Binding.name "splits"), []), [(maps (fn (x, y) => [x, y]) splits, [])]),
        ((Binding.empty, [Simplifier.simp_add]),
          [(flat case_rewrites @ flat distinct @ rec_rewrites, [])]),
        ((Binding.empty, [Code.add_default_eqn_attribute]), [(rec_rewrites, [])]),
        ((Binding.empty, [iff_add]), [(flat inject, [])]),
        ((Binding.empty, [Classical.safe_elim NONE]),
          [(map (fn th => th RS notE) (flat distinct), [])]),
        ((Binding.empty, [Simplifier.cong_add]), [(weak_case_congs, [])]),
        ((Binding.empty, [Induct.induct_simp_add]), [(flat (distinct @ inject), [])])] @
          named_rules @ unnamed_rules)
    |> snd
    |> Datatype_Data.register dt_infos
    |> Datatype_Data.interpretation_data (config, dt_names)
    |> Datatype_Case.add_case_tr' case_names
    |> pair dt_names
  end;

end;



(** declare existing type as datatype **)

local

fun prove_rep_datatype config dt_names descr raw_inject half_distinct raw_induct thy1 =
  let
    val raw_distinct = (map o maps) (fn thm => [thm, thm RS not_sym]) half_distinct;
    val new_type_names = map Long_Name.base_name dt_names;
    val prfx = Binding.qualify true (space_implode "_" new_type_names);
    val (((inject, distinct), [(_, [induct])]), thy2) =
      thy1
      |> Datatype_Aux.store_thmss "inject" new_type_names raw_inject
      ||>> Datatype_Aux.store_thmss "distinct" new_type_names raw_distinct
      ||>> Global_Theory.note_thmss ""
        [((prfx (Binding.name "induct"), [Datatype_Data.mk_case_names_induct descr]),
          [([raw_induct], [])])];
  in
    thy2
    |> derive_datatype_props config dt_names [descr] induct inject distinct
 end;

fun gen_rep_datatype prep_term config after_qed raw_ts thy =
  let
    val ctxt = Proof_Context.init_global thy;

    fun constr_of_term (Const (c, T)) = (c, T)
      | constr_of_term t = error ("Not a constant: " ^ Syntax.string_of_term ctxt t);
    fun no_constr (c, T) =
      error ("Bad constructor: " ^ Proof_Context.extern_const ctxt c ^ "::" ^
        Syntax.string_of_typ ctxt T);
    fun type_of_constr (cT as (_, T)) =
      let
        val frees = Term.add_tfreesT T [];
        val (tyco, vs) = (apsnd o map) dest_TFree (dest_Type (body_type T))
          handle TYPE _ => no_constr cT
        val _ = if has_duplicates (eq_fst (op =)) vs then no_constr cT else ();
        val _ = if length frees <> length vs then no_constr cT else ();
      in (tyco, (vs, cT)) end;

    val raw_cs =
      AList.group (op =) (map (type_of_constr o constr_of_term o prep_term thy) raw_ts);
    val _ =
      (case map_filter (fn (tyco, _) =>
          if Symtab.defined (Datatype_Data.get_all thy) tyco then SOME tyco else NONE) raw_cs of
        [] => ()
      | tycos => error ("Type(s) " ^ commas_quote tycos ^ " already represented inductivly"));
    val raw_vss = maps (map (map snd o fst) o snd) raw_cs;
    val ms =
      (case distinct (op =) (map length raw_vss) of
         [n] => 0 upto n - 1
      | _ => error "Different types in given constructors");
    fun inter_sort m =
      map (fn xs => nth xs m) raw_vss
      |> foldr1 (Sorts.inter_sort (Sign.classes_of thy));
    val sorts = map inter_sort ms;
    val vs = Name.invent_names Name.context Name.aT sorts;

    fun norm_constr (raw_vs, (c, T)) =
      (c, map_atyps
        (TFree o (the o AList.lookup (op =) (map fst raw_vs ~~ vs)) o fst o dest_TFree) T);

    val cs = map (apsnd (map norm_constr)) raw_cs;
    val dtyps_of_typ = map (Datatype_Aux.dtyp_of_typ (map (rpair vs o fst) cs)) o binder_types;
    val dt_names = map fst cs;

    fun mk_spec (i, (tyco, constr)) =
      (i, (tyco, map Datatype_Aux.DtTFree vs, (map o apsnd) dtyps_of_typ constr));
    val descr = map_index mk_spec cs;
    val injs = Datatype_Prop.make_injs [descr];
    val half_distincts = Datatype_Prop.make_distincts [descr];
    val ind = Datatype_Prop.make_ind [descr];
    val rules = (map o map o map) Logic.close_form [[[ind]], injs, half_distincts];

    fun after_qed' raw_thms =
      let
        val [[[raw_induct]], raw_inject, half_distinct] =
          unflat rules (map Drule.zero_var_indexes_list raw_thms);
            (*FIXME somehow dubious*)
      in
        Proof_Context.background_theory_result  (* FIXME !? *)
          (prove_rep_datatype config dt_names descr raw_inject half_distinct raw_induct)
        #-> after_qed
      end;
  in
    ctxt
    |> Proof.theorem NONE after_qed' ((map o map) (rpair []) (flat rules))
  end;

in

val rep_datatype = gen_rep_datatype Sign.cert_term;
val rep_datatype_cmd = gen_rep_datatype Syntax.read_term_global;

end;


(* outer syntax *)

val _ =
  Outer_Syntax.command @{command_spec "rep_datatype"} "represent existing types inductively"
    (Scan.repeat1 Parse.term >> (fn ts =>
      Toplevel.print o
      Toplevel.theory_to_proof (rep_datatype_cmd Datatype_Aux.default_config (K I) ts)));

end;
