(*  Title:      HOL/Tools/datatype_rep_proofs.ML
    Author:     Stefan Berghofer, TU Muenchen

Definitional introduction of datatypes
Proof of characteristic theorems:

 - injectivity of constructors
 - distinctness of constructors
 - induction theorem
*)

signature DATATYPE_REP_PROOFS =
sig
  include DATATYPE_COMMON
  val representation_proofs : config -> info Symtab.table ->
    string list -> descr list -> (string * sort) list ->
      (binding * mixfix) list -> (binding * mixfix) list list -> attribute
        -> theory -> (thm list list * thm list list * thm) * theory
end;

structure DatatypeRepProofs : DATATYPE_REP_PROOFS =
struct

open DatatypeAux;

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (prems_of distinct_lemma);

val collect_simp = rewrite_rule [mk_meta_eq mem_Collect_eq];


(** theory context references **)

fun exh_thm_of (dt_info : info Symtab.table) tname =
  #exhaust (the (Symtab.lookup dt_info tname));

(******************************************************************************)

fun representation_proofs (config : config) (dt_info : info Symtab.table)
      new_type_names descr sorts types_syntax constr_syntax case_names_induct thy =
  let
    val Datatype_thy = ThyInfo.the_theory "Datatype" thy;
    val node_name = "Datatype.node";
    val In0_name = "Datatype.In0";
    val In1_name = "Datatype.In1";
    val Scons_name = "Datatype.Scons";
    val Leaf_name = "Datatype.Leaf";
    val Numb_name = "Datatype.Numb";
    val Lim_name = "Datatype.Lim";
    val Suml_name = "Datatype.Suml";
    val Sumr_name = "Datatype.Sumr";

    val [In0_inject, In1_inject, Scons_inject, Leaf_inject,
         In0_eq, In1_eq, In0_not_In1, In1_not_In0,
         Lim_inject, Suml_inject, Sumr_inject] = map (PureThy.get_thm Datatype_thy)
          ["In0_inject", "In1_inject", "Scons_inject", "Leaf_inject",
           "In0_eq", "In1_eq", "In0_not_In1", "In1_not_In0",
           "Lim_inject", "Suml_inject", "Sumr_inject"];

    val descr' = flat descr;

    val big_name = space_implode "_" new_type_names;
    val thy1 = Sign.add_path big_name thy;
    val big_rec_name = big_name ^ "_rep_set";
    val rep_set_names' =
      (if length descr' = 1 then [big_rec_name] else
        (map ((curry (op ^) (big_rec_name ^ "_")) o string_of_int)
          (1 upto (length descr'))));
    val rep_set_names = map (Sign.full_bname thy1) rep_set_names';

    val tyvars = map (fn (_, (_, Ts, _)) => map dest_DtTFree Ts) (hd descr);
    val leafTs' = get_nonrec_types descr' sorts;
    val branchTs = get_branching_types descr' sorts;
    val branchT = if null branchTs then HOLogic.unitT
      else Balanced_Tree.make (fn (T, U) => Type ("+", [T, U])) branchTs;
    val arities = remove (op =) 0 (get_arities descr');
    val unneeded_vars = subtract (op =) (List.foldr OldTerm.add_typ_tfree_names [] (leafTs' @ branchTs)) (hd tyvars);
    val leafTs = leafTs' @ (map (fn n => TFree (n, (the o AList.lookup (op =) sorts) n)) unneeded_vars);
    val recTs = get_rec_types descr' sorts;
    val newTs = Library.take (length (hd descr), recTs);
    val oldTs = Library.drop (length (hd descr), recTs);
    val sumT = if null leafTs then HOLogic.unitT
      else Balanced_Tree.make (fn (T, U) => Type ("+", [T, U])) leafTs;
    val Univ_elT = HOLogic.mk_setT (Type (node_name, [sumT, branchT]));
    val UnivT = HOLogic.mk_setT Univ_elT;
    val UnivT' = Univ_elT --> HOLogic.boolT;
    val Collect = Const ("Collect", UnivT' --> UnivT);

    val In0 = Const (In0_name, Univ_elT --> Univ_elT);
    val In1 = Const (In1_name, Univ_elT --> Univ_elT);
    val Leaf = Const (Leaf_name, sumT --> Univ_elT);
    val Lim = Const (Lim_name, (branchT --> Univ_elT) --> Univ_elT);

    (* make injections needed for embedding types in leaves *)

    fun mk_inj T' x =
      let
        fun mk_inj' T n i =
          if n = 1 then x else
          let val n2 = n div 2;
              val Type (_, [T1, T2]) = T
          in
            if i <= n2 then
              Const ("Sum_Type.Inl", T1 --> T) $ (mk_inj' T1 n2 i)
            else
              Const ("Sum_Type.Inr", T2 --> T) $ (mk_inj' T2 (n - n2) (i - n2))
          end
      in mk_inj' sumT (length leafTs) (1 + find_index (fn T'' => T'' = T') leafTs)
      end;

    (* make injections for constructors *)

    fun mk_univ_inj ts = Balanced_Tree.access
      {left = fn t => In0 $ t,
        right = fn t => In1 $ t,
        init =
          if ts = [] then Const (@{const_name undefined}, Univ_elT)
          else foldr1 (HOLogic.mk_binop Scons_name) ts};

    (* function spaces *)

    fun mk_fun_inj T' x =
      let
        fun mk_inj T n i =
          if n = 1 then x else
          let
            val n2 = n div 2;
            val Type (_, [T1, T2]) = T;
            fun mkT U = (U --> Univ_elT) --> T --> Univ_elT
          in
            if i <= n2 then Const (Suml_name, mkT T1) $ mk_inj T1 n2 i
            else Const (Sumr_name, mkT T2) $ mk_inj T2 (n - n2) (i - n2)
          end
      in mk_inj branchT (length branchTs) (1 + find_index (fn T'' => T'' = T') branchTs)
      end;

    val mk_lim = List.foldr (fn (T, t) => Lim $ mk_fun_inj T (Abs ("x", T, t)));

    (************** generate introduction rules for representing set **********)

    val _ = message config "Constructing representing sets ...";

    (* make introduction rule for a single constructor *)

    fun make_intr s n (i, (_, cargs)) =
      let
        fun mk_prem (dt, (j, prems, ts)) = (case strip_dtyp dt of
            (dts, DtRec k) =>
              let
                val Ts = map (typ_of_dtyp descr' sorts) dts;
                val free_t =
                  app_bnds (mk_Free "x" (Ts ---> Univ_elT) j) (length Ts)
              in (j + 1, list_all (map (pair "x") Ts,
                  HOLogic.mk_Trueprop
                    (Free (nth rep_set_names' k, UnivT') $ free_t)) :: prems,
                mk_lim free_t Ts :: ts)
              end
          | _ =>
              let val T = typ_of_dtyp descr' sorts dt
              in (j + 1, prems, (Leaf $ mk_inj T (mk_Free "x" T j))::ts)
              end);

        val (_, prems, ts) = List.foldr mk_prem (1, [], []) cargs;
        val concl = HOLogic.mk_Trueprop
          (Free (s, UnivT') $ mk_univ_inj ts n i)
      in Logic.list_implies (prems, concl)
      end;

    val intr_ts = maps (fn ((_, (_, _, constrs)), rep_set_name) =>
      map (make_intr rep_set_name (length constrs))
        ((1 upto (length constrs)) ~~ constrs)) (descr' ~~ rep_set_names');

    val ({raw_induct = rep_induct, intrs = rep_intrs, ...}, thy2) =
      thy1
      |> Sign.map_naming Name_Space.conceal
      |> Inductive.add_inductive_global (serial ())
          {quiet_mode = #quiet config, verbose = false, kind = Thm.internalK,
           alt_name = Binding.name big_rec_name, coind = false, no_elim = true, no_ind = false,
           skip_mono = true, fork_mono = false}
          (map (fn s => ((Binding.name s, UnivT'), NoSyn)) rep_set_names') []
          (map (fn x => (Attrib.empty_binding, x)) intr_ts) []
      ||> Sign.restore_naming thy1
      ||> Theory.checkpoint;

    (********************************* typedef ********************************)

    val (typedefs, thy3) = thy2 |>
      Sign.parent_path |>
      fold_map (fn ((((name, mx), tvs), c), name') =>
          Typedef.add_typedef false (SOME (Binding.name name')) (name, tvs, mx)
            (Collect $ Const (c, UnivT')) NONE
            (rtac exI 1 THEN rtac CollectI 1 THEN
              QUIET_BREADTH_FIRST (has_fewer_prems 1)
              (resolve_tac rep_intrs 1)))
                (types_syntax ~~ tyvars ~~
                  (Library.take (length newTs, rep_set_names)) ~~ new_type_names) ||>
      Sign.add_path big_name;

    (*********************** definition of constructors ***********************)

    val big_rep_name = (space_implode "_" new_type_names) ^ "_Rep_";
    val rep_names = map (curry op ^ "Rep_") new_type_names;
    val rep_names' = map (fn i => big_rep_name ^ (string_of_int i))
      (1 upto (length (flat (tl descr))));
    val all_rep_names = map (Sign.intern_const thy3) rep_names @
      map (Sign.full_bname thy3) rep_names';

    (* isomorphism declarations *)

    val iso_decls = map (fn (T, s) => (Binding.name s, T --> Univ_elT, NoSyn))
      (oldTs ~~ rep_names');

    (* constructor definitions *)

    fun make_constr_def tname T n ((cname, cargs), (cname', mx)) (thy, defs, eqns, i) =
      let
        fun constr_arg (dt, (j, l_args, r_args)) =
          let val T = typ_of_dtyp descr' sorts dt;
              val free_t = mk_Free "x" T j
          in (case (strip_dtyp dt, strip_type T) of
              ((_, DtRec m), (Us, U)) => (j + 1, free_t :: l_args, mk_lim
                (Const (nth all_rep_names m, U --> Univ_elT) $
                   app_bnds free_t (length Us)) Us :: r_args)
            | _ => (j + 1, free_t::l_args, (Leaf $ mk_inj T free_t)::r_args))
          end;

        val (_, l_args, r_args) = List.foldr constr_arg (1, [], []) cargs;
        val constrT = (map (typ_of_dtyp descr' sorts) cargs) ---> T;
        val abs_name = Sign.intern_const thy ("Abs_" ^ tname);
        val rep_name = Sign.intern_const thy ("Rep_" ^ tname);
        val lhs = list_comb (Const (cname, constrT), l_args);
        val rhs = mk_univ_inj r_args n i;
        val def = Logic.mk_equals (lhs, Const (abs_name, Univ_elT --> T) $ rhs);
        val def_name = Long_Name.base_name cname ^ "_def";
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> Univ_elT) $ lhs, rhs));
        val ([def_thm], thy') =
          thy
          |> Sign.add_consts_i [(cname', constrT, mx)]
          |> (PureThy.add_defs false o map Thm.no_attributes) [(Binding.name def_name, def)];

      in (thy', defs @ [def_thm], eqns @ [eqn], i + 1) end;

    (* constructor definitions for datatype *)

    fun dt_constr_defs ((((_, (_, _, constrs)), tname), T), constr_syntax)
        (thy, defs, eqns, rep_congs, dist_lemmas) =
      let
        val _ $ (_ $ (cong_f $ _) $ _) = concl_of arg_cong;
        val rep_const = cterm_of thy
          (Const (Sign.intern_const thy ("Rep_" ^ tname), T --> Univ_elT));
        val cong' =
          Drule.standard (cterm_instantiate [(cterm_of thy cong_f, rep_const)] arg_cong);
        val dist =
          Drule.standard (cterm_instantiate [(cterm_of thy distinct_f, rep_const)] distinct_lemma);
        val (thy', defs', eqns', _) = fold ((make_constr_def tname T) (length constrs))
          (constrs ~~ constr_syntax) (Sign.add_path tname thy, defs, [], 1);
      in
        (Sign.parent_path thy', defs', eqns @ [eqns'],
          rep_congs @ [cong'], dist_lemmas @ [dist])
      end;

    val (thy4, constr_defs, constr_rep_eqns, rep_congs, dist_lemmas) =
      fold dt_constr_defs
        (hd descr ~~ new_type_names ~~ newTs ~~ constr_syntax)
        (thy3 |> Sign.add_consts_i iso_decls |> Sign.parent_path, [], [], [], []);


    (*********** isomorphisms for new types (introduced by typedef) ***********)

    val _ = message config "Proving isomorphism properties ...";

    val newT_iso_axms = map (fn (_, td) =>
      (collect_simp (#Abs_inverse td), #Rep_inverse td,
       collect_simp (#Rep td))) typedefs;

    val newT_iso_inj_thms = map (fn (_, td) =>
      (collect_simp (#Abs_inject td) RS iffD1, #Rep_inject td RS iffD1)) typedefs;

    (********* isomorphisms between existing types and "unfolded" types *******)

    (*---------------------------------------------------------------------*)
    (* isomorphisms are defined using primrec-combinators:                 *)
    (* generate appropriate functions for instantiating primrec-combinator *)
    (*                                                                     *)
    (*   e.g.  dt_Rep_i = list_rec ... (%h t y. In1 (Scons (Leaf h) y))    *)
    (*                                                                     *)
    (* also generate characteristic equations for isomorphisms             *)
    (*                                                                     *)
    (*   e.g.  dt_Rep_i (cons h t) = In1 (Scons (dt_Rep_j h) (dt_Rep_i t)) *)
    (*---------------------------------------------------------------------*)

    fun make_iso_def k ks n (cname, cargs) (fs, eqns, i) =
      let
        val argTs = map (typ_of_dtyp descr' sorts) cargs;
        val T = nth recTs k;
        val rep_name = nth all_rep_names k;
        val rep_const = Const (rep_name, T --> Univ_elT);
        val constr = Const (cname, argTs ---> T);

        fun process_arg ks' dt (i2, i2', ts, Ts) =
          let
            val T' = typ_of_dtyp descr' sorts dt;
            val (Us, U) = strip_type T'
          in (case strip_dtyp dt of
              (_, DtRec j) => if j mem ks' then
                  (i2 + 1, i2' + 1, ts @ [mk_lim (app_bnds
                     (mk_Free "y" (Us ---> Univ_elT) i2') (length Us)) Us],
                   Ts @ [Us ---> Univ_elT])
                else
                  (i2 + 1, i2', ts @ [mk_lim
                     (Const (nth all_rep_names j, U --> Univ_elT) $
                        app_bnds (mk_Free "x" T' i2) (length Us)) Us], Ts)
            | _ => (i2 + 1, i2', ts @ [Leaf $ mk_inj T' (mk_Free "x" T' i2)], Ts))
          end;

        val (i2, i2', ts, Ts) = fold (process_arg ks) cargs (1, 1, [], []);
        val xs = map (uncurry (mk_Free "x")) (argTs ~~ (1 upto (i2 - 1)));
        val ys = map (uncurry (mk_Free "y")) (Ts ~~ (1 upto (i2' - 1)));
        val f = list_abs_free (map dest_Free (xs @ ys), mk_univ_inj ts n i);

        val (_, _, ts', _) = fold (process_arg []) cargs (1, 1, [], []);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (rep_const $ list_comb (constr, xs), mk_univ_inj ts' n i))

      in (fs @ [f], eqns @ [eqn], i + 1) end;

    (* define isomorphisms for all mutually recursive datatypes in list ds *)

    fun make_iso_defs ds (thy, char_thms) =
      let
        val ks = map fst ds;
        val (_, (tname, _, _)) = hd ds;
        val {rec_rewrites, rec_names, ...} = the (Symtab.lookup dt_info tname);

        fun process_dt (k, (tname, _, constrs)) (fs, eqns, isos) =
          let
            val (fs', eqns', _) =
              fold (make_iso_def k ks (length constrs)) constrs (fs, eqns, 1);
            val iso = (nth recTs k, nth all_rep_names k)
          in (fs', eqns', isos @ [iso]) end;
        
        val (fs, eqns, isos) = fold process_dt ds ([], [], []);
        val fTs = map fastype_of fs;
        val defs = map (fn (rec_name, (T, iso_name)) => (Binding.name (Long_Name.base_name iso_name ^ "_def"),
          Logic.mk_equals (Const (iso_name, T --> Univ_elT),
            list_comb (Const (rec_name, fTs @ [T] ---> Univ_elT), fs)))) (rec_names ~~ isos);
        val (def_thms, thy') =
          apsnd Theory.checkpoint ((PureThy.add_defs false o map Thm.no_attributes) defs thy);

        (* prove characteristic equations *)

        val rewrites = def_thms @ (map mk_meta_eq rec_rewrites);
        val char_thms' = map (fn eqn => Skip_Proof.prove_global thy' [] [] eqn
          (fn _ => EVERY [rewrite_goals_tac rewrites, rtac refl 1])) eqns;

      in (thy', char_thms' @ char_thms) end;

    val (thy5, iso_char_thms) = apfst Theory.checkpoint (fold_rev make_iso_defs
        (tl descr) (Sign.add_path big_name thy4, []));

    (* prove isomorphism properties *)

    fun mk_funs_inv thy thm =
      let
        val prop = Thm.prop_of thm;
        val _ $ (_ $ ((S as Const (_, Type (_, [U, _]))) $ _ )) $
          (_ $ (_ $ (r $ (a $ _)) $ _)) = Type.freeze prop;
        val used = OldTerm.add_term_tfree_names (a, []);

        fun mk_thm i =
          let
            val Ts = map (TFree o rpair HOLogic.typeS)
              (Name.variant_list used (replicate i "'t"));
            val f = Free ("f", Ts ---> U)
          in Skip_Proof.prove_global thy [] [] (Logic.mk_implies
            (HOLogic.mk_Trueprop (HOLogic.list_all
               (map (pair "x") Ts, S $ app_bnds f i)),
             HOLogic.mk_Trueprop (HOLogic.mk_eq (list_abs (map (pair "x") Ts,
               r $ (a $ app_bnds f i)), f))))
            (fn _ => EVERY [REPEAT_DETERM_N i (rtac ext 1),
               REPEAT (etac allE 1), rtac thm 1, atac 1])
          end
      in map (fn r => r RS subst) (thm :: map mk_thm arities) end;

    (* prove  inj dt_Rep_i  and  dt_Rep_i x : dt_rep_set_i *)

    val fun_congs = map (fn T => make_elim (Drule.instantiate'
      [SOME (ctyp_of thy5 T)] [] fun_cong)) branchTs;

    fun prove_iso_thms (ds, (inj_thms, elem_thms)) =
      let
        val (_, (tname, _, _)) = hd ds;
        val induct = (#induct o the o Symtab.lookup dt_info) tname;

        fun mk_ind_concl (i, _) =
          let
            val T = nth recTs i;
            val Rep_t = Const (nth all_rep_names i, T --> Univ_elT);
            val rep_set_name = nth rep_set_names i
          in (HOLogic.all_const T $ Abs ("y", T, HOLogic.imp $
                HOLogic.mk_eq (Rep_t $ mk_Free "x" T i, Rep_t $ Bound 0) $
                  HOLogic.mk_eq (mk_Free "x" T i, Bound 0)),
              Const (rep_set_name, UnivT') $ (Rep_t $ mk_Free "x" T i))
          end;

        val (ind_concl1, ind_concl2) = ListPair.unzip (map mk_ind_concl ds);

        val rewrites = map mk_meta_eq iso_char_thms;
        val inj_thms' = map snd newT_iso_inj_thms @
          map (fn r => r RS @{thm injD}) inj_thms;

        val inj_thm = Skip_Proof.prove_global thy5 [] []
          (HOLogic.mk_Trueprop (mk_conj ind_concl1)) (fn _ => EVERY
            [(indtac induct [] THEN_ALL_NEW ObjectLogic.atomize_prems_tac) 1,
             REPEAT (EVERY
               [rtac allI 1, rtac impI 1,
                exh_tac (exh_thm_of dt_info) 1,
                REPEAT (EVERY
                  [hyp_subst_tac 1,
                   rewrite_goals_tac rewrites,
                   REPEAT (dresolve_tac [In0_inject, In1_inject] 1),
                   (eresolve_tac [In0_not_In1 RS notE, In1_not_In0 RS notE] 1)
                   ORELSE (EVERY
                     [REPEAT (eresolve_tac (Scons_inject ::
                        map make_elim [Leaf_inject, Inl_inject, Inr_inject]) 1),
                      REPEAT (cong_tac 1), rtac refl 1,
                      REPEAT (atac 1 ORELSE (EVERY
                        [REPEAT (rtac ext 1),
                         REPEAT (eresolve_tac (mp :: allE ::
                           map make_elim (Suml_inject :: Sumr_inject ::
                             Lim_inject :: inj_thms') @ fun_congs) 1),
                         atac 1]))])])])]);

        val inj_thms'' = map (fn r => r RS @{thm datatype_injI})
                             (split_conj_thm inj_thm);

        val elem_thm = 
            Skip_Proof.prove_global thy5 [] [] (HOLogic.mk_Trueprop (mk_conj ind_concl2))
              (fn _ =>
               EVERY [(indtac induct [] THEN_ALL_NEW ObjectLogic.atomize_prems_tac) 1,
                rewrite_goals_tac rewrites,
                REPEAT ((resolve_tac rep_intrs THEN_ALL_NEW
                  ((REPEAT o etac allE) THEN' ares_tac elem_thms)) 1)]);

      in (inj_thms'' @ inj_thms, elem_thms @ (split_conj_thm elem_thm))
      end;

    val (iso_inj_thms_unfolded, iso_elem_thms) = List.foldr prove_iso_thms
      ([], map #3 newT_iso_axms) (tl descr);
    val iso_inj_thms = map snd newT_iso_inj_thms @
      map (fn r => r RS @{thm injD}) iso_inj_thms_unfolded;

    (* prove  dt_rep_set_i x --> x : range dt_Rep_i *)

    fun mk_iso_t (((set_name, iso_name), i), T) =
      let val isoT = T --> Univ_elT
      in HOLogic.imp $ 
        (Const (set_name, UnivT') $ mk_Free "x" Univ_elT i) $
          (if i < length newTs then HOLogic.true_const
           else HOLogic.mk_mem (mk_Free "x" Univ_elT i,
             Const (@{const_name image}, isoT --> HOLogic.mk_setT T --> UnivT) $
               Const (iso_name, isoT) $ Const (@{const_name UNIV}, HOLogic.mk_setT T)))
      end;

    val iso_t = HOLogic.mk_Trueprop (mk_conj (map mk_iso_t
      (rep_set_names ~~ all_rep_names ~~ (0 upto (length descr' - 1)) ~~ recTs)));

    (* all the theorems are proved by one single simultaneous induction *)

    val range_eqs = map (fn r => mk_meta_eq (r RS @{thm range_ex1_eq}))
      iso_inj_thms_unfolded;

    val iso_thms = if length descr = 1 then [] else
      Library.drop (length newTs, split_conj_thm
        (Skip_Proof.prove_global thy5 [] [] iso_t (fn _ => EVERY
           [(indtac rep_induct [] THEN_ALL_NEW ObjectLogic.atomize_prems_tac) 1,
            REPEAT (rtac TrueI 1),
            rewrite_goals_tac (mk_meta_eq choice_eq ::
              symmetric (mk_meta_eq @{thm expand_fun_eq}) :: range_eqs),
            rewrite_goals_tac (map symmetric range_eqs),
            REPEAT (EVERY
              [REPEAT (eresolve_tac ([rangeE, ex1_implies_ex RS exE] @
                 maps (mk_funs_inv thy5 o #1) newT_iso_axms) 1),
               TRY (hyp_subst_tac 1),
               rtac (sym RS range_eqI) 1,
               resolve_tac iso_char_thms 1])])));

    val Abs_inverse_thms' =
      map #1 newT_iso_axms @
      map2 (fn r_inj => fn r => @{thm f_the_inv_into_f} OF [r_inj, r RS mp])
        iso_inj_thms_unfolded iso_thms;

    val Abs_inverse_thms = maps (mk_funs_inv thy5) Abs_inverse_thms';

    (******************* freeness theorems for constructors *******************)

    val _ = message config "Proving freeness of constructors ...";

    (* prove theorem  Rep_i (Constr_j ...) = Inj_j ...  *)
    
    fun prove_constr_rep_thm eqn =
      let
        val inj_thms = map fst newT_iso_inj_thms;
        val rewrites = @{thm o_def} :: constr_defs @ (map (mk_meta_eq o #2) newT_iso_axms)
      in Skip_Proof.prove_global thy5 [] [] eqn (fn _ => EVERY
        [resolve_tac inj_thms 1,
         rewrite_goals_tac rewrites,
         rtac refl 3,
         resolve_tac rep_intrs 2,
         REPEAT (resolve_tac iso_elem_thms 1)])
      end;

    (*--------------------------------------------------------------*)
    (* constr_rep_thms and rep_congs are used to prove distinctness *)
    (* of constructors.                                             *)
    (*--------------------------------------------------------------*)

    val constr_rep_thms = map (map prove_constr_rep_thm) constr_rep_eqns;

    val dist_rewrites = map (fn (rep_thms, dist_lemma) =>
      dist_lemma::(rep_thms @ [In0_eq, In1_eq, In0_not_In1, In1_not_In0]))
        (constr_rep_thms ~~ dist_lemmas);

    fun prove_distinct_thms dist_rewrites' (k, ts) =
      let
        fun prove [] = []
          | prove (t :: ts) =
              let
                val dist_thm = Skip_Proof.prove_global thy5 [] [] t (fn _ =>
                  EVERY [simp_tac (HOL_ss addsimps dist_rewrites') 1])
              in dist_thm :: Drule.standard (dist_thm RS not_sym) :: prove ts end;
      in prove ts end;

    val distinct_thms = map2 (prove_distinct_thms)
      dist_rewrites (DatatypeProp.make_distincts descr sorts);

    (* prove injectivity of constructors *)

    fun prove_constr_inj_thm rep_thms t =
      let val inj_thms = Scons_inject :: (map make_elim
        (iso_inj_thms @
          [In0_inject, In1_inject, Leaf_inject, Inl_inject, Inr_inject,
           Lim_inject, Suml_inject, Sumr_inject]))
      in Skip_Proof.prove_global thy5 [] [] t (fn _ => EVERY
        [rtac iffI 1,
         REPEAT (etac conjE 2), hyp_subst_tac 2, rtac refl 2,
         dresolve_tac rep_congs 1, dtac box_equals 1,
         REPEAT (resolve_tac rep_thms 1),
         REPEAT (eresolve_tac inj_thms 1),
         REPEAT (ares_tac [conjI] 1 ORELSE (EVERY [REPEAT (rtac ext 1),
           REPEAT (eresolve_tac (make_elim fun_cong :: inj_thms) 1),
           atac 1]))])
      end;

    val constr_inject = map (fn (ts, thms) => map (prove_constr_inj_thm thms) ts)
      ((DatatypeProp.make_injs descr sorts) ~~ constr_rep_thms);

    val ((constr_inject', distinct_thms'), thy6) =
      thy5
      |> Sign.parent_path
      |> store_thmss "inject" new_type_names constr_inject
      ||>> store_thmss "distinct" new_type_names distinct_thms;

    (*************************** induction theorem ****************************)

    val _ = message config "Proving induction rule for datatypes ...";

    val Rep_inverse_thms = (map (fn (_, iso, _) => iso RS subst) newT_iso_axms) @
      (map (fn r => r RS @{thm the_inv_f_f} RS subst) iso_inj_thms_unfolded);
    val Rep_inverse_thms' = map (fn r => r RS @{thm the_inv_f_f}) iso_inj_thms_unfolded;

    fun mk_indrule_lemma ((i, _), T) (prems, concls) =
      let
        val Rep_t = Const (nth all_rep_names i, T --> Univ_elT) $
          mk_Free "x" T i;

        val Abs_t = if i < length newTs then
            Const (Sign.intern_const thy6
              ("Abs_" ^ (nth new_type_names i)), Univ_elT --> T)
          else Const (@{const_name the_inv_into},
              [HOLogic.mk_setT T, T --> Univ_elT, Univ_elT] ---> T) $
            HOLogic.mk_UNIV T $ Const (nth all_rep_names i, T --> Univ_elT)

      in (prems @ [HOLogic.imp $
            (Const (nth rep_set_names i, UnivT') $ Rep_t) $
              (mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ (Abs_t $ Rep_t))],
          concls @ [mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ mk_Free "x" T i])
      end;

    val (indrule_lemma_prems, indrule_lemma_concls) =
      fold mk_indrule_lemma (descr' ~~ recTs) ([], []);

    val cert = cterm_of thy6;

    val indrule_lemma = Skip_Proof.prove_global thy6 [] []
      (Logic.mk_implies
        (HOLogic.mk_Trueprop (mk_conj indrule_lemma_prems),
         HOLogic.mk_Trueprop (mk_conj indrule_lemma_concls))) (fn _ => EVERY
           [REPEAT (etac conjE 1),
            REPEAT (EVERY
              [TRY (rtac conjI 1), resolve_tac Rep_inverse_thms 1,
               etac mp 1, resolve_tac iso_elem_thms 1])]);

    val Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule_lemma)));
    val frees = if length Ps = 1 then [Free ("P", snd (dest_Var (hd Ps)))] else
      map (Free o apfst fst o dest_Var) Ps;
    val indrule_lemma' = cterm_instantiate (map cert Ps ~~ map cert frees) indrule_lemma;

    val dt_induct_prop = DatatypeProp.make_ind descr sorts;
    val dt_induct = Skip_Proof.prove_global thy6 []
      (Logic.strip_imp_prems dt_induct_prop) (Logic.strip_imp_concl dt_induct_prop)
      (fn {prems, ...} => EVERY
        [rtac indrule_lemma' 1,
         (indtac rep_induct [] THEN_ALL_NEW ObjectLogic.atomize_prems_tac) 1,
         EVERY (map (fn (prem, r) => (EVERY
           [REPEAT (eresolve_tac Abs_inverse_thms 1),
            simp_tac (HOL_basic_ss addsimps ((symmetric r)::Rep_inverse_thms')) 1,
            DEPTH_SOLVE_1 (ares_tac [prem] 1 ORELSE etac allE 1)]))
                (prems ~~ (constr_defs @ (map mk_meta_eq iso_char_thms))))]);

    val ([dt_induct'], thy7) =
      thy6
      |> Sign.add_path big_name
      |> PureThy.add_thms [((Binding.name "induct", dt_induct), [case_names_induct])]
      ||> Sign.parent_path
      ||> Theory.checkpoint;

  in
    ((constr_inject', distinct_thms', dt_induct'), thy7)
  end;

end;
