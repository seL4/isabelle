(*  Title:      HOL/Tools/datatype_rep_proofs.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definitional introduction of datatypes
Proof of characteristic theorems:

 - injectivity of constructors
 - distinctness of constructors
 - induction theorem

*)

signature DATATYPE_REP_PROOFS =
sig
  val representation_proofs : bool -> DatatypeAux.datatype_info Symtab.table ->
    string list -> (int * (string * DatatypeAux.dtyp list *
      (string * DatatypeAux.dtyp list) list)) list list -> (string * sort) list ->
        (string * mixfix) list -> (string * mixfix) list list -> theory attribute
          -> theory -> theory * thm list list * thm list list * thm list list *
            DatatypeAux.simproc_dist list * thm
end;

structure DatatypeRepProofs : DATATYPE_REP_PROOFS =
struct

open DatatypeAux;

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (prems_of distinct_lemma);


(** theory context references **)

val f_myinv_f = thm "f_myinv_f";
val myinv_f_f = thm "myinv_f_f";


fun exh_thm_of (dt_info : datatype_info Symtab.table) tname =
  #exhaustion (the (Symtab.lookup (dt_info, tname)));

(******************************************************************************)

fun representation_proofs flat_names (dt_info : datatype_info Symtab.table)
      new_type_names descr sorts types_syntax constr_syntax case_names_induct thy =
  let
    val Datatype_thy = theory "Datatype";
    val node_name = Sign.intern_tycon (Theory.sign_of Datatype_thy) "node";
    val [In0_name, In1_name, Scons_name, Leaf_name, Numb_name, Lim_name,
      Funs_name, o_name, sum_case_name] =
      map (Sign.intern_const (Theory.sign_of Datatype_thy))
        ["In0", "In1", "Scons", "Leaf", "Numb", "Lim", "Funs", "op o", "sum_case"];

    val [In0_inject, In1_inject, Scons_inject, Leaf_inject, In0_eq, In1_eq,
         In0_not_In1, In1_not_In0, Funs_mono, FunsI, Lim_inject,
         Funs_inv, FunsD, Funs_rangeE, Funs_nonempty, sum_case_inject] = map (get_thm Datatype_thy)
        ["In0_inject", "In1_inject", "Scons_inject", "Leaf_inject", "In0_eq", "In1_eq",
         "In0_not_In1", "In1_not_In0", "Funs_mono", "FunsI", "Lim_inject",
         "Funs_inv", "FunsD", "Funs_rangeE", "Funs_nonempty", "sum_case_inject"];

    val Funs_IntE = (Int_lower2 RS Funs_mono RS
      (Int_lower1 RS Funs_mono RS Int_greatest) RS subsetD) RS IntE;

    val descr' = flat descr;

    val big_name = space_implode "_" new_type_names;
    val thy1 = add_path flat_names big_name thy;
    val big_rec_name = big_name ^ "_rep_set";
    val rep_set_names = map (Sign.full_name (Theory.sign_of thy1))
      (if length descr' = 1 then [big_rec_name] else
        (map ((curry (op ^) (big_rec_name ^ "_")) o string_of_int)
          (1 upto (length descr'))));

    val tyvars = map (fn (_, (_, Ts, _)) => map dest_DtTFree Ts) (hd descr);
    val leafTs' = get_nonrec_types descr' sorts;
    val branchTs = get_branching_types descr' sorts;
    val branchT = if null branchTs then HOLogic.unitT
      else fold_bal (fn (T, U) => Type ("+", [T, U])) branchTs;
    val unneeded_vars = hd tyvars \\ foldr add_typ_tfree_names (leafTs' @ branchTs, []);
    val leafTs = leafTs' @ (map (fn n => TFree (n, the (assoc (sorts, n)))) unneeded_vars);
    val recTs = get_rec_types descr' sorts;
    val newTs = take (length (hd descr), recTs);
    val oldTs = drop (length (hd descr), recTs);
    val sumT = if null leafTs then HOLogic.unitT
      else fold_bal (fn (T, U) => Type ("+", [T, U])) leafTs;
    val Univ_elT = HOLogic.mk_setT (Type (node_name, [sumT, branchT]));
    val UnivT = HOLogic.mk_setT Univ_elT;

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
              Const ("Inl", T1 --> T) $ (mk_inj' T1 n2 i)
            else
              Const ("Inr", T2 --> T) $ (mk_inj' T2 (n - n2) (i - n2))
          end
      in mk_inj' sumT (length leafTs) (1 + find_index_eq T' leafTs)
      end;

    (* make injections for constructors *)

    fun mk_univ_inj ts = access_bal (fn t => In0 $ t, fn t => In1 $ t, if ts = [] then
        Const ("arbitrary", Univ_elT)
      else
        foldr1 (HOLogic.mk_binop Scons_name) ts);

    (* function spaces *)

    fun mk_fun_inj T' x =
      let
        fun mk_inj T n i =
          if n = 1 then x else
          let
            val n2 = n div 2;
            val Type (_, [T1, T2]) = T;
            val sum_case = Const (sum_case_name, [T1 --> Univ_elT, T2 --> Univ_elT, T] ---> Univ_elT)
          in
            if i <= n2 then
              sum_case $ (mk_inj T1 n2 i) $ Const ("arbitrary", T2 --> Univ_elT)
            else
              sum_case $ Const ("arbitrary", T1 --> Univ_elT) $ mk_inj T2 (n - n2) (i - n2)
          end
      in mk_inj branchT (length branchTs) (1 + find_index_eq T' branchTs)
      end;

    (************** generate introduction rules for representing set **********)

    val _ = message "Constructing representing sets ...";

    (* make introduction rule for a single constructor *)

    fun make_intr s n (i, (_, cargs)) =
      let
        fun mk_prem (DtRec k, (j, prems, ts)) =
              let val free_t = mk_Free "x" Univ_elT j
              in (j + 1, (HOLogic.mk_mem (free_t,
                Const (nth_elem (k, rep_set_names), UnivT)))::prems, free_t::ts)
              end
          | mk_prem (DtType ("fun", [T, DtRec k]), (j, prems, ts)) =
              let val T' = typ_of_dtyp descr' sorts T;
                  val free_t = mk_Free "x" (T' --> Univ_elT) j
              in (j + 1, (HOLogic.mk_mem (free_t,
                Const (Funs_name, UnivT --> HOLogic.mk_setT (T' --> Univ_elT)) $
                  Const (nth_elem (k, rep_set_names), UnivT)))::prems,
                    Lim $ mk_fun_inj T' free_t::ts)
              end
          | mk_prem (dt, (j, prems, ts)) =
              let val T = typ_of_dtyp descr' sorts dt
              in (j + 1, prems, (Leaf $ mk_inj T (mk_Free "x" T j))::ts)
              end;

        val (_, prems, ts) = foldr mk_prem (cargs, (1, [], []));
        val concl = HOLogic.mk_Trueprop (HOLogic.mk_mem
          (mk_univ_inj ts n i, Const (s, UnivT)))
      in Logic.list_implies (map HOLogic.mk_Trueprop prems, concl)
      end;

    val consts = map (fn s => Const (s, UnivT)) rep_set_names;

    val intr_ts = flat (map (fn ((_, (_, _, constrs)), rep_set_name) =>
      map (make_intr rep_set_name (length constrs))
        ((1 upto (length constrs)) ~~ constrs)) (descr' ~~ rep_set_names));

    val (thy2, {raw_induct = rep_induct, intrs = rep_intrs, ...}) =
      setmp InductivePackage.quiet_mode (!quiet_mode)
        (InductivePackage.add_inductive_i false true big_rec_name false true false
           consts (map (fn x => (("", x), [])) intr_ts) [Funs_mono] []) thy1;

    (********************************* typedef ********************************)

    val thy3 = add_path flat_names big_name (foldl (fn (thy, ((((name, mx), tvs), c), name')) =>
      setmp TypedefPackage.quiet_mode true
        (TypedefPackage.add_typedef_i_no_def name' (name, tvs, mx) c [] []
          (Some (QUIET_BREADTH_FIRST (has_fewer_prems 1)
            (resolve_tac (Funs_nonempty::rep_intrs) 1)))) thy |> #1)
              (parent_path flat_names thy2, types_syntax ~~ tyvars ~~
                (take (length newTs, consts)) ~~ new_type_names));

    (*********************** definition of constructors ***********************)

    val big_rep_name = (space_implode "_" new_type_names) ^ "_Rep_";
    val rep_names = map (curry op ^ "Rep_") new_type_names;
    val rep_names' = map (fn i => big_rep_name ^ (string_of_int i))
      (1 upto (length (flat (tl descr))));
    val all_rep_names = map (Sign.intern_const (Theory.sign_of thy3)) rep_names @
      map (Sign.full_name (Theory.sign_of thy3)) rep_names';

    (* isomorphism declarations *)

    val iso_decls = map (fn (T, s) => (s, T --> Univ_elT, NoSyn))
      (oldTs ~~ rep_names');

    (* constructor definitions *)

    fun make_constr_def tname T n ((thy, defs, eqns, i), ((cname, cargs), (cname', mx))) =
      let
        fun constr_arg (dt, (j, l_args, r_args)) =
          let val T = typ_of_dtyp descr' sorts dt;
              val free_t = mk_Free "x" T j
          in (case dt of
              DtRec m => (j + 1, free_t::l_args, (Const (nth_elem (m, all_rep_names),
                T --> Univ_elT) $ free_t)::r_args)
            | DtType ("fun", [T', DtRec m]) =>
                let val ([T''], T''') = strip_type T
                in (j + 1, free_t::l_args, (Lim $ mk_fun_inj T''
                  (Const (o_name, [T''' --> Univ_elT, T, T''] ---> Univ_elT) $
                    Const (nth_elem (m, all_rep_names), T''' --> Univ_elT) $ free_t))::r_args)
                end

            | _ => (j + 1, free_t::l_args, (Leaf $ mk_inj T free_t)::r_args))
          end;

        val (_, l_args, r_args) = foldr constr_arg (cargs, (1, [], []));
        val constrT = (map (typ_of_dtyp descr' sorts) cargs) ---> T;
        val abs_name = Sign.intern_const (Theory.sign_of thy) ("Abs_" ^ tname);
        val rep_name = Sign.intern_const (Theory.sign_of thy) ("Rep_" ^ tname);
        val lhs = list_comb (Const (cname, constrT), l_args);
        val rhs = mk_univ_inj r_args n i;
        val def = equals T $ lhs $ (Const (abs_name, Univ_elT --> T) $ rhs);
        val def_name = (Sign.base_name cname) ^ "_def";
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> Univ_elT) $ lhs, rhs));
        val (thy', [def_thm]) = thy |>
          Theory.add_consts_i [(cname', constrT, mx)] |>
          (PureThy.add_defs_i false o map Thm.no_attributes) [(def_name, def)];

      in (thy', defs @ [def_thm], eqns @ [eqn], i + 1) end;

    (* constructor definitions for datatype *)

    fun dt_constr_defs ((thy, defs, eqns, rep_congs, dist_lemmas),
        ((((_, (_, _, constrs)), tname), T), constr_syntax)) =
      let
        val _ $ (_ $ (cong_f $ _) $ _) = concl_of arg_cong;
        val sg = Theory.sign_of thy;
        val rep_const = cterm_of sg
          (Const (Sign.intern_const sg ("Rep_" ^ tname), T --> Univ_elT));
        val cong' = standard (cterm_instantiate [(cterm_of sg cong_f, rep_const)] arg_cong);
        val dist = standard (cterm_instantiate [(cterm_of sg distinct_f, rep_const)] distinct_lemma);
        val (thy', defs', eqns', _) = foldl ((make_constr_def tname T) (length constrs))
          ((add_path flat_names tname thy, defs, [], 1), constrs ~~ constr_syntax)
      in
        (parent_path flat_names thy', defs', eqns @ [eqns'],
          rep_congs @ [cong'], dist_lemmas @ [dist])
      end;

    val (thy4, constr_defs, constr_rep_eqns, rep_congs, dist_lemmas) = foldl dt_constr_defs
      ((thy3 |> Theory.add_consts_i iso_decls |> parent_path flat_names, [], [], [], []),
        hd descr ~~ new_type_names ~~ newTs ~~ constr_syntax);

    (*********** isomorphisms for new types (introduced by typedef) ***********)

    val _ = message "Proving isomorphism properties ...";

    (* get axioms from theory *)

    val newT_iso_axms = map (fn s =>
      (get_thm thy4 ("Abs_" ^ s ^ "_inverse"),
       get_thm thy4 ("Rep_" ^ s ^ "_inverse"),
       get_thm thy4 ("Rep_" ^ s))) new_type_names;

    (*------------------------------------------------*)
    (* prove additional theorems:                     *)
    (*  inj_on dt_Abs_i rep_set_i  and  inj dt_Rep_i  *)
    (*------------------------------------------------*)

    fun prove_newT_iso_inj_thm (((s, (thm1, thm2, _)), T), rep_set_name) =
      let
        val sg = Theory.sign_of thy4;
        val RepT = T --> Univ_elT;
        val Rep_name = Sign.intern_const sg ("Rep_" ^ s);
        val AbsT = Univ_elT --> T;
        val Abs_name = Sign.intern_const sg ("Abs_" ^ s);

        val inj_Abs_thm = 
	    prove_goalw_cterm [] 
	      (cterm_of sg
	       (HOLogic.mk_Trueprop 
		(Const ("Fun.inj_on", [AbsT, UnivT] ---> HOLogic.boolT) $
		 Const (Abs_name, AbsT) $ Const (rep_set_name, UnivT))))
              (fn _ => [rtac inj_on_inverseI 1, etac thm1 1]);

        val setT = HOLogic.mk_setT T

        val inj_Rep_thm =
	    prove_goalw_cterm []
	      (cterm_of sg
	       (HOLogic.mk_Trueprop
		(Const ("Fun.inj_on", [RepT, setT] ---> HOLogic.boolT) $
		 Const (Rep_name, RepT) $ Const ("UNIV", setT))))
              (fn _ => [rtac inj_inverseI 1, rtac thm2 1])

      in (inj_Abs_thm, inj_Rep_thm) end;

    val newT_iso_inj_thms = map prove_newT_iso_inj_thm
      (new_type_names ~~ newT_iso_axms ~~ newTs ~~
        take (length newTs, rep_set_names));

    (********* isomorphisms between existing types and "unfolded" types *******)

    (*---------------------------------------------------------------------*)
    (* isomorphisms are defined using primrec-combinators:                 *)
    (* generate appropriate functions for instantiating primrec-combinator *)
    (*                                                                     *)
    (*   e.g.  dt_Rep_i = list_rec ... (%h t y. In1 ((Leaf h) $ y))        *)
    (*                                                                     *)
    (* also generate characteristic equations for isomorphisms             *)
    (*                                                                     *)
    (*   e.g.  dt_Rep_i (cons h t) = In1 ((dt_Rep_j h) $ (dt_Rep_i t))     *)
    (*---------------------------------------------------------------------*)

    fun make_iso_def k ks n ((fs, eqns, i), (cname, cargs)) =
      let
        val argTs = map (typ_of_dtyp descr' sorts) cargs;
        val T = nth_elem (k, recTs);
        val rep_name = nth_elem (k, all_rep_names);
        val rep_const = Const (rep_name, T --> Univ_elT);
        val constr = Const (cname, argTs ---> T);

        fun process_arg ks' ((i2, i2', ts, Ts), dt) =
          let val T' = typ_of_dtyp descr' sorts dt
          in (case dt of
              DtRec j => if j mem ks' then
                  (i2 + 1, i2' + 1, ts @ [mk_Free "y" Univ_elT i2'], Ts @ [Univ_elT])
                else
                  (i2 + 1, i2', ts @ [Const (nth_elem (j, all_rep_names),
                    T' --> Univ_elT) $ mk_Free "x" T' i2], Ts)
            | (DtType ("fun", [_, DtRec j])) =>
                let val ([T''], T''') = strip_type T'
                in if j mem ks' then
                    (i2 + 1, i2' + 1, ts @ [Lim $ mk_fun_inj T''
                      (mk_Free "y" (T'' --> Univ_elT) i2')], Ts @ [T'' --> Univ_elT])
                  else
                    (i2 + 1, i2', ts @ [Lim $ mk_fun_inj T''
                      (Const (o_name, [T''' --> Univ_elT, T', T''] ---> Univ_elT) $
                        Const (nth_elem (j, all_rep_names), T''' --> Univ_elT) $
                          mk_Free "x" T' i2)], Ts)
                end
            | _ => (i2 + 1, i2', ts @ [Leaf $ mk_inj T' (mk_Free "x" T' i2)], Ts))
          end;

        val (i2, i2', ts, Ts) = foldl (process_arg ks) ((1, 1, [], []), cargs);
        val xs = map (uncurry (mk_Free "x")) (argTs ~~ (1 upto (i2 - 1)));
        val ys = map (uncurry (mk_Free "y")) (Ts ~~ (1 upto (i2' - 1)));
        val f = list_abs_free (map dest_Free (xs @ ys), mk_univ_inj ts n i);

        val (_, _, ts', _) = foldl (process_arg []) ((1, 1, [], []), cargs);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (rep_const $ list_comb (constr, xs), mk_univ_inj ts' n i))

      in (fs @ [f], eqns @ [eqn], i + 1) end;

    (* define isomorphisms for all mutually recursive datatypes in list ds *)

    fun make_iso_defs (ds, (thy, char_thms)) =
      let
        val ks = map fst ds;
        val (_, (tname, _, _)) = hd ds;
        val {rec_rewrites, rec_names, ...} = the (Symtab.lookup (dt_info, tname));

        fun process_dt ((fs, eqns, isos), (k, (tname, _, constrs))) =
          let
            val (fs', eqns', _) = foldl (make_iso_def k ks (length constrs))
              ((fs, eqns, 1), constrs);
            val iso = (nth_elem (k, recTs), nth_elem (k, all_rep_names))
          in (fs', eqns', isos @ [iso]) end;
        
        val (fs, eqns, isos) = foldl process_dt (([], [], []), ds);
        val fTs = map fastype_of fs;
        val defs = map (fn (rec_name, (T, iso_name)) => ((Sign.base_name iso_name) ^ "_def",
          equals (T --> Univ_elT) $ Const (iso_name, T --> Univ_elT) $
            list_comb (Const (rec_name, fTs @ [T] ---> Univ_elT), fs))) (rec_names ~~ isos);
        val (thy', def_thms) = (PureThy.add_defs_i false o map Thm.no_attributes) defs thy;

        (* prove characteristic equations *)

        val rewrites = def_thms @ (map mk_meta_eq rec_rewrites);
        val char_thms' = map (fn eqn => prove_goalw_cterm rewrites
          (cterm_of (Theory.sign_of thy') eqn) (fn _ => [rtac refl 1])) eqns;

      in (thy', char_thms' @ char_thms) end;

    val (thy5, iso_char_thms) = foldr make_iso_defs
      (tl descr, (add_path flat_names big_name thy4, []));

    (* prove isomorphism properties *)

    fun mk_funs_inv thm =
      let
        val [_, t] = prems_of Funs_inv;
        val [_ $ (_ $ _ $ R)] = Logic.strip_assums_hyp t;
        val _ $ (_ $ (r $ (a $ _)) $ _) = Logic.strip_assums_concl t;
        val [_ $ (_ $ _ $ R')] = prems_of thm;
        val _ $ (_ $ (r' $ (a' $ _)) $ _) = concl_of thm;
        val inv' = cterm_instantiate (map 
          ((pairself (cterm_of (sign_of_thm thm))) o
           (apsnd (map_term_types (incr_tvar 1))))
             [(R, R'), (r, r'), (a, a')]) Funs_inv
      in
        rule_by_tactic (atac 2) (thm RSN (2, inv'))
      end;

    (* prove  inj dt_Rep_i  and  dt_Rep_i x : dt_rep_set_i *)

    fun prove_iso_thms (ds, (inj_thms, elem_thms)) =
      let
        val (_, (tname, _, _)) = hd ds;
        val {induction, ...} = the (Symtab.lookup (dt_info, tname));

        fun mk_ind_concl (i, _) =
          let
            val T = nth_elem (i, recTs);
            val Rep_t = Const (nth_elem (i, all_rep_names), T --> Univ_elT);
            val rep_set_name = nth_elem (i, rep_set_names)
          in (HOLogic.all_const T $ Abs ("y", T, HOLogic.imp $
                HOLogic.mk_eq (Rep_t $ mk_Free "x" T i, Rep_t $ Bound 0) $
                  HOLogic.mk_eq (mk_Free "x" T i, Bound 0)),
              HOLogic.mk_mem (Rep_t $ mk_Free "x" T i, Const (rep_set_name, UnivT)))
          end;

        val (ind_concl1, ind_concl2) = ListPair.unzip (map mk_ind_concl ds);

        val rewrites = map mk_meta_eq iso_char_thms;
        val inj_thms' = flat (map (fn r => [r RS injD, r RS inj_o])
          (map snd newT_iso_inj_thms @ inj_thms));

        val inj_thm = prove_goalw_cterm [] (cterm_of (Theory.sign_of thy5)
          (HOLogic.mk_Trueprop (mk_conj ind_concl1))) (fn _ =>
            [indtac induction 1,
             REPEAT (EVERY
               [rtac allI 1, rtac impI 1,
                exh_tac (exh_thm_of dt_info) 1,
                REPEAT (EVERY
                  [hyp_subst_tac 1,
                   rewrite_goals_tac rewrites,
                   REPEAT (dresolve_tac [In0_inject, In1_inject] 1),
                   (eresolve_tac [In0_not_In1 RS notE, In1_not_In0 RS notE] 1)
                   ORELSE (EVERY
                     [REPEAT (etac Scons_inject 1),
                      REPEAT (dresolve_tac
                        (inj_thms' @ [Leaf_inject, Lim_inject, Inl_inject, Inr_inject]) 1),
                      REPEAT ((EVERY [etac allE 1, dtac mp 1, atac 1]) ORELSE
                              (dtac inj_fun_lemma 1 THEN atac 1)),
                      TRY (hyp_subst_tac 1),
                      rtac refl 1])])])]);

        val inj_thms'' = map (fn r => r RS datatype_injI)
                             (split_conj_thm inj_thm);

        val elem_thm = 
	    prove_goalw_cterm []
	      (cterm_of (Theory.sign_of thy5)
	       (HOLogic.mk_Trueprop (mk_conj ind_concl2)))
	      (fn _ =>
	       [indtac induction 1,
		rewrite_goals_tac (o_def :: rewrites),
		REPEAT (EVERY
			[resolve_tac rep_intrs 1,
			 REPEAT (FIRST [atac 1, etac spec 1,
				 resolve_tac (FunsI :: elem_thms) 1])])]);

      in (inj_thms'' @ inj_thms, elem_thms @ (split_conj_thm elem_thm))
      end;

    val (iso_inj_thms_unfolded, iso_elem_thms) = foldr prove_iso_thms
      (tl descr, ([], map #3 newT_iso_axms));
    val iso_inj_thms = map snd newT_iso_inj_thms @ iso_inj_thms_unfolded;

    (* prove  x : dt_rep_set_i --> x : range dt_Rep_i *)

    fun mk_iso_t (((set_name, iso_name), i), T) =
      let val isoT = T --> Univ_elT
      in HOLogic.imp $ 
        HOLogic.mk_mem (mk_Free "x" Univ_elT i, Const (set_name, UnivT)) $
          (if i < length newTs then Const ("True", HOLogic.boolT)
           else HOLogic.mk_mem (mk_Free "x" Univ_elT i,
             Const ("image", [isoT, HOLogic.mk_setT T] ---> UnivT) $
               Const (iso_name, isoT) $ Const ("UNIV", HOLogic.mk_setT T)))
      end;

    val iso_t = HOLogic.mk_Trueprop (mk_conj (map mk_iso_t
      (rep_set_names ~~ all_rep_names ~~ (0 upto (length descr' - 1)) ~~ recTs)));

    (* all the theorems are proved by one single simultaneous induction *)

    val iso_thms = if length descr = 1 then [] else
      drop (length newTs, split_conj_thm
        (prove_goalw_cterm [] (cterm_of (Theory.sign_of thy5) iso_t) (fn _ =>
           [indtac rep_induct 1,
            REPEAT (rtac TrueI 1),
            REPEAT (EVERY
              [rewrite_goals_tac [mk_meta_eq Collect_mem_eq],
               REPEAT (etac Funs_IntE 1),
               REPEAT (eresolve_tac (rangeE ::
                 map (fn r => r RS Funs_rangeE) iso_inj_thms_unfolded) 1),
               REPEAT (eresolve_tac (map (fn (iso, _, _) => iso RS subst) newT_iso_axms @
                 map (fn (iso, _, _) => mk_funs_inv iso RS subst) newT_iso_axms) 1),
               TRY (hyp_subst_tac 1),
               rtac (sym RS range_eqI) 1,
               resolve_tac iso_char_thms 1])])));

    val Abs_inverse_thms' =
      map #1 newT_iso_axms @
      map2 (fn (r_inj, r) => f_myinv_f OF [r_inj, r RS mp])
        (iso_inj_thms_unfolded, iso_thms);

    val Abs_inverse_thms = map (fn r => r RS subst) (Abs_inverse_thms' @
      map mk_funs_inv Abs_inverse_thms');

    (******************* freeness theorems for constructors *******************)

    val _ = message "Proving freeness of constructors ...";

    (* prove theorem  Rep_i (Constr_j ...) = Inj_j ...  *)
    
    fun prove_constr_rep_thm eqn =
      let
        val inj_thms = map (fn (r, _) => r RS inj_onD) newT_iso_inj_thms;
        val rewrites = o_def :: constr_defs @ (map (mk_meta_eq o #2) newT_iso_axms)
      in prove_goalw_cterm [] (cterm_of (Theory.sign_of thy5) eqn) (fn _ =>
        [resolve_tac inj_thms 1,
         rewrite_goals_tac rewrites,
         rtac refl 1,
         resolve_tac rep_intrs 2,
         REPEAT (resolve_tac (FunsI :: iso_elem_thms) 1)])
      end;

    (*--------------------------------------------------------------*)
    (* constr_rep_thms and rep_congs are used to prove distinctness *)
    (* of constructors.                                             *)
    (*--------------------------------------------------------------*)

    val constr_rep_thms = map (map prove_constr_rep_thm) constr_rep_eqns;

    val dist_rewrites = map (fn (rep_thms, dist_lemma) =>
      dist_lemma::(rep_thms @ [In0_eq, In1_eq, In0_not_In1, In1_not_In0]))
        (constr_rep_thms ~~ dist_lemmas);

    fun prove_distinct_thms (_, []) = []
      | prove_distinct_thms (dist_rewrites', t::_::ts) =
          let
            val dist_thm = prove_goalw_cterm [] (cterm_of (Theory.sign_of thy5) t) (fn _ =>
              [simp_tac (HOL_ss addsimps dist_rewrites') 1])
          in dist_thm::(standard (dist_thm RS not_sym))::
            (prove_distinct_thms (dist_rewrites', ts))
          end;

    val distinct_thms = map prove_distinct_thms (dist_rewrites ~~
      DatatypeProp.make_distincts new_type_names descr sorts thy5);

    val simproc_dists = map (fn ((((_, (_, _, constrs)), rep_thms), congr), dists) =>
      if length constrs < !DatatypeProp.dtK then FewConstrs dists
      else ManyConstrs (congr, HOL_basic_ss addsimps rep_thms)) (hd descr ~~
        constr_rep_thms ~~ rep_congs ~~ distinct_thms);

    (* prove injectivity of constructors *)

    fun prove_constr_inj_thm rep_thms t =
      let val inj_thms = Scons_inject::sum_case_inject::(map make_elim
        ((map (fn r => r RS injD) iso_inj_thms) @
          [In0_inject, In1_inject, Leaf_inject, Inl_inject, Inr_inject, Lim_inject]))
      in prove_goalw_cterm [] (cterm_of (Theory.sign_of thy5) t) (fn _ =>
        [rtac iffI 1,
         REPEAT (etac conjE 2), hyp_subst_tac 2, rtac refl 2,
         dresolve_tac rep_congs 1, dtac box_equals 1,
         REPEAT (resolve_tac rep_thms 1), rewtac o_def,
         REPEAT (eresolve_tac inj_thms 1),
         REPEAT (ares_tac [conjI] 1 ORELSE (EVERY [rtac ext 1, dtac fun_cong 1,
                  eresolve_tac inj_thms 1, atac 1]))])
      end;

    val constr_inject = map (fn (ts, thms) => map (prove_constr_inj_thm thms) ts)
      ((DatatypeProp.make_injs descr sorts) ~~ constr_rep_thms);

    val (thy6, (constr_inject', distinct_thms'))= thy5 |> parent_path flat_names |>
      store_thmss "inject" new_type_names constr_inject |>>>
      store_thmss "distinct" new_type_names distinct_thms;

    (*************************** induction theorem ****************************)

    val _ = message "Proving induction rule for datatypes ...";

    val Rep_inverse_thms = (map (fn (_, iso, _) => iso RS subst) newT_iso_axms) @
      (map (fn r => r RS myinv_f_f RS subst) iso_inj_thms_unfolded);
    val Rep_inverse_thms' = map (fn r => r RS myinv_f_f) iso_inj_thms_unfolded;

    fun mk_indrule_lemma ((prems, concls), ((i, _), T)) =
      let
        val Rep_t = Const (nth_elem (i, all_rep_names), T --> Univ_elT) $
          mk_Free "x" T i;

        val Abs_t = if i < length newTs then
            Const (Sign.intern_const (Theory.sign_of thy6)
              ("Abs_" ^ (nth_elem (i, new_type_names))), Univ_elT --> T)
          else Const ("Inductive.myinv", [T --> Univ_elT, Univ_elT] ---> T) $
            Const (nth_elem (i, all_rep_names), T --> Univ_elT)

      in (prems @ [HOLogic.imp $ HOLogic.mk_mem (Rep_t,
            Const (nth_elem (i, rep_set_names), UnivT)) $
              (mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ (Abs_t $ Rep_t))],
          concls @ [mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ mk_Free "x" T i])
      end;

    val (indrule_lemma_prems, indrule_lemma_concls) =
      foldl mk_indrule_lemma (([], []), (descr' ~~ recTs));

    val cert = cterm_of (Theory.sign_of thy6);

    val indrule_lemma = prove_goalw_cterm [] (cert
      (Logic.mk_implies
        (HOLogic.mk_Trueprop (mk_conj indrule_lemma_prems),
         HOLogic.mk_Trueprop (mk_conj indrule_lemma_concls)))) (fn prems =>
           [cut_facts_tac prems 1, REPEAT (etac conjE 1),
            REPEAT (EVERY
              [TRY (rtac conjI 1), resolve_tac Rep_inverse_thms 1,
               etac mp 1, resolve_tac iso_elem_thms 1])]);

    val Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (concl_of indrule_lemma)));
    val frees = if length Ps = 1 then [Free ("P", snd (dest_Var (hd Ps)))] else
      map (Free o apfst fst o dest_Var) Ps;
    val indrule_lemma' = cterm_instantiate (map cert Ps ~~ map cert frees) indrule_lemma;

    val dt_induct = prove_goalw_cterm [InductivePackage.inductive_forall_def] (cert
      (DatatypeProp.make_ind descr sorts)) (fn prems =>
        [rtac indrule_lemma' 1, indtac rep_induct 1,
         EVERY (map (fn (prem, r) => (EVERY
           [REPEAT (eresolve_tac (Funs_IntE::Abs_inverse_thms) 1),
            simp_tac (HOL_basic_ss addsimps ((symmetric r)::Rep_inverse_thms')) 1,
            DEPTH_SOLVE_1 (ares_tac [prem] 1 ORELSE (EVERY [rewtac o_def,
              rtac allI 1, dtac FunsD 1, etac CollectD 1]))]))
                (prems ~~ (constr_defs @ (map mk_meta_eq iso_char_thms))))]);

    val (thy7, [dt_induct']) = thy6 |>
      Theory.add_path big_name |>
      PureThy.add_thms [(("induct", dt_induct),
        [Drule.rule_attribute (K InductivePackage.rulify), case_names_induct])] |>>
      Theory.parent_path;

  in (thy7, constr_inject', distinct_thms', dist_rewrites, simproc_dists, dt_induct')
  end;

end;
