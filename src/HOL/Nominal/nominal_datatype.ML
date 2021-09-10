(*  Title:      HOL/Nominal/nominal_datatype.ML
    Author:     Stefan Berghofer and Christian Urban, TU Muenchen

Nominal datatype package for Isabelle/HOL.
*)

signature NOMINAL_DATATYPE =
sig
  val nominal_datatype : Old_Datatype_Aux.config -> Old_Datatype.spec list -> theory -> theory
  val nominal_datatype_cmd : Old_Datatype_Aux.config -> Old_Datatype.spec_cmd list -> theory ->
    theory
  type descr
  type nominal_datatype_info
  val get_nominal_datatypes : theory -> nominal_datatype_info Symtab.table
  val get_nominal_datatype : theory -> string -> nominal_datatype_info option
  val mk_perm: typ list -> term -> term -> term
  val perm_of_pair: term * term -> term
  val mk_not_sym: thm list -> thm list
  val perm_simproc: simproc
  val fresh_const: typ -> typ -> term
  val fresh_star_const: typ -> typ -> term
end

structure NominalDatatype : NOMINAL_DATATYPE =
struct

val finite_emptyI = @{thm finite.emptyI};
val finite_Diff = @{thm finite_Diff};
val finite_Un = @{thm finite_Un};
val Un_iff = @{thm Un_iff};
val Un_assoc = @{thm Un_assoc};
val Collect_disj_eq = @{thm Collect_disj_eq};
val Collect_False_empty = @{thm empty_def [THEN sym, THEN eq_reflection]};
val empty_iff = @{thm empty_iff};

open NominalAtoms;


(* theory data *)

type descr =
  (int * (string * Old_Datatype_Aux.dtyp list *
      (string * (Old_Datatype_Aux.dtyp list * Old_Datatype_Aux.dtyp) list) list)) list;

type nominal_datatype_info =
  {index : int,
   descr : descr,
   rec_names : string list,
   rec_rewrites : thm list,
   induction : thm,
   distinct : thm list,
   inject : thm list};

structure NominalDatatypesData = Theory_Data
(
  type T = nominal_datatype_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
);

val get_nominal_datatypes = NominalDatatypesData.get;
val put_nominal_datatypes = NominalDatatypesData.put;
val map_nominal_datatypes = NominalDatatypesData.map;
val get_nominal_datatype = Symtab.lookup o get_nominal_datatypes;


(**** make datatype info ****)

fun make_dt_info descr induct reccomb_names rec_thms
    (i, (((_, (tname, _, _)), distinct), inject)) =
  (tname,
   {index = i,
    descr = descr,
    rec_names = reccomb_names,
    rec_rewrites = rec_thms,
    induction = induct,
    distinct = distinct,
    inject = inject});

(*******************************)

val (_ $ (_ $ (_ $ (distinct_f $ _) $ _))) = hd (Thm.prems_of Old_Datatype.distinct_lemma);


(** simplification procedure for sorting permutations **)

val dj_cp = @{thm dj_cp};

fun dest_permT (Type (\<^type_name>\<open>fun\<close>,
    [Type (\<^type_name>\<open>list\<close>, [Type (\<^type_name>\<open>Product_Type.prod\<close>, [T, _])]),
      Type (\<^type_name>\<open>fun\<close>, [_, U])])) = (T, U);

fun permTs_of (Const (\<^const_name>\<open>Nominal.perm\<close>, T) $ t $ u) = fst (dest_permT T) :: permTs_of u
  | permTs_of _ = [];

fun perm_simproc' ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Nominal.perm\<close>, T) $ t $ (u as Const (\<^const_name>\<open>Nominal.perm\<close>, U) $ r $ s) =>
      let
        val thy = Proof_Context.theory_of ctxt;
        val (aT as Type (a, []), S) = dest_permT T;
        val (bT as Type (b, []), _) = dest_permT U;
      in
        if member (op =) (permTs_of u) aT andalso aT <> bT then
          let
            val cp = cp_inst_of thy a b;
            val dj = dj_thm_of thy b a;
            val dj_cp' = [cp, dj] MRS dj_cp;
            val cert = SOME o Thm.cterm_of ctxt
          in
            SOME (mk_meta_eq (Thm.instantiate' [SOME (Thm.ctyp_of ctxt S)]
              [cert t, cert r, cert s] dj_cp'))
          end
        else NONE
      end
  | _ => NONE);

val perm_simproc =
  Simplifier.make_simproc \<^context> "perm_simp"
   {lhss = [\<^term>\<open>pi1 \<bullet> (pi2 \<bullet> x)\<close>], proc = K perm_simproc'};

fun projections ctxt rule =
  Project_Rule.projections ctxt rule
  |> map (Drule.export_without_context #> Rule_Cases.save rule);

val supp_prod = @{thm supp_prod};
val fresh_prod = @{thm fresh_prod};
val supports_fresh = @{thm supports_fresh};
val supports_def = Simpdata.mk_eq @{thm Nominal.supports_def};
val fresh_def = Simpdata.mk_eq @{thm fresh_def};
val supp_def = Simpdata.mk_eq @{thm supp_def};
val rev_simps = @{thms rev.simps};
val app_simps = @{thms append.simps};
val at_fin_set_supp = @{thm at_fin_set_supp};
val at_fin_set_fresh = @{thm at_fin_set_fresh};
val abs_fun_eq1 = @{thm abs_fun_eq1};

fun collect_simp ctxt = rewrite_rule ctxt [mk_meta_eq mem_Collect_eq];

fun mk_perm Ts t u =
  let
    val T = fastype_of1 (Ts, t);
    val U = fastype_of1 (Ts, u)
  in Const (\<^const_name>\<open>Nominal.perm\<close>, T --> U --> U) $ t $ u end;

fun perm_of_pair (x, y) =
  let
    val T = fastype_of x;
    val pT = mk_permT T
  in Const (\<^const_name>\<open>Cons\<close>, HOLogic.mk_prodT (T, T) --> pT --> pT) $
    HOLogic.mk_prod (x, y) $ Const (\<^const_name>\<open>Nil\<close>, pT)
  end;

fun mk_not_sym ths = maps (fn th =>
  (case Thm.prop_of th of
    _ $ (Const (\<^const_name>\<open>Not\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _)) =>
    [th, th RS not_sym]
  | _ => [th])) ths;

fun fresh_const T U = Const (\<^const_name>\<open>Nominal.fresh\<close>, T --> U --> HOLogic.boolT);
fun fresh_star_const T U =
  Const (\<^const_name>\<open>Nominal.fresh_star\<close>, HOLogic.mk_setT T --> U --> HOLogic.boolT);

fun gen_nominal_datatype prep_specs (config: Old_Datatype_Aux.config) dts thy =
  let
    val new_type_names = map (fn ((tname, _, _), _) => Binding.name_of tname) dts;

    val (dts', _) = prep_specs dts thy;

    val atoms = atoms_of thy;

    val tyvars = map (fn ((_, tvs, _), _) => tvs) dts';
    val sorts = flat tyvars;

    fun inter_sort thy S S' = Sign.inter_sort thy (S, S');
    fun augment_sort_typ thy S =
      let val S = Sign.minimize_sort thy (Sign.certify_sort thy S)
      in map_type_tfree (fn (s, S') => TFree (s,
        if member (op = o apsnd fst) sorts s then inter_sort thy S S' else S'))
      end;
    fun augment_sort thy S = map_types (augment_sort_typ thy S);

    val types_syntax = map (fn ((tname, tvs, mx), constrs) => (tname, mx)) dts';
    val constr_syntax = map (fn (_, constrs) =>
      map (fn (cname, cargs, mx) => (cname, mx)) constrs) dts';

    val ps = map (fn ((n, _, _), _) =>
      (Sign.full_name thy n, Sign.full_name thy (Binding.suffix_name "_Rep" n))) dts;
    val rps = map Library.swap ps;

    fun replace_types (Type (\<^type_name>\<open>ABS\<close>, [T, U])) =
          Type (\<^type_name>\<open>fun\<close>, [T, Type (\<^type_name>\<open>noption\<close>, [replace_types U])])
      | replace_types (Type (s, Ts)) =
          Type (the_default s (AList.lookup op = ps s), map replace_types Ts)
      | replace_types T = T;

    val dts'' = map (fn ((tname, tvs, mx), constrs) =>
      ((Binding.suffix_name "_Rep" tname, tvs, NoSyn),
        map (fn (cname, cargs, mx) => (Binding.suffix_name "_Rep" cname,
          map replace_types cargs, NoSyn)) constrs)) dts';

    val new_type_names' = map (fn n => n ^ "_Rep") new_type_names;

    val (full_new_type_names',thy1) = BNF_LFP_Compat.add_datatype [BNF_LFP_Compat.Kill_Type_Args] dts'' thy;

    val {descr, induct, ...} = BNF_LFP_Compat.the_info thy1 [] (hd full_new_type_names');
    fun nth_dtyp i = Old_Datatype_Aux.typ_of_dtyp descr (Old_Datatype_Aux.DtRec i);

    val big_name = space_implode "_" new_type_names;


    (**** define permutation functions ****)

    val permT = mk_permT (TFree ("'x", \<^sort>\<open>type\<close>));
    val pi = Free ("pi", permT);
    val perm_types = map (fn (i, _) =>
      let val T = nth_dtyp i
      in permT --> T --> T end) descr;
    val perm_names' = Old_Datatype_Prop.indexify_names (map (fn (i, _) =>
      "perm_" ^ Old_Datatype_Aux.name_of_typ (nth_dtyp i)) descr);
    val perm_names = replicate (length new_type_names) \<^const_name>\<open>Nominal.perm\<close> @
      map (Sign.full_bname thy1) (List.drop (perm_names', length new_type_names));
    val perm_names_types = perm_names ~~ perm_types;
    val perm_names_types' = perm_names' ~~ perm_types;

    val perm_eqs = maps (fn (i, (_, _, constrs)) =>
      let val T = nth_dtyp i
      in map (fn (cname, dts) =>
        let
          val Ts = map (Old_Datatype_Aux.typ_of_dtyp descr) dts;
          val names = Name.variant_list ["pi"] (Old_Datatype_Prop.make_tnames Ts);
          val args = map Free (names ~~ Ts);
          val c = Const (cname, Ts ---> T);
          fun perm_arg (dt, x) =
            let val T = type_of x
            in if Old_Datatype_Aux.is_rec_type dt then
                let val Us = binder_types T
                in
                  fold_rev (Term.abs o pair "x") Us
                    (Free (nth perm_names_types' (Old_Datatype_Aux.body_index dt)) $ pi $
                      list_comb (x, map (fn (i, U) =>
                        Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> U --> U) $
                          (Const (\<^const_name>\<open>rev\<close>, permT --> permT) $ pi) $
                          Bound i) ((length Us - 1 downto 0) ~~ Us)))
                end
              else Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> T --> T) $ pi $ x
            end;
        in
          ((Binding.empty_atts, HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Free (nth perm_names_types' i) $
               Free ("pi", mk_permT (TFree ("'x", \<^sort>\<open>type\<close>))) $
               list_comb (c, args),
             list_comb (c, map perm_arg (dts ~~ args))))), [], [])
        end) constrs
      end) descr;

    val (perm_simps, thy2) =
      BNF_LFP_Compat.primrec_overloaded
        (map (fn (s, sT) => (s, sT, false))
           (List.take (perm_names' ~~ perm_names_types, length new_type_names)))
        (map (fn s => (Binding.name s, NONE, NoSyn)) perm_names') perm_eqs thy1;

    (**** prove that permutation functions introduced by unfolding are ****)
    (**** equivalent to already existing permutation functions         ****)

    val _ = warning ("length descr: " ^ string_of_int (length descr));
    val _ = warning ("length new_type_names: " ^ string_of_int (length new_type_names));

    val perm_indnames = Old_Datatype_Prop.make_tnames (map body_type perm_types);
    val perm_fun_def = Simpdata.mk_eq @{thm perm_fun_def};

    val unfolded_perm_eq_thms =
      if length descr = length new_type_names then []
      else map Drule.export_without_context (List.drop (Old_Datatype_Aux.split_conj_thm
        (Goal.prove_global_future thy2 [] []
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
            (map (fn (c as (s, T), x) =>
               let val [T1, T2] = binder_types T
               in HOLogic.mk_eq (Const c $ pi $ Free (x, T2),
                 Const (\<^const_name>\<open>Nominal.perm\<close>, T) $ pi $ Free (x, T2))
               end)
             (perm_names_types ~~ perm_indnames))))
          (fn {context = ctxt, ...} =>
            EVERY [Old_Datatype_Aux.ind_tac ctxt induct perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (ctxt addsimps [perm_fun_def]))])),
        length new_type_names));

    (**** prove [] \<bullet> t = t ****)

    val _ = warning "perm_empty_thms";

    val perm_empty_thms = maps (fn a =>
      let val permT = mk_permT (Type (a, []))
      in map Drule.export_without_context (List.take (Old_Datatype_Aux.split_conj_thm
        (Goal.prove_global_future thy2 [] []
          (augment_sort thy2 [pt_class_of thy2 a]
            (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
              (map (fn ((s, T), x) => HOLogic.mk_eq
                  (Const (s, permT --> T --> T) $
                     Const (\<^const_name>\<open>Nil\<close>, permT) $ Free (x, T),
                   Free (x, T)))
               (perm_names ~~
                map body_type perm_types ~~ perm_indnames)))))
          (fn {context = ctxt, ...} =>
            EVERY [Old_Datatype_Aux.ind_tac ctxt induct perm_indnames 1,
              ALLGOALS (asm_full_simp_tac ctxt)])),
        length new_type_names))
      end)
      atoms;

    (**** prove (pi1 @ pi2) \<bullet> t = pi1 \<bullet> (pi2 \<bullet> t) ****)

    val _ = warning "perm_append_thms";

    (*FIXME: these should be looked up statically*)
    val at_pt_inst = Global_Theory.get_thm thy2 "at_pt_inst";
    val pt2 = Global_Theory.get_thm thy2 "pt2";

    val perm_append_thms = maps (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        val pt_inst = pt_inst_of thy2 a;
        val pt2' = pt_inst RS pt2;
        val pt2_ax = Global_Theory.get_thm thy2 (Long_Name.map_base_name (fn s => "pt_" ^ s ^ "2") a);
      in List.take (map Drule.export_without_context (Old_Datatype_Aux.split_conj_thm
        (Goal.prove_global_future thy2 [] []
           (augment_sort thy2 [pt_class_of thy2 a]
             (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ (Const (\<^const_name>\<open>append\<close>, permT --> permT --> permT) $
                         pi1 $ pi2) $ Free (x, T),
                       perm $ pi1 $ (perm $ pi2 $ Free (x, T)))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames)))))
           (fn {context = ctxt, ...} =>
             EVERY [Old_Datatype_Aux.ind_tac ctxt induct perm_indnames 1,
               ALLGOALS (asm_full_simp_tac (ctxt addsimps [pt2', pt2_ax]))]))),
         length new_type_names)
      end) atoms;

    (**** prove pi1 ~ pi2 ==> pi1 \<bullet> t = pi2 \<bullet> t ****)

    val _ = warning "perm_eq_thms";

    val pt3 = Global_Theory.get_thm thy2 "pt3";
    val pt3_rev = Global_Theory.get_thm thy2 "pt3_rev";

    val perm_eq_thms = maps (fn a =>
      let
        val permT = mk_permT (Type (a, []));
        val pi1 = Free ("pi1", permT);
        val pi2 = Free ("pi2", permT);
        val at_inst = at_inst_of thy2 a;
        val pt_inst = pt_inst_of thy2 a;
        val pt3' = pt_inst RS pt3;
        val pt3_rev' = at_inst RS (pt_inst RS pt3_rev);
        val pt3_ax = Global_Theory.get_thm thy2 (Long_Name.map_base_name (fn s => "pt_" ^ s ^ "3") a);
      in List.take (map Drule.export_without_context (Old_Datatype_Aux.split_conj_thm
        (Goal.prove_global_future thy2 [] []
          (augment_sort thy2 [pt_class_of thy2 a] (Logic.mk_implies
             (HOLogic.mk_Trueprop (Const (\<^const_name>\<open>Nominal.prm_eq\<close>,
                permT --> permT --> HOLogic.boolT) $ pi1 $ pi2),
              HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn ((s, T), x) =>
                    let val perm = Const (s, permT --> T --> T)
                    in HOLogic.mk_eq
                      (perm $ pi1 $ Free (x, T),
                       perm $ pi2 $ Free (x, T))
                    end)
                  (perm_names ~~
                   map body_type perm_types ~~ perm_indnames))))))
           (fn {context = ctxt, ...} =>
             EVERY [Old_Datatype_Aux.ind_tac ctxt induct perm_indnames 1,
               ALLGOALS (asm_full_simp_tac (ctxt addsimps [pt3', pt3_rev', pt3_ax]))]))),
         length new_type_names)
      end) atoms;

    (**** prove pi1 \<bullet> (pi2 \<bullet> t) = (pi1 \<bullet> pi2) \<bullet> (pi1 \<bullet> t) ****)

    val cp1 = Global_Theory.get_thm thy2 "cp1";
    val dj_cp = Global_Theory.get_thm thy2 "dj_cp";
    val pt_perm_compose = Global_Theory.get_thm thy2 "pt_perm_compose";
    val pt_perm_compose_rev = Global_Theory.get_thm thy2 "pt_perm_compose_rev";
    val dj_perm_perm_forget = Global_Theory.get_thm thy2 "dj_perm_perm_forget";

    fun composition_instance name1 name2 thy =
      let
        val cp_class = cp_class_of thy name1 name2;
        val pt_class =
          if name1 = name2 then [pt_class_of thy name1]
          else [];
        val permT1 = mk_permT (Type (name1, []));
        val permT2 = mk_permT (Type (name2, []));
        val Ts = map body_type perm_types;
        val cp_inst = cp_inst_of thy name1 name2;
        fun simps ctxt = ctxt addsimps (perm_fun_def ::
          (if name1 <> name2 then
             let val dj = dj_thm_of thy name2 name1
             in [dj RS (cp_inst RS dj_cp), dj RS dj_perm_perm_forget] end
           else
             let
               val at_inst = at_inst_of thy name1;
               val pt_inst = pt_inst_of thy name1;
             in
               [cp_inst RS cp1 RS sym,
                at_inst RS (pt_inst RS pt_perm_compose) RS sym,
                at_inst RS (pt_inst RS pt_perm_compose_rev) RS sym]
            end))
        val sort = Sign.minimize_sort thy (Sign.certify_sort thy (cp_class :: pt_class));
        val thms = Old_Datatype_Aux.split_conj_thm (Goal.prove_global_future thy [] []
          (augment_sort thy sort
            (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
              (map (fn ((s, T), x) =>
                  let
                    val pi1 = Free ("pi1", permT1);
                    val pi2 = Free ("pi2", permT2);
                    val perm1 = Const (s, permT1 --> T --> T);
                    val perm2 = Const (s, permT2 --> T --> T);
                    val perm3 = Const (\<^const_name>\<open>Nominal.perm\<close>, permT1 --> permT2 --> permT2)
                  in HOLogic.mk_eq
                    (perm1 $ pi1 $ (perm2 $ pi2 $ Free (x, T)),
                     perm2 $ (perm3 $ pi1 $ pi2) $ (perm1 $ pi1 $ Free (x, T)))
                  end)
                (perm_names ~~ Ts ~~ perm_indnames)))))
          (fn {context = ctxt, ...} =>
            EVERY [Old_Datatype_Aux.ind_tac ctxt induct perm_indnames 1,
              ALLGOALS (asm_full_simp_tac (simps ctxt))]))
      in
        fold (fn (s, tvs) => fn thy => Axclass.prove_arity
            (s, map (inter_sort thy sort o snd) tvs, [cp_class])
            (fn ctxt' =>
              Class.intro_classes_tac ctxt' [] THEN ALLGOALS (resolve_tac ctxt' thms)) thy)
          (full_new_type_names' ~~ tyvars) thy
      end;

    val (perm_thmss,thy3) = thy2 |>
      fold (fn name1 => fold (composition_instance name1) atoms) atoms |>
      fold (fn atom => fn thy =>
        let val pt_name = pt_class_of thy atom
        in
          fold (fn (s, tvs) => fn thy => Axclass.prove_arity
              (s, map (inter_sort thy [pt_name] o snd) tvs, [pt_name])
              (fn ctxt => EVERY
                [Class.intro_classes_tac ctxt [],
                 resolve_tac ctxt perm_empty_thms 1,
                 resolve_tac ctxt perm_append_thms 1,
                 resolve_tac ctxt perm_eq_thms 1, assume_tac ctxt 1]) thy)
            (full_new_type_names' ~~ tyvars) thy
        end) atoms |>
      Global_Theory.add_thmss
        [((Binding.name (space_implode "_" new_type_names ^ "_unfolded_perm_eq"),
          unfolded_perm_eq_thms), [Simplifier.simp_add]),
         ((Binding.name (space_implode "_" new_type_names ^ "_perm_empty"),
          perm_empty_thms), [Simplifier.simp_add]),
         ((Binding.name (space_implode "_" new_type_names ^ "_perm_append"),
          perm_append_thms), [Simplifier.simp_add]),
         ((Binding.name (space_implode "_" new_type_names ^ "_perm_eq"),
          perm_eq_thms), [Simplifier.simp_add])];

    (**** Define representing sets ****)

    val _ = warning "representing sets";

    val rep_set_names =
      Old_Datatype_Prop.indexify_names
        (map (fn (i, _) => Old_Datatype_Aux.name_of_typ (nth_dtyp i) ^ "_set") descr);
    val big_rep_name =
      space_implode "_" (Old_Datatype_Prop.indexify_names (map_filter
        (fn (i, (\<^type_name>\<open>noption\<close>, _, _)) => NONE
          | (i, _) => SOME (Old_Datatype_Aux.name_of_typ (nth_dtyp i))) descr)) ^ "_set";
    val _ = warning ("big_rep_name: " ^ big_rep_name);

    fun strip_option (dtf as Old_Datatype_Aux.DtType ("fun", [dt, Old_Datatype_Aux.DtRec i])) =
          (case AList.lookup op = descr i of
             SOME (\<^type_name>\<open>noption\<close>, _, [(_, [dt']), _]) =>
               apfst (cons dt) (strip_option dt')
           | _ => ([], dtf))
      | strip_option (Old_Datatype_Aux.DtType ("fun",
            [dt, Old_Datatype_Aux.DtType (\<^type_name>\<open>noption\<close>, [dt'])])) =
          apfst (cons dt) (strip_option dt')
      | strip_option dt = ([], dt);

    val dt_atomTs = distinct op = (map (Old_Datatype_Aux.typ_of_dtyp descr)
      (maps (fn (_, (_, _, cs)) => maps (maps (fst o strip_option) o snd) cs) descr));
    val dt_atoms = map (fst o dest_Type) dt_atomTs;

    fun make_intr s T (cname, cargs) =
      let
        fun mk_prem dt (j, j', prems, ts) =
          let
            val (dts, dt') = strip_option dt;
            val (dts', dt'') = Old_Datatype_Aux.strip_dtyp dt';
            val Ts = map (Old_Datatype_Aux.typ_of_dtyp descr) dts;
            val Us = map (Old_Datatype_Aux.typ_of_dtyp descr) dts';
            val T = Old_Datatype_Aux.typ_of_dtyp descr dt'';
            val free = Old_Datatype_Aux.mk_Free "x" (Us ---> T) j;
            val free' = Old_Datatype_Aux.app_bnds free (length Us);
            fun mk_abs_fun T (i, t) =
              let val U = fastype_of t
              in (i + 1, Const (\<^const_name>\<open>Nominal.abs_fun\<close>, [T, U, T] --->
                Type (\<^type_name>\<open>noption\<close>, [U])) $ Old_Datatype_Aux.mk_Free "y" T i $ t)
              end
          in (j + 1, j' + length Ts,
            case dt'' of
                Old_Datatype_Aux.DtRec k => Logic.list_all (map (pair "x") Us,
                  HOLogic.mk_Trueprop (Free (nth rep_set_names k,
                    T --> HOLogic.boolT) $ free')) :: prems
              | _ => prems,
            snd (fold_rev mk_abs_fun Ts (j', free)) :: ts)
          end;

        val (_, _, prems, ts) = fold_rev mk_prem cargs (1, 1, [], []);
        val concl = HOLogic.mk_Trueprop (Free (s, T --> HOLogic.boolT) $
          list_comb (Const (cname, map fastype_of ts ---> T), ts))
      in Logic.list_implies (prems, concl)
      end;

    val (intr_ts, (rep_set_names', recTs')) =
      apfst flat (apsnd ListPair.unzip (ListPair.unzip (map_filter
        (fn ((_, (\<^type_name>\<open>noption\<close>, _, _)), _) => NONE
          | ((i, (_, _, constrs)), rep_set_name) =>
              let val T = nth_dtyp i
              in SOME (map (make_intr rep_set_name T) constrs,
                (rep_set_name, T))
              end)
                (descr ~~ rep_set_names))));
    val rep_set_names'' = map (Sign.full_bname thy3) rep_set_names';

    val ({raw_induct = rep_induct, intrs = rep_intrs, ...}, thy4) =
      thy3
      |> Sign.concealed
      |> Named_Target.theory_map_result Inductive.transform_result
         (Inductive.add_inductive
          {quiet_mode = false, verbose = false, alt_name = Binding.name big_rep_name,
           coind = false, no_elim = true, no_ind = false, skip_mono = true}
          (map (fn (s, T) => ((Binding.name s, T --> HOLogic.boolT), NoSyn))
             (rep_set_names' ~~ recTs'))
          [] (map (fn x => (Binding.empty_atts, x)) intr_ts) [])
      ||> Sign.restore_naming thy3;

    (**** Prove that representing set is closed under permutation ****)

    val _ = warning "proving closure under permutation...";

    val abs_perm = Global_Theory.get_thms thy4 "abs_perm";

    val perm_indnames' = map_filter
      (fn (x, (_, (\<^type_name>\<open>noption\<close>, _, _))) => NONE | (x, _) => SOME x)
      (perm_indnames ~~ descr);

    fun mk_perm_closed name = map (fn th => Drule.export_without_context (th RS mp))
      (List.take (Old_Datatype_Aux.split_conj_thm (Goal.prove_global_future thy4 [] []
        (augment_sort thy4
          (pt_class_of thy4 name :: map (cp_class_of thy4 name) (remove (op =) name dt_atoms))
          (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map
            (fn ((s, T), x) =>
               let
                 val S = Const (s, T --> HOLogic.boolT);
                 val permT = mk_permT (Type (name, []))
               in HOLogic.mk_imp (S $ Free (x, T),
                 S $ (Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> T --> T) $
                   Free ("pi", permT) $ Free (x, T)))
               end) (rep_set_names'' ~~ recTs' ~~ perm_indnames')))))
        (fn {context = ctxt, ...} => EVERY
           [Old_Datatype_Aux.ind_tac ctxt rep_induct [] 1,
            ALLGOALS (simp_tac (ctxt addsimps
              (Thm.symmetric perm_fun_def :: abs_perm))),
            ALLGOALS (resolve_tac ctxt rep_intrs THEN_ALL_NEW assume_tac ctxt)])),
        length new_type_names));

    val perm_closed_thmss = map mk_perm_closed atoms;

    (**** typedef ****)

    val _ = warning "defining type...";

    val (typedefs, thy6) =
      thy4
      |> fold_map (fn (((name, mx), tvs), (cname, U)) => fn thy =>
          Named_Target.theory_map_result (apsnd o Typedef.transform_info)
          (Typedef.add_typedef {overloaded = false}
            (name, map (fn (v, _) => (v, dummyS)) tvs, mx)  (* FIXME keep constraints!? *)
            (Const (\<^const_name>\<open>Collect\<close>, (U --> HOLogic.boolT) --> HOLogic.mk_setT U) $
               Const (cname, U --> HOLogic.boolT)) NONE
            (fn ctxt =>
              resolve_tac ctxt [exI] 1 THEN
              resolve_tac ctxt [CollectI] 1 THEN
              QUIET_BREADTH_FIRST (has_fewer_prems 1)
              (resolve_tac ctxt rep_intrs 1))) thy |> (fn ((_, r), thy) =>
        let
          val permT = mk_permT
            (TFree (singleton (Name.variant_list (map fst tvs)) "'a", \<^sort>\<open>type\<close>));
          val pi = Free ("pi", permT);
          val T = Type (Sign.full_name thy name, map TFree tvs);
        in apfst (pair r o hd)
          (Global_Theory.add_defs_unchecked true
            [((Binding.map_name (fn n => "prm_" ^ n ^ "_def") name, Logic.mk_equals
              (Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> T --> T) $ pi $ Free ("x", T),
               Const (Sign.intern_const thy ("Abs_" ^ Binding.name_of name), U --> T) $
                 (Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> U --> U) $ pi $
                   (Const (Sign.intern_const thy ("Rep_" ^ Binding.name_of name), T --> U) $
                     Free ("x", T))))), [])] thy)
        end))
        (types_syntax ~~ tyvars ~~ List.take (rep_set_names'' ~~ recTs', length new_type_names));

    val ctxt6 = Proof_Context.init_global thy6;

    val perm_defs = map snd typedefs;
    val Abs_inverse_thms = map (collect_simp ctxt6 o #Abs_inverse o snd o fst) typedefs;
    val Rep_inverse_thms = map (#Rep_inverse o snd o fst) typedefs;
    val Rep_thms = map (collect_simp ctxt6 o #Rep o snd o fst) typedefs;


    (** prove that new types are in class pt_<name> **)

    val _ = warning "prove that new types are in class pt_<name> ...";

    fun pt_instance (atom, perm_closed_thms) =
      fold (fn ((((((Abs_inverse, Rep_inverse), Rep),
        perm_def), name), tvs), perm_closed) => fn thy =>
          let
            val pt_class = pt_class_of thy atom;
            val sort = Sign.minimize_sort thy (Sign.certify_sort thy
              (pt_class :: map (cp_class_of thy atom) (remove (op =) atom dt_atoms)))
          in Axclass.prove_arity
            (Sign.intern_type thy name,
              map (inter_sort thy sort o snd) tvs, [pt_class])
            (fn ctxt => EVERY [Class.intro_classes_tac ctxt [],
              rewrite_goals_tac ctxt [perm_def],
              asm_full_simp_tac (ctxt addsimps [Rep_inverse]) 1,
              asm_full_simp_tac (ctxt addsimps
                [Rep RS perm_closed RS Abs_inverse]) 1,
              asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [Global_Theory.get_thm thy
                ("pt_" ^ Long_Name.base_name atom ^ "3")]) 1]) thy
          end)
        (Abs_inverse_thms ~~ Rep_inverse_thms ~~ Rep_thms ~~ perm_defs ~~
           new_type_names ~~ tyvars ~~ perm_closed_thms);


    (** prove that new types are in class cp_<name1>_<name2> **)

    val _ = warning "prove that new types are in class cp_<name1>_<name2> ...";

    fun cp_instance (atom1, perm_closed_thms1) (atom2, perm_closed_thms2) thy =
      let
        val cp_class = cp_class_of thy atom1 atom2;
        val sort = Sign.minimize_sort thy (Sign.certify_sort thy
          (pt_class_of thy atom1 :: map (cp_class_of thy atom1) (remove (op =) atom1 dt_atoms) @
           (if atom1 = atom2 then [cp_class_of thy atom1 atom1] else
            pt_class_of thy atom2 :: map (cp_class_of thy atom2) (remove (op =) atom2 dt_atoms))));
        val cp1' = cp_inst_of thy atom1 atom2 RS cp1
      in fold (fn ((((((Abs_inverse, Rep),
        perm_def), name), tvs), perm_closed1), perm_closed2) => fn thy =>
          Axclass.prove_arity
            (Sign.intern_type thy name,
              map (inter_sort thy sort o snd) tvs, [cp_class])
            (fn ctxt => EVERY [Class.intro_classes_tac ctxt [],
              rewrite_goals_tac ctxt [perm_def],
              asm_full_simp_tac (ctxt addsimps
                ((Rep RS perm_closed1 RS Abs_inverse) ::
                 (if atom1 = atom2 then []
                  else [Rep RS perm_closed2 RS Abs_inverse]))) 1,
              cong_tac ctxt 1,
              resolve_tac ctxt [refl] 1,
              resolve_tac ctxt [cp1'] 1]) thy)
        (Abs_inverse_thms ~~ Rep_thms ~~ perm_defs ~~ new_type_names ~~
           tyvars ~~ perm_closed_thms1 ~~ perm_closed_thms2) thy
      end;

    val thy7 = fold (fn x => fn thy => thy |>
      pt_instance x |>
      fold (cp_instance x) (atoms ~~ perm_closed_thmss))
        (atoms ~~ perm_closed_thmss) thy6;

    (**** constructors ****)

    fun mk_abs_fun x t =
      let
        val T = fastype_of x;
        val U = fastype_of t
      in
        Const (\<^const_name>\<open>Nominal.abs_fun\<close>, T --> U --> T -->
          Type (\<^type_name>\<open>noption\<close>, [U])) $ x $ t
      end;

    val (ty_idxs, _) = List.foldl
      (fn ((i, (\<^type_name>\<open>noption\<close>, _, _)), p) => p
        | ((i, _), (ty_idxs, j)) => (ty_idxs @ [(i, j)], j + 1)) ([], 0) descr;

    fun reindex (Old_Datatype_Aux.DtType (s, dts)) = Old_Datatype_Aux.DtType (s, map reindex dts)
      | reindex (Old_Datatype_Aux.DtRec i) =
        Old_Datatype_Aux.DtRec (the (AList.lookup op = ty_idxs i))
      | reindex dt = dt;

    fun strip_suffix i s = implode (List.take (raw_explode s, size s - i));  (* FIXME Symbol.explode (?) *)

    (** strips the "_Rep" in type names *)
    fun strip_nth_name i s =
      let val xs = Long_Name.explode s;
      in Long_Name.implode (Library.nth_map (length xs - i) (strip_suffix 4) xs) end;

    val (descr'', ndescr) = ListPair.unzip (map_filter
      (fn (i, (\<^type_name>\<open>noption\<close>, _, _)) => NONE
        | (i, (s, dts, constrs)) =>
             let
               val SOME index = AList.lookup op = ty_idxs i;
               val (constrs2, constrs1) =
                 map_split (fn (cname, cargs) =>
                   apsnd (pair (strip_nth_name 2 (strip_nth_name 1 cname)))
                   (fold_map (fn dt => fn dts =>
                     let val (dts', dt') = strip_option dt
                     in ((length dts, length dts'), dts @ dts' @ [reindex dt']) end)
                       cargs [])) constrs
             in SOME ((index, (strip_nth_name 1 s,  map reindex dts, constrs1)),
               (index, constrs2))
             end) descr);

    val (descr1, descr2) = chop (length new_type_names) descr'';
    val descr' = [descr1, descr2];

    fun partition_cargs idxs xs = map (fn (i, j) =>
      (List.take (List.drop (xs, i), j), nth xs (i + j))) idxs;

    val pdescr = map (fn ((i, (s, dts, constrs)), (_, idxss)) => (i, (s, dts,
      map (fn ((cname, cargs), idxs) => (cname, partition_cargs idxs cargs))
        (constrs ~~ idxss)))) (descr'' ~~ ndescr);

    fun nth_dtyp' i = Old_Datatype_Aux.typ_of_dtyp descr'' (Old_Datatype_Aux.DtRec i);

    val rep_names = map (fn s =>
      Sign.intern_const thy7 ("Rep_" ^ s)) new_type_names;
    val abs_names = map (fn s =>
      Sign.intern_const thy7 ("Abs_" ^ s)) new_type_names;

    val recTs = Old_Datatype_Aux.get_rec_types descr'';
    val newTs' = take (length new_type_names) recTs';
    val newTs = take (length new_type_names) recTs;

    val full_new_type_names = map (Sign.full_bname thy) new_type_names;

    fun make_constr_def tname T T' (((cname_rep, _), (cname, cargs)), (cname', mx))
        (thy, defs, eqns) =
      let
        fun constr_arg (dts, dt) (j, l_args, r_args) =
          let
            val xs =
              map (fn (dt, i) =>
                  Old_Datatype_Aux.mk_Free "x" (Old_Datatype_Aux.typ_of_dtyp descr'' dt) i)
                (dts ~~ (j upto j + length dts - 1))
            val x =
              Old_Datatype_Aux.mk_Free "x" (Old_Datatype_Aux.typ_of_dtyp descr'' dt)
                (j + length dts)
          in
            (j + length dts + 1,
             xs @ x :: l_args,
             fold_rev mk_abs_fun xs
               (case dt of
                  Old_Datatype_Aux.DtRec k => if k < length new_type_names then
                      Const (nth rep_names k, Old_Datatype_Aux.typ_of_dtyp descr'' dt -->
                        Old_Datatype_Aux.typ_of_dtyp descr dt) $ x
                    else error "nested recursion not supported"
                | _ => x) :: r_args)
          end

        val (_, l_args, r_args) = fold_rev constr_arg cargs (1, [], []);
        val abs_name = Sign.intern_const thy ("Abs_" ^ tname);
        val rep_name = Sign.intern_const thy ("Rep_" ^ tname);
        val constrT = map fastype_of l_args ---> T;
        val lhs = list_comb (Const (cname, constrT), l_args);
        val rhs = list_comb (Const (cname_rep, map fastype_of r_args ---> T'), r_args);
        val def = Logic.mk_equals (lhs, Const (abs_name, T' --> T) $ rhs);
        val eqn = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (rep_name, T --> T') $ lhs, rhs));
        val def_name = (Long_Name.base_name cname) ^ "_def";
        val ([def_thm], thy') = thy |>
          Sign.add_consts [(cname', constrT, mx)] |>
          (Global_Theory.add_defs false o map Thm.no_attributes) [(Binding.name def_name, def)];
      in (thy', defs @ [def_thm], eqns @ [eqn]) end;

    fun dt_constr_defs ((((((_, (_, _, constrs)),
        (_, (_, _, constrs'))), tname), T), T'), constr_syntax) (thy, defs, eqns, dist_lemmas) =
      let
        val rep_const = Thm.global_cterm_of thy
          (Const (Sign.intern_const thy ("Rep_" ^ tname), T --> T'));
        val dist =
          Drule.export_without_context
            (infer_instantiate (Proof_Context.init_global thy)
              [(#1 (dest_Var distinct_f), rep_const)] Old_Datatype.distinct_lemma);
        val (thy', defs', eqns') = fold (make_constr_def tname T T')
          (constrs ~~ constrs' ~~ constr_syntax) (Sign.add_path tname thy, defs, [])
      in
        (Sign.parent_path thy', defs', eqns @ [eqns'], dist_lemmas @ [dist])
      end;

    val (thy8, constr_defs, constr_rep_eqns, dist_lemmas) = fold dt_constr_defs
      (List.take (descr, length new_type_names) ~~
        List.take (pdescr, length new_type_names) ~~
        new_type_names ~~ newTs ~~ newTs' ~~ constr_syntax)
      (thy7, [], [], []);

    val abs_inject_thms = map (collect_simp ctxt6 o #Abs_inject o snd o fst) typedefs
    val rep_inject_thms = map (#Rep_inject o snd o fst) typedefs

    (* prove theorem  Rep_i (Constr_j ...) = Constr'_j ...  *)

    fun prove_constr_rep_thm eqn =
      let
        val inj_thms = map (fn r => r RS iffD1) abs_inject_thms;
        val rewrites = constr_defs @ map mk_meta_eq Rep_inverse_thms
      in Goal.prove_global_future thy8 [] [] eqn (fn {context = ctxt, ...} => EVERY
        [resolve_tac ctxt inj_thms 1,
         rewrite_goals_tac ctxt rewrites,
         resolve_tac ctxt [refl] 3,
         resolve_tac ctxt rep_intrs 2,
         REPEAT (resolve_tac ctxt Rep_thms 1)])
      end;

    val constr_rep_thmss = map (map prove_constr_rep_thm) constr_rep_eqns;

    (* prove theorem  pi \<bullet> Rep_i x = Rep_i (pi \<bullet> x) *)

    fun prove_perm_rep_perm (atom, perm_closed_thms) = map (fn th =>
      let
        val _ $ (_ $ (Rep $ x)) = Logic.unvarify_global (Thm.prop_of th);
        val Type ("fun", [T, U]) = fastype_of Rep;
        val permT = mk_permT (Type (atom, []));
        val pi = Free ("pi", permT);
      in
        Goal.prove_global_future thy8 [] []
          (augment_sort thy8
            (pt_class_of thy8 atom :: map (cp_class_of thy8 atom) (remove (op =) atom dt_atoms))
            (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> U --> U) $ pi $ (Rep $ x),
               Rep $ (Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> T --> T) $ pi $ x)))))
          (fn {context = ctxt, ...} =>
            simp_tac (put_simpset HOL_basic_ss ctxt addsimps (perm_defs @ Abs_inverse_thms @
            perm_closed_thms @ Rep_thms)) 1)
      end) Rep_thms;

    val perm_rep_perm_thms = maps prove_perm_rep_perm (atoms ~~ perm_closed_thmss);

    (* prove distinctness theorems *)

    val distinct_props = Old_Datatype_Prop.make_distincts descr';
    val dist_rewrites = map2 (fn rep_thms => fn dist_lemma => dist_lemma :: rep_thms)
      constr_rep_thmss dist_lemmas;

    fun prove_distinct_thms _ [] = []
      | prove_distinct_thms (p as (rep_thms, dist_lemma)) (t :: ts) =
          let
            val dist_thm = Goal.prove_global_future thy8 [] [] t (fn {context = ctxt, ...} =>
              simp_tac (ctxt addsimps (dist_lemma :: rep_thms)) 1)
          in
            dist_thm :: Drule.export_without_context (dist_thm RS not_sym) ::
              prove_distinct_thms p ts
          end;

    val distinct_thms = map2 prove_distinct_thms
      (constr_rep_thmss ~~ dist_lemmas) distinct_props;

    (** prove equations for permutation functions **)

    val perm_simps' = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = nth_dtyp' i
      in maps (fn (atom, perm_closed_thms) =>
          map (fn ((cname, dts), constr_rep_thm) =>
        let
          val cname = Sign.intern_const thy8
            (Long_Name.append tname (Long_Name.base_name cname));
          val permT = mk_permT (Type (atom, []));
          val pi = Free ("pi", permT);

          fun perm t =
            let val T = fastype_of t
            in Const (\<^const_name>\<open>Nominal.perm\<close>, permT --> T --> T) $ pi $ t end;

          fun constr_arg (dts, dt) (j, l_args, r_args) =
            let
              val Ts = map (Old_Datatype_Aux.typ_of_dtyp descr'') dts;
              val xs =
                map (fn (T, i) => Old_Datatype_Aux.mk_Free "x" T i)
                  (Ts ~~ (j upto j + length dts - 1));
              val x =
                Old_Datatype_Aux.mk_Free "x" (Old_Datatype_Aux.typ_of_dtyp descr'' dt)
                  (j + length dts);
            in
              (j + length dts + 1,
               xs @ x :: l_args,
               map perm (xs @ [x]) @ r_args)
            end

          val (_, l_args, r_args) = fold_rev constr_arg dts (1, [], []);
          val c = Const (cname, map fastype_of l_args ---> T)
        in
          Goal.prove_global_future thy8 [] []
            (augment_sort thy8
              (pt_class_of thy8 atom :: map (cp_class_of thy8 atom) (remove (op =) atom dt_atoms))
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (perm (list_comb (c, l_args)), list_comb (c, r_args)))))
            (fn {context = ctxt, ...} => EVERY
              [simp_tac (ctxt addsimps (constr_rep_thm :: perm_defs)) 1,
               simp_tac (put_simpset HOL_basic_ss ctxt addsimps (Rep_thms @ Abs_inverse_thms @
                 constr_defs @ perm_closed_thms)) 1,
               TRY (simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                 (Thm.symmetric perm_fun_def :: abs_perm)) 1),
               TRY (simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                 (perm_fun_def :: perm_defs @ Rep_thms @ Abs_inverse_thms @
                    perm_closed_thms)) 1)])
        end) (constrs ~~ constr_rep_thms)) (atoms ~~ perm_closed_thmss)
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** prove injectivity of constructors **)

    val rep_inject_thms' = map (fn th => th RS sym) rep_inject_thms;
    val alpha = Global_Theory.get_thms thy8 "alpha";
    val abs_fresh = Global_Theory.get_thms thy8 "abs_fresh";

    val pt_cp_sort =
      map (pt_class_of thy8) dt_atoms @
      maps (fn s => map (cp_class_of thy8 s) (remove (op =) s dt_atoms)) dt_atoms;

    val inject_thms = map (fn (((i, (_, _, constrs)), tname), constr_rep_thms) =>
      let val T = nth_dtyp' i
      in map_filter (fn ((cname, dts), constr_rep_thm) =>
        if null dts then NONE else SOME
        let
          val cname = Sign.intern_const thy8
            (Long_Name.append tname (Long_Name.base_name cname));

          fun make_inj (dts, dt) (j, args1, args2, eqs) =
            let
              val Ts_idx =
                map (Old_Datatype_Aux.typ_of_dtyp descr'') dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => Old_Datatype_Aux.mk_Free "x" T i) Ts_idx;
              val ys = map (fn (T, i) => Old_Datatype_Aux.mk_Free "y" T i) Ts_idx;
              val x =
                Old_Datatype_Aux.mk_Free "x" (Old_Datatype_Aux.typ_of_dtyp descr'' dt)
                  (j + length dts);
              val y =
                Old_Datatype_Aux.mk_Free "y" (Old_Datatype_Aux.typ_of_dtyp descr'' dt)
                  (j + length dts);
            in
              (j + length dts + 1,
               xs @ (x :: args1), ys @ (y :: args2),
               HOLogic.mk_eq
                 (fold_rev mk_abs_fun xs x, fold_rev mk_abs_fun ys y) :: eqs)
            end;

          val (_, args1, args2, eqs) = fold_rev make_inj dts (1, [], [], []);
          val Ts = map fastype_of args1;
          val c = Const (cname, Ts ---> T)
        in
          Goal.prove_global_future thy8 [] []
            (augment_sort thy8 pt_cp_sort
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (HOLogic.mk_eq (list_comb (c, args1), list_comb (c, args2)),
                 foldr1 HOLogic.mk_conj eqs))))
            (fn {context = ctxt, ...} => EVERY
               [asm_full_simp_tac (ctxt addsimps (constr_rep_thm ::
                  rep_inject_thms')) 1,
                TRY (asm_full_simp_tac (put_simpset HOL_basic_ss ctxt
                  addsimps (fresh_def :: supp_def ::
                  alpha @ abs_perm @ abs_fresh @ rep_inject_thms @
                  perm_rep_perm_thms)) 1)])
        end) (constrs ~~ constr_rep_thms)
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ constr_rep_thmss);

    (** equations for support and freshness **)

    val (supp_thms, fresh_thms) = ListPair.unzip (map ListPair.unzip
      (map (fn ((((i, (_, _, constrs)), tname), inject_thms'), perm_thms') =>
      let val T = nth_dtyp' i
      in maps (fn (cname, dts) => map (fn atom =>
        let
          val cname = Sign.intern_const thy8
            (Long_Name.append tname (Long_Name.base_name cname));
          val atomT = Type (atom, []);

          fun process_constr (dts, dt) (j, args1, args2) =
            let
              val Ts_idx =
                map (Old_Datatype_Aux.typ_of_dtyp descr'') dts ~~ (j upto j + length dts - 1);
              val xs = map (fn (T, i) => Old_Datatype_Aux.mk_Free "x" T i) Ts_idx;
              val x =
                Old_Datatype_Aux.mk_Free "x" (Old_Datatype_Aux.typ_of_dtyp descr'' dt)
                  (j + length dts);
            in
              (j + length dts + 1,
               xs @ (x :: args1), fold_rev mk_abs_fun xs x :: args2)
            end;

          val (_, args1, args2) = fold_rev process_constr dts (1, [], []);
          val Ts = map fastype_of args1;
          val c = list_comb (Const (cname, Ts ---> T), args1);
          fun supp t =
            Const (\<^const_name>\<open>Nominal.supp\<close>, fastype_of t --> HOLogic.mk_setT atomT) $ t;
          fun fresh t = fresh_const atomT (fastype_of t) $ Free ("a", atomT) $ t;
          val supp_thm = Goal.prove_global_future thy8 [] []
            (augment_sort thy8 pt_cp_sort
              (HOLogic.mk_Trueprop (HOLogic.mk_eq
                (supp c,
                 if null dts then HOLogic.mk_set atomT []
                 else foldr1 (HOLogic.mk_binop \<^const_abbrev>\<open>union\<close>) (map supp args2)))))
            (fn {context = ctxt, ...} =>
              simp_tac (put_simpset HOL_basic_ss ctxt addsimps (supp_def ::
                 Un_assoc :: @{thm de_Morgan_conj} :: Collect_disj_eq :: finite_Un ::
                 Collect_False_empty :: finite_emptyI :: @{thms simp_thms} @
                 abs_perm @ abs_fresh @ inject_thms' @ perm_thms')) 1)
        in
          (supp_thm,
           Goal.prove_global_future thy8 [] [] (augment_sort thy8 pt_cp_sort
             (HOLogic.mk_Trueprop (HOLogic.mk_eq
               (fresh c,
                if null dts then \<^term>\<open>True\<close>
                else foldr1 HOLogic.mk_conj (map fresh args2)))))
             (fn {context = ctxt, ...} =>
               simp_tac (put_simpset HOL_ss ctxt addsimps [Un_iff, empty_iff, fresh_def, supp_thm]) 1))
        end) atoms) constrs
      end) (List.take (pdescr, length new_type_names) ~~ new_type_names ~~ inject_thms ~~ perm_simps')));

    (**** weak induction theorem ****)

    fun mk_indrule_lemma (((i, _), T), U) (prems, concls) =
      let
        val Rep_t = Const (nth rep_names i, T --> U) $ Old_Datatype_Aux.mk_Free "x" T i;

        val Abs_t =  Const (nth abs_names i, U --> T);

      in
        (prems @ [HOLogic.imp $
            (Const (nth rep_set_names'' i, U --> HOLogic.boolT) $ Rep_t) $
              (Old_Datatype_Aux.mk_Free "P" (T --> HOLogic.boolT) (i + 1) $ (Abs_t $ Rep_t))],
         concls @
           [Old_Datatype_Aux.mk_Free "P" (T --> HOLogic.boolT) (i + 1) $
              Old_Datatype_Aux.mk_Free "x" T i])
      end;

    val (indrule_lemma_prems, indrule_lemma_concls) =
      fold mk_indrule_lemma (descr'' ~~ recTs ~~ recTs') ([], []);

    val indrule_lemma = Goal.prove_global_future thy8 [] []
      (Logic.mk_implies
        (HOLogic.mk_Trueprop (Old_Datatype_Aux.mk_conj indrule_lemma_prems),
         HOLogic.mk_Trueprop (Old_Datatype_Aux.mk_conj indrule_lemma_concls)))
         (fn {context = ctxt, ...} => EVERY
           [REPEAT (eresolve_tac ctxt [conjE] 1),
            REPEAT (EVERY
              [TRY (resolve_tac ctxt [conjI] 1),
               full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps Rep_inverse_thms) 1,
               eresolve_tac ctxt [mp] 1,
               resolve_tac ctxt Rep_thms 1])]);

    val Ps = map head_of (HOLogic.dest_conj (HOLogic.dest_Trueprop (Thm.concl_of indrule_lemma)));
    val frees = if length Ps = 1 then [Free ("P", snd (dest_Var (hd Ps)))] else
      map (Free o apfst fst o dest_Var) Ps;

    val Abs_inverse_thms' = map (fn r => r RS subst) Abs_inverse_thms;

    val dt_induct_prop = Old_Datatype_Prop.make_ind descr';
    val dt_induct = Goal.prove_global_future thy8 []
      (Logic.strip_imp_prems dt_induct_prop) (Logic.strip_imp_concl dt_induct_prop)
      (fn {prems, context = ctxt} =>
        let
          val indrule_lemma' = infer_instantiate ctxt
            (map (#1 o dest_Var) Ps ~~ map (Thm.cterm_of ctxt) frees) indrule_lemma;
        in
          EVERY [resolve_tac ctxt [indrule_lemma'] 1,
           (Old_Datatype_Aux.ind_tac ctxt rep_induct [] THEN_ALL_NEW
             Object_Logic.atomize_prems_tac ctxt) 1,
           EVERY (map (fn (prem, r) => (EVERY
             [REPEAT (eresolve_tac ctxt Abs_inverse_thms' 1),
              simp_tac (put_simpset HOL_basic_ss ctxt addsimps [Thm.symmetric r]) 1,
              DEPTH_SOLVE_1
                (assume_tac ctxt 1 ORELSE resolve_tac ctxt [prem] 1 ORELSE eresolve_tac ctxt [allE] 1)]))
                  (prems ~~ constr_defs))]
        end);

    val case_names_induct = Old_Datatype_Data.mk_case_names_induct descr'';

    (**** prove that new datatypes have finite support ****)

    val _ = warning "proving finite support for the new datatype";

    val indnames = Old_Datatype_Prop.make_tnames recTs;

    val abs_supp = Global_Theory.get_thms thy8 "abs_supp";
    val supp_atm = Global_Theory.get_thms thy8 "supp_atm";

    val finite_supp_thms = map (fn atom =>
      let val atomT = Type (atom, [])
      in map Drule.export_without_context (List.take
        (Old_Datatype_Aux.split_conj_thm (Goal.prove_global_future thy8 [] []
           (augment_sort thy8 (fs_class_of thy8 atom :: pt_cp_sort)
             (HOLogic.mk_Trueprop
               (foldr1 HOLogic.mk_conj (map (fn (s, T) =>
                 Const (\<^const_name>\<open>finite\<close>, HOLogic.mk_setT atomT --> HOLogic.boolT) $
                   (Const (\<^const_name>\<open>Nominal.supp\<close>, T --> HOLogic.mk_setT atomT) $ Free (s, T)))
                   (indnames ~~ recTs)))))
           (fn {context = ctxt, ...} =>
             Old_Datatype_Aux.ind_tac ctxt dt_induct indnames 1 THEN
             ALLGOALS (asm_full_simp_tac (ctxt addsimps
              (abs_supp @ supp_atm @
               Global_Theory.get_thms thy8 ("fs_" ^ Long_Name.base_name atom ^ "1") @
               flat supp_thms))))),
         length new_type_names))
      end) atoms;

    val simp_atts = replicate (length new_type_names) [Simplifier.simp_add];

        (* Function to add both the simp and eqvt attributes *)
        (* These two attributes are duplicated on all the types in the mutual nominal datatypes *)

    val simp_eqvt_atts = replicate (length new_type_names) [Simplifier.simp_add, NominalThmDecls.eqvt_add];
 
    val (_, thy9) = thy8 |>
      Sign.add_path big_name |>
      Global_Theory.add_thms [((Binding.name "induct", dt_induct), [case_names_induct])] ||>>
      Global_Theory.add_thmss
        [((Binding.name "inducts", projections (Proof_Context.init_global thy8) dt_induct),
            [case_names_induct])] ||>
      Sign.parent_path ||>>
      Old_Datatype_Aux.store_thmss_atts "distinct" new_type_names simp_atts distinct_thms ||>>
      Old_Datatype_Aux.store_thmss "constr_rep" new_type_names constr_rep_thmss ||>>
      Old_Datatype_Aux.store_thmss_atts "perm" new_type_names simp_eqvt_atts perm_simps' ||>>
      Old_Datatype_Aux.store_thmss "inject" new_type_names inject_thms ||>>
      Old_Datatype_Aux.store_thmss "supp" new_type_names supp_thms ||>>
      Old_Datatype_Aux.store_thmss_atts "fresh" new_type_names simp_atts fresh_thms ||>
      fold (fn (atom, ths) => fn thy =>
        let
          val class = fs_class_of thy atom;
          val sort = Sign.minimize_sort thy (Sign.certify_sort thy (class :: pt_cp_sort));
        in fold (fn Type (s, Ts) => Axclass.prove_arity
          (s, map (inter_sort thy sort o snd o dest_TFree) Ts, [class])
          (fn ctxt => Class.intro_classes_tac ctxt [] THEN resolve_tac ctxt ths 1)) newTs thy
        end) (atoms ~~ finite_supp_thms);

    (**** strong induction theorem ****)

    val pnames = if length descr'' = 1 then ["P"]
      else map (fn i => "P" ^ string_of_int i) (1 upto length descr'');
    val ind_sort = if null dt_atomTs then \<^sort>\<open>type\<close>
      else Sign.minimize_sort thy9 (Sign.certify_sort thy9 (map (fs_class_of thy9) dt_atoms));
    val fsT = TFree ("'n", ind_sort);
    val fsT' = TFree ("'n", \<^sort>\<open>type\<close>);

    val fresh_fs = map (fn (s, T) => (T, Free (s, fsT' --> HOLogic.mk_setT T)))
      (Old_Datatype_Prop.indexify_names (replicate (length dt_atomTs) "f") ~~ dt_atomTs);

    fun make_pred fsT i T = Free (nth pnames i, fsT --> T --> HOLogic.boolT);

    fun mk_fresh1 xs [] = []
      | mk_fresh1 xs ((y as (_, T)) :: ys) = map (fn x => HOLogic.mk_Trueprop
            (HOLogic.mk_not (HOLogic.mk_eq (Free y, Free x))))
              (filter (fn (_, U) => T = U) (rev xs)) @
          mk_fresh1 (y :: xs) ys;

    fun mk_fresh2 xss [] = []
      | mk_fresh2 xss ((p as (ys, _)) :: yss) = maps (fn y as (_, T) =>
            map (fn (_, x as (_, U)) => HOLogic.mk_Trueprop
              (fresh_const T U $ Free y $ Free x)) (rev xss @ yss)) ys @
          mk_fresh2 (p :: xss) yss;

    fun make_ind_prem fsT f k T ((cname, cargs), idxs) =
      let
        val recs = filter Old_Datatype_Aux.is_rec_type cargs;
        val Ts = map (Old_Datatype_Aux.typ_of_dtyp descr'') cargs;
        val recTs' = map (Old_Datatype_Aux.typ_of_dtyp descr'') recs;
        val tnames = Name.variant_list pnames (Old_Datatype_Prop.make_tnames Ts);
        val rec_tnames = map fst (filter (Old_Datatype_Aux.is_rec_type o snd) (tnames ~~ cargs));
        val frees = tnames ~~ Ts;
        val frees' = partition_cargs idxs frees;
        val z = (singleton (Name.variant_list tnames) "z", fsT);

        fun mk_prem ((dt, s), T) =
          let
            val (Us, U) = strip_type T;
            val l = length Us;
          in
            Logic.list_all (z :: map (pair "x") Us,
              HOLogic.mk_Trueprop
                (make_pred fsT (Old_Datatype_Aux.body_index dt) U $ Bound l $
                  Old_Datatype_Aux.app_bnds (Free (s, T)) l))
          end;

        val prems = map mk_prem (recs ~~ rec_tnames ~~ recTs');
        val prems' = map (fn p as (_, T) => HOLogic.mk_Trueprop
            (f T (Free p) (Free z))) (maps fst frees') @
          mk_fresh1 [] (maps fst frees') @
          mk_fresh2 [] frees'

      in
        fold_rev (Logic.all o Free) (frees @ [z])
          (Logic.list_implies (prems' @ prems,
            HOLogic.mk_Trueprop (make_pred fsT k T $ Free z $
              list_comb (Const (cname, Ts ---> T), map Free frees))))
      end;

    val ind_prems = maps (fn (((i, (_, _, constrs)), (_, idxss)), T) =>
      map (make_ind_prem fsT (fn T => fn t => fn u =>
        fresh_const T fsT $ t $ u) i T)
          (constrs ~~ idxss)) (descr'' ~~ ndescr ~~ recTs);
    val tnames = Old_Datatype_Prop.make_tnames recTs;
    val zs = Name.variant_list tnames (replicate (length descr'') "z");
    val ind_concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop \<^const_name>\<open>HOL.conj\<close>)
      (map (fn ((((i, _), T), tname), z) =>
        make_pred fsT i T $ Free (z, fsT) $ Free (tname, T))
        (descr'' ~~ recTs ~~ tnames ~~ zs)));
    val induct = Logic.list_implies (ind_prems, ind_concl);

    val ind_prems' =
      map (fn (_, f as Free (_, T)) => Logic.all (Free ("x", fsT'))
        (HOLogic.mk_Trueprop (Const (\<^const_name>\<open>finite\<close>,
          Term.range_type T -->
            HOLogic.boolT) $ (f $ Free ("x", fsT'))))) fresh_fs @
      maps (fn (((i, (_, _, constrs)), (_, idxss)), T) =>
        map (make_ind_prem fsT' (fn T => fn t => fn u => HOLogic.Not $
          HOLogic.mk_mem (t, the (AList.lookup op = fresh_fs T) $ u)) i T)
            (constrs ~~ idxss)) (descr'' ~~ ndescr ~~ recTs);
    val ind_concl' = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop \<^const_name>\<open>HOL.conj\<close>)
      (map (fn ((((i, _), T), tname), z) =>
        make_pred fsT' i T $ Free (z, fsT') $ Free (tname, T))
        (descr'' ~~ recTs ~~ tnames ~~ zs)));
    val induct' = Logic.list_implies (ind_prems', ind_concl');

    val aux_ind_vars =
      (Old_Datatype_Prop.indexify_names (replicate (length dt_atomTs) "pi") ~~
       map mk_permT dt_atomTs) @ [("z", fsT')];
    val aux_ind_Ts = rev (map snd aux_ind_vars);
    val aux_ind_concl = HOLogic.mk_Trueprop (foldr1 (HOLogic.mk_binop \<^const_name>\<open>HOL.conj\<close>)
      (map (fn (((i, _), T), tname) =>
        HOLogic.list_all (aux_ind_vars, make_pred fsT' i T $ Bound 0 $
          fold_rev (mk_perm aux_ind_Ts) (map Bound (length dt_atomTs downto 1))
            (Free (tname, T))))
        (descr'' ~~ recTs ~~ tnames)));

    val fin_set_supp = map (fn s =>
      at_inst_of thy9 s RS at_fin_set_supp) dt_atoms;
    val fin_set_fresh = map (fn s =>
      at_inst_of thy9 s RS at_fin_set_fresh) dt_atoms;
    val pt1_atoms = map (fn Type (s, _) =>
      Global_Theory.get_thm thy9 ("pt_" ^ Long_Name.base_name s ^ "1")) dt_atomTs;
    val pt2_atoms = map (fn Type (s, _) =>
      Global_Theory.get_thm thy9 ("pt_" ^ Long_Name.base_name s ^ "2") RS sym) dt_atomTs;
    val exists_fresh' = Global_Theory.get_thms thy9 "exists_fresh'";
    val fs_atoms = Global_Theory.get_thms thy9 "fin_supp";
    val abs_supp = Global_Theory.get_thms thy9 "abs_supp";
    val perm_fresh_fresh = Global_Theory.get_thms thy9 "perm_fresh_fresh";
    val calc_atm = Global_Theory.get_thms thy9 "calc_atm";
    val fresh_atm = Global_Theory.get_thms thy9 "fresh_atm";
    val fresh_left = Global_Theory.get_thms thy9 "fresh_left";
    val perm_swap = Global_Theory.get_thms thy9 "perm_swap";

    fun obtain_fresh_name' ths ts T (freshs1, freshs2, ctxt) =
      let
        val p = foldr1 HOLogic.mk_prod (ts @ freshs1);
        val ex = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
            (HOLogic.exists_const T $ Abs ("x", T,
              fresh_const T (fastype_of p) $
                Bound 0 $ p)))
          (fn _ => EVERY
            [resolve_tac ctxt exists_fresh' 1,
             simp_tac (put_simpset HOL_ss ctxt addsimps (supp_prod :: finite_Un :: fs_atoms @
               fin_set_supp @ ths)) 1]);
        val (([(_, cx)], ths), ctxt') = Obtain.result
          (fn ctxt' => EVERY
            [eresolve_tac ctxt' [exE] 1,
             full_simp_tac (put_simpset HOL_ss ctxt' addsimps (fresh_prod :: fresh_atm)) 1,
             REPEAT (eresolve_tac ctxt' [conjE] 1)])
          [ex] ctxt
      in (freshs1 @ [Thm.term_of cx], freshs2 @ ths, ctxt') end;

    fun fresh_fresh_inst thy a b =
      let
        val T = fastype_of a;
        val SOME th = find_first (fn th =>
          (case Thm.prop_of th of
            _ $ (_ $ (Const (_, Type (_, [U, _])) $ _ $ _)) $ _ => U = T
          | _ => false)) perm_fresh_fresh
      in
        Thm.instantiate' []
          [SOME (Thm.global_cterm_of thy a), NONE, SOME (Thm.global_cterm_of thy b)] th
      end;

    val fs_cp_sort =
      map (fs_class_of thy9) dt_atoms @
      maps (fn s => map (cp_class_of thy9 s) (remove (op =) s dt_atoms)) dt_atoms;

    (**********************************************************************
      The subgoals occurring in the proof of induct_aux have the
      following parameters:

        x_1 ... x_k p_1 ... p_m z

      where

        x_i : constructor arguments (introduced by weak induction rule)
        p_i : permutations (one for each atom type in the data type)
        z   : freshness context
    ***********************************************************************)

    val _ = warning "proving strong induction theorem ...";

    val induct_aux = Goal.prove_global_future thy9 []
        (map (augment_sort thy9 fs_cp_sort) ind_prems')
        (augment_sort thy9 fs_cp_sort ind_concl') (fn {prems, context} =>
      let
        val (prems1, prems2) = chop (length dt_atomTs) prems;
        val ind_ss2 = put_simpset HOL_ss context addsimps
          finite_Diff :: abs_fresh @ abs_supp @ fs_atoms;
        val ind_ss1 = ind_ss2 addsimps fresh_left @ calc_atm @
          fresh_atm @ rev_simps @ app_simps;
        val ind_ss3 = put_simpset HOL_ss context addsimps abs_fun_eq1 ::
          abs_perm @ calc_atm @ perm_swap;
        val ind_ss4 = put_simpset HOL_basic_ss context addsimps fresh_left @ prems1 @
          fin_set_fresh @ calc_atm;
        val ind_ss5 = put_simpset HOL_basic_ss context addsimps pt1_atoms;
        val ind_ss6 = put_simpset HOL_basic_ss context addsimps flat perm_simps';
        val th = Goal.prove context [] []
          (augment_sort thy9 fs_cp_sort aux_ind_concl)
          (fn {context = context1, ...} =>
             EVERY (Old_Datatype_Aux.ind_tac context1 dt_induct tnames 1 ::
               maps (fn ((_, (_, _, constrs)), (_, constrs')) =>
                 map (fn ((cname, cargs), is) =>
                   REPEAT (resolve_tac context1 [allI] 1) THEN
                   SUBPROOF (fn {prems = iprems, params, concl,
                       context = context2, ...} =>
                     let
                       val concl' = Thm.term_of concl;
                       val _ $ (_ $ _ $ u) = concl';
                       val U = fastype_of u;
                       val (xs, params') =
                         chop (length cargs) (map (Thm.term_of o #2) params);
                       val Ts = map fastype_of xs;
                       val cnstr = Const (cname, Ts ---> U);
                       val (pis, z) = split_last params';
                       val mk_pi = fold_rev (mk_perm []) pis;
                       val xs' = partition_cargs is xs;
                       val xs'' = map (fn (ts, u) => (map mk_pi ts, mk_pi u)) xs';
                       val ts = maps (fn (ts, u) => ts @ [u]) xs'';
                       val (freshs1, freshs2, context3) = fold (fn t =>
                         let val T = fastype_of t
                         in obtain_fresh_name' prems1
                           (the (AList.lookup op = fresh_fs T) $ z :: ts) T
                         end) (maps fst xs') ([], [], context2);
                       val freshs1' = unflat (map fst xs') freshs1;
                       val freshs2' = map (Simplifier.simplify ind_ss4)
                         (mk_not_sym freshs2);
                       val ind_ss1' = ind_ss1 addsimps freshs2';
                       val ind_ss3' = ind_ss3 addsimps freshs2';
                       val rename_eq =
                         if forall (null o fst) xs' then []
                         else [Goal.prove context3 [] []
                           (HOLogic.mk_Trueprop (HOLogic.mk_eq
                             (list_comb (cnstr, ts),
                              list_comb (cnstr, maps (fn ((bs, t), cs) =>
                                cs @ [fold_rev (mk_perm []) (map perm_of_pair
                                  (bs ~~ cs)) t]) (xs'' ~~ freshs1')))))
                           (fn {context = ctxt, ...} => EVERY
                              (simp_tac (put_simpset HOL_ss context3 addsimps flat inject_thms) 1 ::
                               REPEAT (FIRSTGOAL (resolve_tac ctxt [conjI])) ::
                               maps (fn ((bs, t), cs) =>
                                 if null bs then []
                                 else resolve_tac ctxt [sym] 1 :: maps (fn (b, c) =>
                                   [resolve_tac ctxt [trans] 1,
                                    resolve_tac ctxt [sym] 1,
                                    resolve_tac ctxt [fresh_fresh_inst thy9 b c] 1,
                                    simp_tac ind_ss1' 1,
                                    simp_tac ind_ss2 1,
                                    simp_tac ind_ss3' 1]) (bs ~~ cs))
                                 (xs'' ~~ freshs1')))];
                       val th = Goal.prove context3 [] [] concl' (fn _ => EVERY
                         [simp_tac (ind_ss6 addsimps rename_eq) 1,
                          cut_facts_tac iprems 1,
                          (resolve_tac context2 prems THEN_ALL_NEW
                            SUBGOAL (fn (t, i) => case Logic.strip_assums_concl t of
                                _ $ (Const (\<^const_name>\<open>Nominal.fresh\<close>, _) $ _ $ _) =>
                                  simp_tac ind_ss1' i
                              | _ $ (Const (\<^const_name>\<open>Not\<close>, _) $ _) =>
                                  resolve_tac context2 freshs2' i
                              | _ => asm_simp_tac (put_simpset HOL_basic_ss context3 addsimps
                                  pt2_atoms addsimprocs [perm_simproc]) i)) 1])
                       val final = Proof_Context.export context3 context2 [th]
                     in
                       resolve_tac context2 final 1
                     end) context1 1) (constrs ~~ constrs')) (descr'' ~~ ndescr)))
      in
        EVERY
          [cut_facts_tac [th] 1,
           REPEAT (eresolve_tac context [conjE, @{thm allE_Nil}] 1),
           REPEAT (eresolve_tac context [allE] 1),
           REPEAT (TRY (resolve_tac context [conjI] 1) THEN asm_full_simp_tac ind_ss5 1)]
      end);

    val induct_aux' = Thm.instantiate (TVars.empty,
      Vars.make (map (fn (s, Var (v as (_, T))) =>
        (v, Thm.global_cterm_of thy9 (Free (s, T))))
          (pnames ~~ map head_of (HOLogic.dest_conj
             (HOLogic.dest_Trueprop (Thm.concl_of induct_aux)))) @
      map (fn (_, f) =>
        let val f' = Logic.varify_global f
        in (dest_Var f',
          Thm.global_cterm_of thy9 (Const (\<^const_name>\<open>Nominal.supp\<close>, fastype_of f')))
        end) fresh_fs)) induct_aux;

    val induct = Goal.prove_global_future thy9 []
      (map (augment_sort thy9 fs_cp_sort) ind_prems)
      (augment_sort thy9 fs_cp_sort ind_concl)
      (fn {prems, context = ctxt} => EVERY
         [resolve_tac ctxt [induct_aux'] 1,
          REPEAT (resolve_tac ctxt fs_atoms 1),
          REPEAT ((resolve_tac ctxt prems THEN_ALL_NEW
            (eresolve_tac ctxt @{thms meta_spec} ORELSE'
              full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [fresh_def]))) 1)])

    val (_, thy10) = thy9 |>
      Sign.add_path big_name |>
      Global_Theory.add_thms [((Binding.name "strong_induct'", induct_aux), [])] ||>>
      Global_Theory.add_thms [((Binding.name "strong_induct", induct), [case_names_induct])] ||>>
      Global_Theory.add_thmss
        [((Binding.name "strong_inducts", projections (Proof_Context.init_global thy9) induct),
            [case_names_induct])];

    (**** recursion combinator ****)

    val _ = warning "defining recursion combinator ...";

    val used = fold Term.add_tfree_namesT recTs [];

    val (rec_result_Ts', rec_fn_Ts') = Old_Datatype_Prop.make_primrec_Ts descr' used;

    val rec_sort = if null dt_atomTs then \<^sort>\<open>type\<close> else
      Sign.minimize_sort thy10 (Sign.certify_sort thy10 pt_cp_sort);

    val rec_result_Ts = map (fn TFree (s, _) => TFree (s, rec_sort)) rec_result_Ts';
    val rec_fn_Ts = map (typ_subst_atomic (rec_result_Ts' ~~ rec_result_Ts)) rec_fn_Ts';

    val rec_set_Ts = map (fn (T1, T2) =>
      rec_fn_Ts @ [T1, T2] ---> HOLogic.boolT) (recTs ~~ rec_result_Ts);

    val big_rec_name = big_name ^ "_rec_set";
    val rec_set_names' =
      if length descr'' = 1 then [big_rec_name] else
        map ((curry (op ^) (big_rec_name ^ "_")) o string_of_int)
          (1 upto (length descr''));
    val rec_set_names =  map (Sign.full_bname thy10) rec_set_names';

    val rec_fns = map (uncurry (Old_Datatype_Aux.mk_Free "f"))
      (rec_fn_Ts ~~ (1 upto (length rec_fn_Ts)));
    val rec_sets' = map (fn c => list_comb (Free c, rec_fns))
      (rec_set_names' ~~ rec_set_Ts);
    val rec_sets = map (fn c => list_comb (Const c, rec_fns))
      (rec_set_names ~~ rec_set_Ts);

    (* introduction rules for graph of recursion function *)

    val rec_preds = map (fn (a, T) =>
      Free (a, T --> HOLogic.boolT)) (pnames ~~ rec_result_Ts);

    fun mk_fresh3 rs [] = []
      | mk_fresh3 rs ((p as (ys, z)) :: yss) = maps (fn y as (_, T) =>
            map_filter (fn ((_, (_, x)), r as (_, U)) => if z = x then NONE
              else SOME (HOLogic.mk_Trueprop
                (fresh_const T U $ Free y $ Free r))) rs) ys @
          mk_fresh3 rs yss;

    (* FIXME: avoid collisions with other variable names? *)
    val rec_ctxt = Free ("z", fsT');

    fun make_rec_intr T p rec_set ((cname, cargs), idxs)
        (rec_intr_ts, rec_prems, rec_prems', rec_eq_prems, l) =
      let
        val Ts = map (Old_Datatype_Aux.typ_of_dtyp descr'') cargs;
        val frees = map (fn i => "x" ^ string_of_int i) (1 upto length Ts) ~~ Ts;
        val frees' = partition_cargs idxs frees;
        val binders = maps fst frees';
        val atomTs = distinct op = (maps (map snd o fst) frees');
        val recs = map_filter
          (fn ((_, Old_Datatype_Aux.DtRec i), p) => SOME (i, p) | _ => NONE)
          (partition_cargs idxs cargs ~~ frees');
        val frees'' = map (fn i => "y" ^ string_of_int i) (1 upto length recs) ~~
          map (fn (i, _) => nth rec_result_Ts i) recs;
        val prems1 = map (fn ((i, (_, x)), y) => HOLogic.mk_Trueprop
          (nth rec_sets' i $ Free x $ Free y)) (recs ~~ frees'');
        val prems2 =
          map (fn f => map (fn p as (_, T) => HOLogic.mk_Trueprop
            (fresh_const T (fastype_of f) $ Free p $ f)) binders) rec_fns;
        val prems3 = mk_fresh1 [] binders @ mk_fresh2 [] frees';
        val prems4 = map (fn ((i, _), y) =>
          HOLogic.mk_Trueprop (nth rec_preds i $ Free y)) (recs ~~ frees'');
        val prems5 = mk_fresh3 (recs ~~ frees'') frees';
        val prems6 = maps (fn aT => map (fn y as (_, T) => HOLogic.mk_Trueprop
          (Const (\<^const_name>\<open>finite\<close>, HOLogic.mk_setT aT --> HOLogic.boolT) $
             (Const (\<^const_name>\<open>Nominal.supp\<close>, T --> HOLogic.mk_setT aT) $ Free y)))
               frees'') atomTs;
        val prems7 = map (fn x as (_, T) => HOLogic.mk_Trueprop
          (fresh_const T fsT' $ Free x $ rec_ctxt)) binders;
        val result = list_comb (nth rec_fns l, map Free (frees @ frees''));
        val result_freshs = map (fn p as (_, T) =>
          fresh_const T (fastype_of result) $ Free p $ result) binders;
        val P = HOLogic.mk_Trueprop (p $ result)
      in
        (rec_intr_ts @ [Logic.list_implies (flat prems2 @ prems3 @ prems1,
           HOLogic.mk_Trueprop (rec_set $
             list_comb (Const (cname, Ts ---> T), map Free frees) $ result))],
         rec_prems @ [fold_rev (Logic.all o Free) (frees @ frees'') (Logic.list_implies (prems4, P))],
         rec_prems' @ map (fn fr => fold_rev (Logic.all o Free) (frees @ frees'')
           (Logic.list_implies (nth prems2 l @ prems3 @ prems5 @ prems7 @ prems6 @ [P],
             HOLogic.mk_Trueprop fr))) result_freshs,
         rec_eq_prems @ [flat prems2 @ prems3],
         l + 1)
      end;

    val (rec_intr_ts, rec_prems, rec_prems', rec_eq_prems, _) =
      fold (fn ((((d, d'), T), p), rec_set) =>
        fold (make_rec_intr T p rec_set) (#3 (snd d) ~~ snd d'))
          (descr'' ~~ ndescr ~~ recTs ~~ rec_preds ~~ rec_sets')
          ([], [], [], [], 0);

    val ({intrs = rec_intrs, elims = rec_elims, raw_induct = rec_induct, ...}, thy11) =
      thy10
      |> Sign.concealed
      |> Named_Target.theory_map_result Inductive.transform_result
          (Inductive.add_inductive {quiet_mode = #quiet config, verbose = false, alt_name = Binding.name big_rec_name,
           coind = false, no_elim = false, no_ind = false, skip_mono = true}
          (map (fn (s, T) => ((Binding.name s, T), NoSyn)) (rec_set_names' ~~ rec_set_Ts))
          (map dest_Free rec_fns)
          (map (fn x => (Binding.empty_atts, x)) rec_intr_ts) [])
      ||> Global_Theory.hide_fact true (Long_Name.append (Sign.full_bname thy10 big_rec_name) "induct")
      ||> Sign.restore_naming thy10;

    (** equivariance **)

    val fresh_bij = Global_Theory.get_thms thy11 "fresh_bij";
    val perm_bij = Global_Theory.get_thms thy11 "perm_bij";

    val (rec_equiv_thms, rec_equiv_thms') = ListPair.unzip (map (fn aT =>
      let
        val permT = mk_permT aT;
        val pi = Free ("pi", permT);
        val rec_fns_pi = map (mk_perm [] pi o uncurry (Old_Datatype_Aux.mk_Free "f"))
          (rec_fn_Ts ~~ (1 upto (length rec_fn_Ts)));
        val rec_sets_pi = map (fn c => list_comb (Const c, rec_fns_pi))
          (rec_set_names ~~ rec_set_Ts);
        val ps = map (fn ((((T, U), R), R'), i) =>
          let
            val x = Free ("x" ^ string_of_int i, T);
            val y = Free ("y" ^ string_of_int i, U)
          in
            (R $ x $ y, R' $ mk_perm [] pi x $ mk_perm [] pi y)
          end) (recTs ~~ rec_result_Ts ~~ rec_sets ~~ rec_sets_pi ~~ (1 upto length recTs));
        val ths = map (fn th => Drule.export_without_context (th RS mp))
          (Old_Datatype_Aux.split_conj_thm
            (Goal.prove_global_future thy11 [] []
              (augment_sort thy1 pt_cp_sort
                (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj (map HOLogic.mk_imp ps))))
              (fn {context = ctxt, ...} =>
                 resolve_tac ctxt [rec_induct] 1 THEN REPEAT
                 (simp_tac (put_simpset HOL_basic_ss ctxt
                    addsimps flat perm_simps'
                    addsimprocs [NominalPermeq.perm_simproc_app]) 1 THEN
                  (resolve_tac ctxt rec_intrs THEN_ALL_NEW
                   asm_simp_tac (put_simpset HOL_ss ctxt addsimps (fresh_bij @ perm_bij))) 1))))
        val ths' = map (fn ((P, Q), th) =>
          Goal.prove_global_future thy11 [] []
            (augment_sort thy1 pt_cp_sort
              (Logic.mk_implies (HOLogic.mk_Trueprop Q, HOLogic.mk_Trueprop P)))
            (fn {context = ctxt, ...} =>
              dresolve_tac ctxt [Thm.instantiate (TVars.empty,
                 Vars.make [((("pi", 0), permT),
                   Thm.global_cterm_of thy11 (Const (\<^const_name>\<open>rev\<close>, permT --> permT) $ pi))]) th] 1 THEN
               NominalPermeq.perm_simp_tac (put_simpset HOL_ss ctxt) 1)) (ps ~~ ths)
      in (ths, ths') end) dt_atomTs);

    (** finite support **)

    val rec_fin_supp_thms = map (fn aT =>
      let
        val name = Long_Name.base_name (fst (dest_Type aT));
        val fs_name = Global_Theory.get_thm thy11 ("fs_" ^ name ^ "1");
        val aset = HOLogic.mk_setT aT;
        val finite = Const (\<^const_name>\<open>finite\<close>, aset --> HOLogic.boolT);
        val fins = map (fn (f, T) => HOLogic.mk_Trueprop
          (finite $ (Const (\<^const_name>\<open>Nominal.supp\<close>, T --> aset) $ f)))
            (rec_fns ~~ rec_fn_Ts)
      in
        map (fn th => Drule.export_without_context (th RS mp)) (Old_Datatype_Aux.split_conj_thm
          (Goal.prove_global_future thy11 []
            (map (augment_sort thy11 fs_cp_sort) fins)
            (augment_sort thy11 fs_cp_sort
              (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                (map (fn (((T, U), R), i) =>
                   let
                     val x = Free ("x" ^ string_of_int i, T);
                     val y = Free ("y" ^ string_of_int i, U)
                   in
                     HOLogic.mk_imp (R $ x $ y,
                       finite $ (Const (\<^const_name>\<open>Nominal.supp\<close>, U --> aset) $ y))
                   end) (recTs ~~ rec_result_Ts ~~ rec_sets ~~
                     (1 upto length recTs))))))
            (fn {prems = fins, context = ctxt} =>
              (resolve_tac ctxt [rec_induct] THEN_ALL_NEW cut_facts_tac fins) 1 THEN REPEAT
               (NominalPermeq.finite_guess_tac (put_simpset HOL_ss ctxt addsimps [fs_name]) 1))))
      end) dt_atomTs;

    (** freshness **)

    val finite_premss = map (fn aT =>
      map (fn (f, T) => HOLogic.mk_Trueprop
        (Const (\<^const_name>\<open>finite\<close>, HOLogic.mk_setT aT --> HOLogic.boolT) $
           (Const (\<^const_name>\<open>Nominal.supp\<close>, T --> HOLogic.mk_setT aT) $ f)))
           (rec_fns ~~ rec_fn_Ts)) dt_atomTs;

    val rec_fns' = map (augment_sort thy11 fs_cp_sort) rec_fns;

    val rec_fresh_thms = map (fn ((aT, eqvt_ths), finite_prems) =>
      let
        val name = Long_Name.base_name (fst (dest_Type aT));
        val fs_name = Global_Theory.get_thm thy11 ("fs_" ^ name ^ "1");
        val a = Free ("a", aT);
        val freshs = map (fn (f, fT) => HOLogic.mk_Trueprop
          (fresh_const aT fT $ a $ f)) (rec_fns ~~ rec_fn_Ts)
      in
        map (fn (((T, U), R), eqvt_th) =>
          let
            val x = Free ("x", augment_sort_typ thy11 fs_cp_sort T);
            val y = Free ("y", U);
            val y' = Free ("y'", U)
          in
            Drule.export_without_context (Goal.prove (Proof_Context.init_global thy11) []
              (map (augment_sort thy11 fs_cp_sort)
                (finite_prems @
                   [HOLogic.mk_Trueprop (R $ x $ y),
                    HOLogic.mk_Trueprop (HOLogic.mk_all ("y'", U,
                      HOLogic.mk_imp (R $ x $ y', HOLogic.mk_eq (y', y)))),
                    HOLogic.mk_Trueprop (fresh_const aT T $ a $ x)] @
                 freshs))
              (HOLogic.mk_Trueprop (fresh_const aT U $ a $ y))
              (fn {prems, context = ctxt} =>
                 let
                   val (finite_prems, rec_prem :: unique_prem ::
                     fresh_prems) = chop (length finite_prems) prems;
                   val unique_prem' = unique_prem RS spec RS mp;
                   val unique = [unique_prem', unique_prem' RS sym] MRS trans;
                   val _ $ (_ $ (_ $ S $ _)) $ _ = Thm.prop_of supports_fresh;
                   val tuple = foldr1 HOLogic.mk_prod (x :: rec_fns')
                 in EVERY
                   [resolve_tac ctxt [infer_instantiate ctxt
                      [(#1 (dest_Var S),
                        Thm.cterm_of ctxt (Const (\<^const_name>\<open>Nominal.supp\<close>,
                          fastype_of tuple --> HOLogic.mk_setT aT) $ tuple))]
                      supports_fresh] 1,
                    simp_tac (put_simpset HOL_basic_ss ctxt addsimps
                      [supports_def, Thm.symmetric fresh_def, fresh_prod]) 1,
                    REPEAT_DETERM (resolve_tac ctxt [allI, impI] 1),
                    REPEAT_DETERM (eresolve_tac ctxt [conjE] 1),
                    resolve_tac ctxt [unique] 1,
                    SUBPROOF (fn {context = ctxt', prems = prems', params = [(_, a), (_, b)], ...} =>
                      EVERY [cut_facts_tac [rec_prem] 1,
                       resolve_tac ctxt' [Thm.instantiate (TVars.empty,
                         Vars.make [((("pi", 0), mk_permT aT),
                           Thm.cterm_of ctxt'
                            (perm_of_pair (Thm.term_of a, Thm.term_of b)))]) eqvt_th] 1,
                       asm_simp_tac (put_simpset HOL_ss ctxt' addsimps
                         (prems' @ perm_swap @ perm_fresh_fresh)) 1]) ctxt 1,
                    resolve_tac ctxt [rec_prem] 1,
                    simp_tac (put_simpset HOL_ss ctxt addsimps (fs_name ::
                      supp_prod :: finite_Un :: finite_prems)) 1,
                    simp_tac (put_simpset HOL_ss ctxt addsimps (Thm.symmetric fresh_def ::
                      fresh_prod :: fresh_prems)) 1]
                 end))
          end) (recTs ~~ rec_result_Ts ~~ rec_sets ~~ eqvt_ths)
      end) (dt_atomTs ~~ rec_equiv_thms' ~~ finite_premss);

    (** uniqueness **)

    val fun_tuple = foldr1 HOLogic.mk_prod (rec_ctxt :: rec_fns);
    val fun_tupleT = fastype_of fun_tuple;
    val rec_unique_frees =
      Old_Datatype_Prop.indexify_names (replicate (length recTs) "x") ~~ recTs;
    val rec_unique_frees'' = map (fn (s, T) => (s ^ "'", T)) rec_unique_frees;
    val rec_unique_frees' =
      Old_Datatype_Prop.indexify_names (replicate (length recTs) "y") ~~ rec_result_Ts;
    val rec_unique_concls = map (fn ((x, U), R) =>
        Const (\<^const_name>\<open>Ex1\<close>, (U --> HOLogic.boolT) --> HOLogic.boolT) $
          Abs ("y", U, R $ Free x $ Bound 0))
      (rec_unique_frees ~~ rec_result_Ts ~~ rec_sets);

    val induct_aux_rec =
      infer_instantiate (Proof_Context.init_global thy11)
      (map (apsnd (Thm.global_cterm_of thy11 o augment_sort thy11 fs_cp_sort))
         (map (fn (aT, f) => (#1 (dest_Var (Logic.varify_global f)), Abs ("z", HOLogic.unitT,
            Const (\<^const_name>\<open>Nominal.supp\<close>, fun_tupleT --> HOLogic.mk_setT aT) $ fun_tuple)))
              fresh_fs @
          map (fn (((P, T), (x, U)), Q) =>
           ((P, 0),
            Abs ("z", HOLogic.unitT, absfree (x, U) Q)))
              (pnames ~~ recTs ~~ rec_unique_frees ~~ rec_unique_concls) @
          map (fn (s, T) => ((s, 0), Free (s, T)))
            rec_unique_frees)) induct_aux;

    fun obtain_fresh_name vs ths rec_fin_supp T (freshs1, freshs2, ctxt) =
      let
        val p = foldr1 HOLogic.mk_prod (vs @ freshs1);
        val ex = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
            (HOLogic.exists_const T $ Abs ("x", T,
              fresh_const T (fastype_of p) $ Bound 0 $ p)))
          (fn _ => EVERY
            [cut_facts_tac ths 1,
             REPEAT_DETERM (dresolve_tac ctxt (the (AList.lookup op = rec_fin_supp T)) 1),
             resolve_tac ctxt exists_fresh' 1,
             asm_simp_tac (put_simpset HOL_ss ctxt addsimps (supp_prod :: finite_Un :: fs_atoms)) 1]);
        val (([(_, cx)], ths), ctxt') = Obtain.result
          (fn ctxt' => EVERY
            [eresolve_tac ctxt' [exE] 1,
             full_simp_tac (put_simpset HOL_ss ctxt' addsimps (fresh_prod :: fresh_atm)) 1,
             REPEAT (eresolve_tac ctxt [conjE] 1)])
          [ex] ctxt
      in (freshs1 @ [Thm.term_of cx], freshs2 @ ths, ctxt') end;

    val finite_ctxt_prems = map (fn aT =>
      HOLogic.mk_Trueprop
        (Const (\<^const_name>\<open>finite\<close>, HOLogic.mk_setT aT --> HOLogic.boolT) $
           (Const (\<^const_name>\<open>Nominal.supp\<close>, fsT' --> HOLogic.mk_setT aT) $ rec_ctxt))) dt_atomTs;

    val rec_unique_thms = Old_Datatype_Aux.split_conj_thm (Goal.prove
      (Proof_Context.init_global thy11) (map fst rec_unique_frees)
      (map (augment_sort thy11 fs_cp_sort)
        (flat finite_premss @ finite_ctxt_prems @ rec_prems @ rec_prems'))
      (augment_sort thy11 fs_cp_sort
        (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj rec_unique_concls)))
      (fn {prems, context} =>
         let
           val k = length rec_fns;
           val (finite_thss, ths1) = fold_map (fn T => fn xs =>
             apfst (pair T) (chop k xs)) dt_atomTs prems;
           val (finite_ctxt_ths, ths2) = chop (length dt_atomTs) ths1;
           val (P_ind_ths, fcbs) = chop k ths2;
           val P_ths = map (fn th => th RS mp) (Old_Datatype_Aux.split_conj_thm
             (Goal.prove context
               (map fst (rec_unique_frees'' @ rec_unique_frees')) []
               (augment_sort thy11 fs_cp_sort
                 (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
                    (map (fn (((x, y), S), P) => HOLogic.mk_imp
                      (S $ Free x $ Free y, P $ (Free y)))
                        (rec_unique_frees'' ~~ rec_unique_frees' ~~
                           rec_sets ~~ rec_preds)))))
               (fn {context = ctxt, ...} =>
                  resolve_tac ctxt [rec_induct] 1 THEN
                  REPEAT ((resolve_tac ctxt P_ind_ths THEN_ALL_NEW assume_tac ctxt) 1))));
           val rec_fin_supp_thms' = map
             (fn (ths, (T, fin_ths)) => (T, map (curry op MRS fin_ths) ths))
             (rec_fin_supp_thms ~~ finite_thss);
         in EVERY
           ([resolve_tac context [induct_aux_rec] 1] @
            maps (fn ((_, finite_ths), finite_th) =>
              [cut_facts_tac (finite_th :: finite_ths) 1,
               asm_simp_tac (put_simpset HOL_ss context addsimps [supp_prod, finite_Un]) 1])
                (finite_thss ~~ finite_ctxt_ths) @
            maps (fn ((_, idxss), elim) => maps (fn idxs =>
              [full_simp_tac (put_simpset HOL_ss context addsimps [Thm.symmetric fresh_def, supp_prod, Un_iff]) 1,
               REPEAT_DETERM (eresolve_tac context @{thms conjE ex1E} 1),
               resolve_tac context @{thms ex1I} 1,
               (resolve_tac context rec_intrs THEN_ALL_NEW assume_tac context) 1,
               rotate_tac ~1 1,
               ((DETERM o eresolve_tac context [elim]) THEN_ALL_NEW full_simp_tac
                  (put_simpset HOL_ss context addsimps flat distinct_thms)) 1] @
               (if null idxs then [] else [hyp_subst_tac context 1,
                SUBPROOF (fn {asms, concl, prems = prems', params, context = context', ...} =>
                  let
                    val SOME prem = find_first (can (HOLogic.dest_eq o
                      HOLogic.dest_Trueprop o Thm.prop_of)) prems';
                    val _ $ (_ $ lhs $ rhs) = Thm.prop_of prem;
                    val _ $ (_ $ lhs' $ rhs') = Thm.term_of concl;
                    val rT = fastype_of lhs';
                    val (c, cargsl) = strip_comb lhs;
                    val cargsl' = partition_cargs idxs cargsl;
                    val boundsl = maps fst cargsl';
                    val (_, cargsr) = strip_comb rhs;
                    val cargsr' = partition_cargs idxs cargsr;
                    val boundsr = maps fst cargsr';
                    val (params1, _ :: params2) =
                      chop (length params div 2) (map (Thm.term_of o #2) params);
                    val params' = params1 @ params2;
                    val rec_prems = filter (fn th =>
                        (case Thm.prop_of th of
                          _ $ p =>
                            (case head_of p of
                              Const (s, _) => member (op =) rec_set_names s
                            | _ => false)
                        | _ => false)) prems';
                    val fresh_prems = filter (fn th =>
                      (case Thm.prop_of th of
                        _ $ (Const (\<^const_name>\<open>Nominal.fresh\<close>, _) $ _ $ _) => true
                      | _ $ (Const (\<^const_name>\<open>Not\<close>, _) $ _) => true
                      | _ => false)) prems';
                    val Ts = map fastype_of boundsl;

                    val _ = warning "step 1: obtaining fresh names";
                    val (freshs1, freshs2, context'') = fold
                      (obtain_fresh_name (rec_ctxt :: rec_fns' @ params')
                         (maps snd finite_thss @ finite_ctxt_ths @ rec_prems)
                         rec_fin_supp_thms')
                      Ts ([], [], context');
                    val pi1 = map perm_of_pair (boundsl ~~ freshs1);
                    val rpi1 = rev pi1;
                    val pi2 = map perm_of_pair (boundsr ~~ freshs1);
                    val rpi2 = rev pi2;

                    val fresh_prems' = mk_not_sym fresh_prems;
                    val freshs2' = mk_not_sym freshs2;

                    (** as, bs, cs # K as ts, K bs us **)
                    val _ = warning "step 2: as, bs, cs # K as ts, K bs us";
                    val prove_fresh_simpset = put_simpset HOL_ss context'' addsimps
                      (finite_Diff :: flat fresh_thms @
                       fs_atoms @ abs_fresh @ abs_supp @ fresh_atm);
                    (* FIXME: avoid asm_full_simp_tac ? *)
                    fun prove_fresh ths y x = Goal.prove context'' [] []
                      (HOLogic.mk_Trueprop (fresh_const
                         (fastype_of x) (fastype_of y) $ x $ y))
                      (fn _ => cut_facts_tac ths 1 THEN asm_full_simp_tac prove_fresh_simpset 1);
                    val constr_fresh_thms =
                      map (prove_fresh fresh_prems lhs) boundsl @
                      map (prove_fresh fresh_prems rhs) boundsr @
                      map (prove_fresh freshs2 lhs) freshs1 @
                      map (prove_fresh freshs2 rhs) freshs1;

                    (** pi1 o (K as ts) = pi2 o (K bs us) **)
                    val _ = warning "step 3: pi1 o (K as ts) = pi2 o (K bs us)";
                    val pi1_pi2_eq = Goal.prove context'' [] []
                      (HOLogic.mk_Trueprop (HOLogic.mk_eq
                        (fold_rev (mk_perm []) pi1 lhs, fold_rev (mk_perm []) pi2 rhs)))
                      (fn {context = ctxt, ...} => EVERY
                         [cut_facts_tac constr_fresh_thms 1,
                          asm_simp_tac (put_simpset HOL_basic_ss context'' addsimps perm_fresh_fresh) 1,
                          resolve_tac ctxt [prem] 1]);

                    (** pi1 o ts = pi2 o us **)
                    val _ = warning "step 4: pi1 o ts = pi2 o us";
                    val pi1_pi2_eqs = map (fn (t, u) =>
                      Goal.prove context'' [] []
                        (HOLogic.mk_Trueprop (HOLogic.mk_eq
                          (fold_rev (mk_perm []) pi1 t, fold_rev (mk_perm []) pi2 u)))
                        (fn _ => EVERY
                           [cut_facts_tac [pi1_pi2_eq] 1,
                            asm_full_simp_tac (put_simpset HOL_ss context'' addsimps
                              (calc_atm @ flat perm_simps' @
                               fresh_prems' @ freshs2' @ abs_perm @
                               alpha @ flat inject_thms)) 1]))
                        (map snd cargsl' ~~ map snd cargsr');

                    (** pi1^-1 o pi2 o us = ts **)
                    val _ = warning "step 5: pi1^-1 o pi2 o us = ts";
                    val rpi1_pi2_eqs = map (fn ((t, u), eq) =>
                      Goal.prove context'' [] []
                        (HOLogic.mk_Trueprop (HOLogic.mk_eq
                          (fold_rev (mk_perm []) (rpi1 @ pi2) u, t)))
                        (fn _ => simp_tac (put_simpset HOL_ss context'' addsimps
                           ((eq RS sym) :: perm_swap)) 1))
                        (map snd cargsl' ~~ map snd cargsr' ~~ pi1_pi2_eqs);

                    val (rec_prems1, rec_prems2) =
                      chop (length rec_prems div 2) rec_prems;

                    (** (ts, pi1^-1 o pi2 o vs) in rec_set **)
                    val _ = warning "step 6: (ts, pi1^-1 o pi2 o vs) in rec_set";
                    val rec_prems' = map (fn th =>
                      let
                        val _ $ (S $ x $ y) = Thm.prop_of th;
                        val Const (s, _) = head_of S;
                        val k = find_index (equal s) rec_set_names;
                        val pi = rpi1 @ pi2;
                        fun mk_pi z = fold_rev (mk_perm []) pi z;
                        fun eqvt_tac ctxt p =
                          let
                            val U as Type (_, [Type (_, [T, _])]) = fastype_of p;
                            val l = find_index (equal T) dt_atomTs;
                            val th = nth (nth rec_equiv_thms' l) k;
                            val th' = Thm.instantiate (TVars.empty,
                              Vars.make [((("pi", 0), U), Thm.global_cterm_of thy11 p)]) th;
                          in resolve_tac ctxt [th'] 1 end;
                        val th' = Goal.prove context'' [] []
                          (HOLogic.mk_Trueprop (S $ mk_pi x $ mk_pi y))
                          (fn {context = ctxt, ...} => EVERY
                             (map (eqvt_tac ctxt) pi @
                              [simp_tac (put_simpset HOL_ss context'' addsimps (fresh_prems' @ freshs2' @
                                 perm_swap @ perm_fresh_fresh)) 1,
                               resolve_tac ctxt [th] 1]))
                      in
                        Simplifier.simplify
                          (put_simpset HOL_basic_ss context'' addsimps rpi1_pi2_eqs) th'
                      end) rec_prems2;

                    val ihs = filter (fn th =>
                      (case Thm.prop_of th of
                        _ $ (Const (\<^const_name>\<open>All\<close>, _) $ _) => true
                      | _ => false)) prems';

                    (** pi1 o rs = pi2 o vs , rs = pi1^-1 o pi2 o vs **)
                    val _ = warning "step 7: pi1 o rs = pi2 o vs , rs = pi1^-1 o pi2 o vs";
                    val rec_eqns = map (fn (th, ih) =>
                      let
                        val th' = th RS (ih RS spec RS mp) RS sym;
                        val _ $ (_ $ lhs $ rhs) = Thm.prop_of th';
                        fun strip_perm (_ $ _ $ t) = strip_perm t
                          | strip_perm t = t;
                      in
                        Goal.prove context'' [] []
                           (HOLogic.mk_Trueprop (HOLogic.mk_eq
                              (fold_rev (mk_perm []) pi1 lhs,
                               fold_rev (mk_perm []) pi2 (strip_perm rhs))))
                           (fn _ => simp_tac (put_simpset HOL_basic_ss context'' addsimps
                              (th' :: perm_swap)) 1)
                      end) (rec_prems' ~~ ihs);

                    (** as # rs **)
                    val _ = warning "step 8: as # rs";
                    val rec_freshs =
                      maps (fn (rec_prem, ih) =>
                        let
                          val _ $ (S $ x $ (y as Free (_, T))) =
                            Thm.prop_of rec_prem;
                          val k = find_index (equal S) rec_sets;
                          val atoms = flat (map_filter (fn (bs, z) =>
                            if z = x then NONE else SOME bs) cargsl')
                        in
                          map (fn a as Free (_, aT) =>
                            let val l = find_index (equal aT) dt_atomTs;
                            in
                              Goal.prove context'' [] []
                                (HOLogic.mk_Trueprop (fresh_const aT T $ a $ y))
                                (fn {context = ctxt, ...} => EVERY
                                   (resolve_tac ctxt [nth (nth rec_fresh_thms l) k] 1 ::
                                    map (fn th => resolve_tac ctxt [th] 1)
                                      (snd (nth finite_thss l)) @
                                    [resolve_tac ctxt [rec_prem] 1,
                                     resolve_tac ctxt [ih] 1,
                                     REPEAT_DETERM (resolve_tac ctxt fresh_prems 1)]))
                            end) atoms
                        end) (rec_prems1 ~~ ihs);

                    (** as # fK as ts rs , bs # fK bs us vs **)
                    val _ = warning "step 9: as # fK as ts rs , bs # fK bs us vs";
                    fun prove_fresh_result (a as Free (_, aT)) =
                      Goal.prove context'' [] []
                        (HOLogic.mk_Trueprop (fresh_const aT rT $ a $ rhs'))
                        (fn _ => EVERY
                           [resolve_tac context'' fcbs 1,
                            REPEAT_DETERM (resolve_tac context''
                              (fresh_prems @ rec_freshs) 1),
                            REPEAT_DETERM (resolve_tac context'' (maps snd rec_fin_supp_thms') 1
                              THEN resolve_tac context'' rec_prems 1),
                            resolve_tac context'' P_ind_ths 1,
                            REPEAT_DETERM (resolve_tac context'' (P_ths @ rec_prems) 1)]);

                    val fresh_results'' = map prove_fresh_result boundsl;

                    fun prove_fresh_result'' ((a as Free (_, aT), b), th) =
                      let val th' = Goal.prove context'' [] []
                        (HOLogic.mk_Trueprop (fresh_const aT rT $
                            fold_rev (mk_perm []) (rpi2 @ pi1) a $
                            fold_rev (mk_perm []) (rpi2 @ pi1) rhs'))
                        (fn {context = ctxt, ...} =>
                          simp_tac (put_simpset HOL_ss context'' addsimps fresh_bij) 1 THEN
                          resolve_tac ctxt [th] 1)
                      in
                        Goal.prove context'' [] []
                          (HOLogic.mk_Trueprop (fresh_const aT rT $ b $ lhs'))
                          (fn {context = ctxt, ...} => EVERY
                             [cut_facts_tac [th'] 1,
                              full_simp_tac (put_simpset HOL_ss ctxt
                                addsimps rec_eqns @ pi1_pi2_eqs @ perm_swap
                                addsimprocs [NominalPermeq.perm_simproc_app]) 1,
                              full_simp_tac (put_simpset HOL_ss context'' addsimps (calc_atm @
                                fresh_prems' @ freshs2' @ perm_fresh_fresh)) 1])
                      end;

                    val fresh_results = fresh_results'' @ map prove_fresh_result''
                      (boundsl ~~ boundsr ~~ fresh_results'');

                    (** cs # fK as ts rs , cs # fK bs us vs **)
                    val _ = warning "step 10: cs # fK as ts rs , cs # fK bs us vs";
                    fun prove_fresh_result' recs t (a as Free (_, aT)) =
                      Goal.prove context'' [] []
                        (HOLogic.mk_Trueprop (fresh_const aT rT $ a $ t))
                        (fn _ => EVERY
                          [cut_facts_tac recs 1,
                           REPEAT_DETERM (dresolve_tac context''
                             (the (AList.lookup op = rec_fin_supp_thms' aT)) 1),
                           NominalPermeq.fresh_guess_tac
                             (put_simpset HOL_ss context'' addsimps (freshs2 @
                                fs_atoms @ fresh_atm @
                                maps snd finite_thss)) 1]);

                    val fresh_results' =
                      map (prove_fresh_result' rec_prems1 rhs') freshs1 @
                      map (prove_fresh_result' rec_prems2 lhs') freshs1;

                    (** pi1 o (fK as ts rs) = pi2 o (fK bs us vs) **)
                    val _ = warning "step 11: pi1 o (fK as ts rs) = pi2 o (fK bs us vs)";
                    val pi1_pi2_result = Goal.prove context'' [] []
                      (HOLogic.mk_Trueprop (HOLogic.mk_eq
                        (fold_rev (mk_perm []) pi1 rhs', fold_rev (mk_perm []) pi2 lhs')))
                      (fn _ => simp_tac (put_simpset HOL_ss context''
                           addsimps pi1_pi2_eqs @ rec_eqns
                           addsimprocs [NominalPermeq.perm_simproc_app]) 1 THEN
                         TRY (simp_tac (put_simpset HOL_ss context'' addsimps
                           (fresh_prems' @ freshs2' @ calc_atm @ perm_fresh_fresh)) 1));

                    val _ = warning "final result";
                    val final = Goal.prove context'' [] [] (Thm.term_of concl)
                      (fn _ => cut_facts_tac [pi1_pi2_result RS sym] 1 THEN
                        full_simp_tac (put_simpset HOL_basic_ss context'' addsimps perm_fresh_fresh @
                          fresh_results @ fresh_results') 1);
                    val final' = Proof_Context.export context'' context' [final];
                    val _ = warning "finished!"
                  in
                    resolve_tac context' final' 1
                  end) context 1])) idxss) (ndescr ~~ rec_elims))
         end));

    val rec_total_thms = map (fn r => r RS @{thm theI'}) rec_unique_thms;

    (* define primrec combinators *)

    val big_reccomb_name = space_implode "_" new_type_names ^ "_rec";
    val reccomb_names = map (Sign.full_bname thy11)
      (if length descr'' = 1 then [big_reccomb_name] else
        (map ((curry (op ^) (big_reccomb_name ^ "_")) o string_of_int)
          (1 upto (length descr''))));
    val reccombs = map (fn ((name, T), T') => list_comb
      (Const (name, rec_fn_Ts @ [T] ---> T'), rec_fns))
        (reccomb_names ~~ recTs ~~ rec_result_Ts);

    val (reccomb_defs, thy12) =
      thy11
      |> Sign.add_consts (map (fn ((name, T), T') =>
          (Binding.name (Long_Name.base_name name), rec_fn_Ts @ [T] ---> T', NoSyn))
          (reccomb_names ~~ recTs ~~ rec_result_Ts))
      |> (Global_Theory.add_defs false o map Thm.no_attributes) (map (fn ((((name, comb), set), T), T') =>
          (Binding.name (Long_Name.base_name name ^ "_def"), Logic.mk_equals (comb, absfree ("x", T)
           (Const (\<^const_name>\<open>The\<close>, (T' --> HOLogic.boolT) --> T') $ absfree ("y", T')
             (set $ Free ("x", T) $ Free ("y", T'))))))
               (reccomb_names ~~ reccombs ~~ rec_sets ~~ recTs ~~ rec_result_Ts));

    (* prove characteristic equations for primrec combinators *)

    val rec_thms = map (fn (prems, concl) =>
      let
        val _ $ (_ $ (_ $ x) $ _) = concl;
        val (_, cargs) = strip_comb x;
        val ps = map (fn (x as Free (_, T), i) =>
          (Free ("x" ^ string_of_int i, T), x)) (cargs ~~ (1 upto length cargs));
        val concl' = subst_atomic_types (rec_result_Ts' ~~ rec_result_Ts) concl;
        val prems' = flat finite_premss @ finite_ctxt_prems @
          rec_prems @ rec_prems' @ map (subst_atomic ps) prems;
        fun solve ctxt rules prems = resolve_tac ctxt rules THEN_ALL_NEW
          (resolve_tac ctxt prems THEN_ALL_NEW assume_tac ctxt)
      in
        Goal.prove_global_future thy12 []
          (map (augment_sort thy12 fs_cp_sort) prems')
          (augment_sort thy12 fs_cp_sort concl')
          (fn {context = ctxt, prems} => EVERY
            [rewrite_goals_tac ctxt reccomb_defs,
             resolve_tac ctxt @{thms the1_equality} 1,
             solve ctxt rec_unique_thms prems 1,
             resolve_tac ctxt rec_intrs 1,
             REPEAT (solve ctxt (prems @ rec_total_thms) prems 1)])
      end) (rec_eq_prems ~~
        Old_Datatype_Prop.make_primrecs reccomb_names descr' thy12);

    val dt_infos = map_index (make_dt_info pdescr induct reccomb_names rec_thms)
      (descr1 ~~ distinct_thms ~~ inject_thms);

    (* FIXME: theorems are stored in database for testing only *)
    val (_, thy13) = thy12 |>
      Global_Theory.add_thmss
        [((Binding.name "rec_equiv", flat rec_equiv_thms), []),
         ((Binding.name "rec_equiv'", flat rec_equiv_thms'), []),
         ((Binding.name "rec_fin_supp", flat rec_fin_supp_thms), []),
         ((Binding.name "rec_fresh", flat rec_fresh_thms), []),
         ((Binding.name "rec_unique", map Drule.export_without_context rec_unique_thms), []),
         ((Binding.name "recs", rec_thms), [])] ||>
      Sign.parent_path ||>
      map_nominal_datatypes (fold Symtab.update dt_infos);
  in
    thy13
  end;

val nominal_datatype = gen_nominal_datatype Old_Datatype.check_specs;
val nominal_datatype_cmd = gen_nominal_datatype Old_Datatype.read_specs;

val spec_cmd =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (\<^keyword>\<open>=\<close> |-- Parse.enum1 "|" (Parse.binding -- Scan.repeat Parse.typ -- Parse.opt_mixfix))
  >> (fn (((vs, t), mx), cons) => ((t, vs, mx), map Scan.triple1 cons));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nominal_datatype\<close> "define nominal datatypes"
    (Parse.and_list1 spec_cmd >>
      (Toplevel.theory o nominal_datatype_cmd Old_Datatype_Aux.default_config));

end
