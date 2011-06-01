(*  Title:      HOL/Tools/Metis/metis_translate.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Metis.
*)

signature METIS_TRANSLATE =
sig
  type type_literal = ATP_Translate.type_literal
  type type_sys = ATP_Translate.type_sys

  datatype mode = FO | HO | FT | MX

  type metis_problem =
    {axioms : (Metis_Thm.thm * thm) list,
     tfrees : type_literal list,
     old_skolems : (string * term) list}

  val metis_equal : string
  val metis_predicator : string
  val metis_app_op : string
  val metis_type_tag : string
  val metis_generated_var_prefix : string
  val metis_name_table : ((string * int) * (string * bool)) list
  val reveal_old_skolem_terms : (string * term) list -> term -> term
  val string_of_mode : mode -> string
  val prepare_metis_problem :
    Proof.context -> mode -> type_sys option -> thm list -> thm list
    -> mode * int Symtab.table * metis_problem
end

structure Metis_Translate : METIS_TRANSLATE =
struct

open ATP_Problem
open ATP_Translate

val metis_equal = "="
val metis_predicator = "{}"
val metis_app_op = "."
val metis_type_tag = ":"
val metis_generated_var_prefix = "_"

val metis_name_table =
  [((tptp_equal, 2), (metis_equal, false)),
   ((tptp_old_equal, 2), (metis_equal, false)),
   ((const_prefix ^ predicator_name, 1), (metis_predicator, false)),
   ((const_prefix ^ app_op_name, 2), (metis_app_op, false)),
   ((const_prefix ^ type_tag_name, 2), (metis_type_tag, true))]

fun predicate_of thy ((@{const Not} $ P), pos) = predicate_of thy (P, not pos)
  | predicate_of thy (t, pos) =
    (combterm_from_term thy [] (Envir.eta_contract t), pos)

fun literals_of_term1 args thy (@{const Trueprop} $ P) =
    literals_of_term1 args thy P
  | literals_of_term1 args thy (@{const HOL.disj} $ P $ Q) =
    literals_of_term1 (literals_of_term1 args thy P) thy Q
  | literals_of_term1 (lits, ts) thy P =
    let val ((pred, ts'), pol) = predicate_of thy (P, true) in
      ((pol, pred) :: lits, union (op =) ts ts')
    end
val literals_of_term = literals_of_term1 ([], [])

fun old_skolem_const_name i j num_T_args =
  old_skolem_const_prefix ^ Long_Name.separator ^
  (space_implode Long_Name.separator (map string_of_int [i, j, num_T_args]))

fun conceal_old_skolem_terms i old_skolems t =
  if exists_Const (curry (op =) @{const_name Meson.skolem} o fst) t then
    let
      fun aux old_skolems
             (t as (Const (@{const_name Meson.skolem}, Type (_, [_, T])) $ _)) =
          let
            val (old_skolems, s) =
              if i = ~1 then
                (old_skolems, @{const_name undefined})
              else case AList.find (op aconv) old_skolems t of
                s :: _ => (old_skolems, s)
              | [] =>
                let
                  val s = old_skolem_const_name i (length old_skolems)
                                                (length (Term.add_tvarsT T []))
                in ((s, t) :: old_skolems, s) end
          in (old_skolems, Const (s, T)) end
        | aux old_skolems (t1 $ t2) =
          let
            val (old_skolems, t1) = aux old_skolems t1
            val (old_skolems, t2) = aux old_skolems t2
          in (old_skolems, t1 $ t2) end
        | aux old_skolems (Abs (s, T, t')) =
          let val (old_skolems, t') = aux old_skolems t' in
            (old_skolems, Abs (s, T, t'))
          end
        | aux old_skolems t = (old_skolems, t)
    in aux old_skolems t end
  else
    (old_skolems, t)

fun reveal_old_skolem_terms old_skolems =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix old_skolem_const_prefix s then
                   AList.lookup (op =) old_skolems s |> the
                   |> map_types Type_Infer.paramify_vars
                 else
                   t
               | t => t)


(* ------------------------------------------------------------------------- *)
(* HOL to FOL  (Isabelle to Metis)                                           *)
(* ------------------------------------------------------------------------- *)

(* first-order, higher-order, fully-typed, mode X (fleXible) *)
datatype mode = FO | HO | FT | MX

fun string_of_mode FO = "FO"
  | string_of_mode HO = "HO"
  | string_of_mode FT = "FT"
  | string_of_mode MX = "MX"

fun fn_isa_to_met_sublevel "equal" = "c_fequal"
  | fn_isa_to_met_sublevel "c_False" = "c_fFalse"
  | fn_isa_to_met_sublevel "c_True" = "c_fTrue"
  | fn_isa_to_met_sublevel "c_Not" = "c_fNot"
  | fn_isa_to_met_sublevel "c_conj" = "c_fconj"
  | fn_isa_to_met_sublevel "c_disj" = "c_fdisj"
  | fn_isa_to_met_sublevel "c_implies" = "c_fimplies"
  | fn_isa_to_met_sublevel x = x

fun fn_isa_to_met_toplevel "equal" = metis_equal
  | fn_isa_to_met_toplevel x = x

fun metis_lit b c args = (b, (c, args));

fun metis_term_from_typ (Type (s, Ts)) =
    Metis_Term.Fn (make_fixed_type_const s, map metis_term_from_typ Ts)
  | metis_term_from_typ (TFree (s, _)) =
    Metis_Term.Fn (make_fixed_type_var s, [])
  | metis_term_from_typ (TVar (x, _)) =
    Metis_Term.Var (make_schematic_type_var x)

(*These two functions insert type literals before the real literals. That is the
  opposite order from TPTP linkup, but maybe OK.*)

fun hol_term_to_fol_FO tm =
  case strip_combterm_comb tm of
      (CombConst ((c, _), _, Ts), tms) =>
        let val tyargs = map metis_term_from_typ Ts
            val args = map hol_term_to_fol_FO tms
        in Metis_Term.Fn (c, tyargs @ args) end
    | (CombVar ((v, _), _), []) => Metis_Term.Var v
    | _ => raise Fail "non-first-order combterm"

fun hol_term_to_fol_HO (CombConst ((a, _), _, Ts)) =
    Metis_Term.Fn (fn_isa_to_met_sublevel a, map metis_term_from_typ Ts)
  | hol_term_to_fol_HO (CombVar ((s, _), _)) = Metis_Term.Var s
  | hol_term_to_fol_HO (CombApp (tm1, tm2)) =
    Metis_Term.Fn (metis_app_op, map hol_term_to_fol_HO [tm1, tm2])

(*The fully-typed translation, to avoid type errors*)
fun tag_with_type tm T =
  Metis_Term.Fn (metis_type_tag, [tm, metis_term_from_typ T])

fun hol_term_to_fol_FT (CombVar ((s, _), ty)) =
    tag_with_type (Metis_Term.Var s) ty
  | hol_term_to_fol_FT (CombConst ((a, _), ty, _)) =
    tag_with_type (Metis_Term.Fn (fn_isa_to_met_sublevel a, [])) ty
  | hol_term_to_fol_FT (tm as CombApp (tm1,tm2)) =
    tag_with_type
        (Metis_Term.Fn (metis_app_op, map hol_term_to_fol_FT [tm1, tm2]))
        (combtyp_of tm)

fun hol_literal_to_fol FO (pos, tm) =
      let
        val (CombConst((p, _), _, Ts), tms) = strip_combterm_comb tm
        val tylits = if p = "equal" then [] else map metis_term_from_typ Ts
        val lits = map hol_term_to_fol_FO tms
      in metis_lit pos (fn_isa_to_met_toplevel p) (tylits @ lits) end
  | hol_literal_to_fol HO (pos, tm) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pos metis_equal (map hol_term_to_fol_HO tms)
        | _ => metis_lit pos metis_predicator [hol_term_to_fol_HO tm])
  | hol_literal_to_fol FT (pos, tm) =
     (case strip_combterm_comb tm of
          (CombConst(("equal", _), _, _), tms) =>
            metis_lit pos metis_equal (map hol_term_to_fol_FT tms)
        | _ => metis_lit pos metis_predicator [hol_term_to_fol_FT tm])

fun literals_of_hol_term thy mode t =
  let val (lits, types_sorts) = literals_of_term thy t in
    (map (hol_literal_to_fol mode) lits, types_sorts)
  end

(*Sign should be "true" for conjecture type constraints, "false" for type lits in clauses.*)
fun metis_of_type_literals pos (TyLitVar ((s, _), (s', _))) =
    metis_lit pos s [Metis_Term.Var s']
  | metis_of_type_literals pos (TyLitFree ((s, _), (s', _))) =
    metis_lit pos s [Metis_Term.Fn (s',[])]

fun has_default_sort _ (TVar _) = false
  | has_default_sort ctxt (TFree (x, s)) =
    (s = the_default [] (Variable.def_sort ctxt (x, ~1)));

fun metis_of_tfree tf =
  Metis_Thm.axiom (Metis_LiteralSet.singleton (metis_of_type_literals true tf));

fun hol_thm_to_fol is_conjecture ctxt mode j old_skolems th =
  let
    val thy = Proof_Context.theory_of ctxt
    val (old_skolems, (mlits, types_sorts)) =
     th |> prop_of |> Logic.strip_imp_concl
        |> conceal_old_skolem_terms j old_skolems
        ||> (HOLogic.dest_Trueprop #> literals_of_hol_term thy mode)
  in
    if is_conjecture then
      (Metis_Thm.axiom (Metis_LiteralSet.fromList mlits),
       raw_type_literals_for_types types_sorts, old_skolems)
    else
      let
        val tylits = types_sorts |> filter_out (has_default_sort ctxt)
                                 |> raw_type_literals_for_types
        val mtylits = map (metis_of_type_literals false) tylits
      in
        (Metis_Thm.axiom (Metis_LiteralSet.fromList(mtylits @ mlits)), [],
         old_skolems)
      end
  end;

(* ------------------------------------------------------------------------- *)
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

type metis_problem =
  {axioms : (Metis_Thm.thm * thm) list,
   tfrees : type_literal list,
   old_skolems : (string * term) list}

fun is_quasi_fol_clause thy =
  Meson.is_fol_term thy o snd o conceal_old_skolem_terms ~1 [] o prop_of

(*Extract TFree constraints from context to include as conjecture clauses*)
fun init_tfrees ctxt =
  let fun add ((a,i),s) Ts = if i = ~1 then TFree(a,s) :: Ts else Ts in
    Vartab.fold add (#2 (Variable.constraints_of ctxt)) []
    |> raw_type_literals_for_types
  end;

fun const_in_metis c (pred, tm_list) =
  let
    fun in_mterm (Metis_Term.Var _) = false
      | in_mterm (Metis_Term.Fn (nm, tm_list)) =
        c = nm orelse exists in_mterm tm_list
  in c = pred orelse exists in_mterm tm_list end

(* ARITY CLAUSE *)
fun m_arity_cls (TConsLit ((c, _), (t, _), args)) =
    metis_lit true c [Metis_Term.Fn(t, map (Metis_Term.Var o fst) args)]
  | m_arity_cls (TVarLit ((c, _), (s, _))) =
    metis_lit false c [Metis_Term.Var s]
(* TrueI is returned as the Isabelle counterpart because there isn't any. *)
fun arity_cls ({prem_lits, concl_lits, ...} : arity_clause) =
  (TrueI,
   Metis_Thm.axiom (Metis_LiteralSet.fromList
                        (map m_arity_cls (concl_lits :: prem_lits))));

(* CLASSREL CLAUSE *)
fun m_class_rel_cls (subclass, _) (superclass, _) =
  [metis_lit false subclass [Metis_Term.Var "T"],
   metis_lit true superclass [Metis_Term.Var "T"]]
fun class_rel_cls ({subclass, superclass, ...} : class_rel_clause) =
  (TrueI, m_class_rel_cls subclass superclass
          |> Metis_LiteralSet.fromList |> Metis_Thm.axiom)

fun type_ext thy tms =
  let
    val subs = tfree_classes_of_terms tms
    val supers = tvar_classes_of_terms tms
    val tycons = type_consts_of_terms thy tms
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in map class_rel_cls class_rel_clauses @ map arity_cls arity_clauses end

fun metis_name_from_atp s ary =
  AList.lookup (op =) metis_name_table (s, ary) |> the_default (s, false)
fun metis_term_from_atp (ATerm (s, tms)) =
  if is_tptp_variable s then
    Metis_Term.Var s
  else
    let val (s, swap) = metis_name_from_atp s (length tms) in
      Metis_Term.Fn (s, tms |> map metis_term_from_atp |> swap ? rev)
    end
fun metis_atom_from_atp (AAtom tm) =
    (case metis_term_from_atp tm of
       Metis_Term.Fn x => x
     | _ => raise Fail "non CNF -- expected function")
  | metis_atom_from_atp _ = raise Fail "not CNF -- expected atom"
fun metis_literal_from_atp (AConn (ANot, [phi])) =
    (false, metis_atom_from_atp phi)
  | metis_literal_from_atp phi = (true, metis_atom_from_atp phi)
fun metis_literals_from_atp (AConn (AOr, [phi1, phi2])) =
    uncurry (union (op =)) (pairself metis_literals_from_atp (phi1, phi2))
  | metis_literals_from_atp phi = [metis_literal_from_atp phi]
fun metis_axiom_from_atp clauses (Formula (ident, _, phi, _, _)) =
    (phi |> metis_literals_from_atp |> Metis_LiteralSet.fromList
         |> Metis_Thm.axiom,
     case try (unprefix conjecture_prefix) ident of
       SOME s => Meson.make_meta_clause (nth clauses (the (Int.fromString s)))
     | NONE => TrueI)
  | metis_axiom_from_atp _ _ = raise Fail "not CNF -- expected formula"

val default_type_sys = Preds (Polymorphic, Nonmonotonic_Types, Light)

(* Function to generate metis clauses, including comb and type clauses *)
fun prepare_metis_problem ctxt MX type_sys conj_clauses fact_clauses =
    let
      val type_sys = type_sys |> the_default default_type_sys
      val explicit_apply = NONE
      val clauses =
        conj_clauses @ fact_clauses
        |> (if polymorphism_of_type_sys type_sys = Polymorphic then
              I
            else
              map (pair 0)
              #> rpair ctxt
              #-> Monomorph.monomorph Monomorph.all_schematic_consts_of
              #> fst #> maps (map snd))
      val (atp_problem, _, _, _, _, _, sym_tab) =
        prepare_atp_problem ctxt CNF Hypothesis Axiom type_sys explicit_apply
                            false false (map prop_of clauses) @{prop False} []
      val axioms =
        atp_problem
        |> maps (map_filter (try (metis_axiom_from_atp clauses)) o snd)
    in
      (MX, sym_tab,
       {axioms = axioms, tfrees = [], old_skolems = [] (* FIXME ### *)})
    end
  | prepare_metis_problem ctxt mode _ conj_clauses fact_clauses =
    let
      val thy = Proof_Context.theory_of ctxt
      (* The modes FO and FT are sticky. HO can be downgraded to FO. *)
      val mode =
        if mode = HO andalso
           forall (forall (is_quasi_fol_clause thy))
                  [conj_clauses, fact_clauses] then
          FO
        else
          mode
      fun add_thm is_conjecture (isa_ith, metis_ith)
                  {axioms, tfrees, old_skolems} : metis_problem =
        let
          val (mth, tfree_lits, old_skolems) =
            hol_thm_to_fol is_conjecture ctxt mode (length axioms) old_skolems
                           metis_ith
        in
          {axioms = (mth, isa_ith) :: axioms,
           tfrees = union (op =) tfree_lits tfrees, old_skolems = old_skolems}
        end;
      fun add_type_thm (ith, mth) {axioms, tfrees, old_skolems} =
        {axioms = (mth, ith) :: axioms, tfrees = tfrees,
         old_skolems = old_skolems}
      fun add_tfrees {axioms, tfrees, old_skolems} =
        {axioms =
           map (rpair TrueI o metis_of_tfree) (distinct (op =) tfrees) @ axioms,
         tfrees = tfrees, old_skolems = old_skolems}
      val problem =
        {axioms = [], tfrees = init_tfrees ctxt, old_skolems = []}
        |> fold (add_thm true o `Meson.make_meta_clause) conj_clauses
        |> add_tfrees
        |> fold (add_thm false o `Meson.make_meta_clause) fact_clauses
      val clause_lists = map (Metis_Thm.clause o #1) (#axioms problem)
      fun is_used c =
        exists (Metis_LiteralSet.exists (const_in_metis c o #2)) clause_lists
      val problem =
        if mode = FO then
          problem
        else
          let
            val fdefs = @{thms fFalse_def fTrue_def fNot_def fconj_def fdisj_def
                               fimplies_def fequal_def}
            val prepare_helper =
              zero_var_indexes
              #> `(Meson.make_meta_clause
                   #> rewrite_rule (map safe_mk_meta_eq fdefs))
            val helper_ths =
              helper_table
              |> filter (is_used o prefix const_prefix o fst)
              |> maps (fn (_, (needs_full_types, thms)) =>
                          if needs_full_types andalso mode <> FT then []
                          else map prepare_helper thms)
          in problem |> fold (add_thm false) helper_ths end
      val type_ths = type_ext thy (map prop_of (conj_clauses @ fact_clauses))
    in (mode, Symtab.empty, fold add_type_thm type_ths problem) end

end;
