(*  Title:      HOL/Tools/Metis/metis_generate.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Translation of HOL to FOL for Metis.
*)

signature METIS_GENERATE =
sig
  type type_enc = ATP_Problem_Generate.type_enc

  datatype isa_thm =
    Isa_Reflexive_or_Trivial |
    Isa_Lambda_Lifted |
    Isa_Raw of thm

  val metis_equal : string
  val metis_predicator : string
  val metis_app_op : string
  val metis_systematic_type_tag : string
  val metis_ad_hoc_type_tag : string
  val metis_generated_var_prefix : string
  val trace : bool Config.T
  val verbose : bool Config.T
  val trace_msg : Proof.context -> (unit -> string) -> unit
  val verbose_warning : Proof.context -> string -> unit
  val metis_name_table : ((string * int) * ((type_enc -> string) * bool)) list
  val reveal_old_skolem_terms : (string * term) list -> term -> term
  val reveal_lam_lifted : (string * term) list -> term -> term
  val prepare_metis_problem :
    Proof.context -> type_enc -> string -> thm list -> thm list
    -> int Symtab.table * (Metis_Thm.thm * isa_thm) list
       * ((string * term) list * (string * term) list)
end

structure Metis_Generate : METIS_GENERATE =
struct

open ATP_Problem
open ATP_Problem_Generate

val metis_equal = "="
val metis_predicator = "{}"
val metis_app_op = Metis_Name.toString Metis_Term.appName
val metis_systematic_type_tag =
  Metis_Name.toString Metis_Term.hasTypeFunctionName
val metis_ad_hoc_type_tag = "**"
val metis_generated_var_prefix = "_"

val trace = Attrib.setup_config_bool @{binding metis_trace} (K false)
val verbose = Attrib.setup_config_bool @{binding metis_verbose} (K true)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()
fun verbose_warning ctxt msg =
  if Config.get ctxt verbose then warning ("Metis: " ^ msg) else ()

val metis_name_table =
  [((tptp_equal, 2), (K metis_equal, false)),
   ((tptp_old_equal, 2), (K metis_equal, false)),
   ((prefixed_predicator_name, 1), (K metis_predicator, false)),
   ((prefixed_app_op_name, 2), (K metis_app_op, false)),
   ((prefixed_type_tag_name, 2),
    (fn type_enc =>
        if level_of_type_enc type_enc = All_Types then metis_systematic_type_tag
        else metis_ad_hoc_type_tag, true))]

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
                   |> map_types (map_type_tvar (K dummyT))
                 else
                   t
               | t => t)

fun reveal_lam_lifted lambdas =
  map_aterms (fn t as Const (s, _) =>
                 if String.isPrefix lam_lifted_prefix s then
                   case AList.lookup (op =) lambdas s of
                     SOME t =>
                     Const (@{const_name Metis.lambda}, dummyT)
                     $ map_types (map_type_tvar (K dummyT))
                                 (reveal_lam_lifted lambdas t)
                   | NONE => t
                 else
                   t
               | t => t)


(* ------------------------------------------------------------------------- *)
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

datatype isa_thm =
  Isa_Reflexive_or_Trivial |
  Isa_Lambda_Lifted |
  Isa_Raw of thm

val proxy_defs = map (fst o snd o snd) proxy_table
val prepare_helper =
  Meson.make_meta_clause #> rewrite_rule (map safe_mk_meta_eq proxy_defs)

fun metis_term_from_atp type_enc (ATerm (s, tms)) =
  if is_tptp_variable s then
    Metis_Term.Var (Metis_Name.fromString s)
  else
    (case AList.lookup (op =) metis_name_table (s, length tms) of
       SOME (f, swap) => (f type_enc, swap)
     | NONE => (s, false))
    |> (fn (s, swap) =>
           Metis_Term.Fn (Metis_Name.fromString s,
                          tms |> map (metis_term_from_atp type_enc)
                              |> swap ? rev))
fun metis_atom_from_atp type_enc (AAtom tm) =
    (case metis_term_from_atp type_enc tm of
       Metis_Term.Fn x => x
     | _ => raise Fail "non CNF -- expected function")
  | metis_atom_from_atp _ _ = raise Fail "not CNF -- expected atom"
fun metis_literal_from_atp type_enc (AConn (ANot, [phi])) =
    (false, metis_atom_from_atp type_enc phi)
  | metis_literal_from_atp type_enc phi =
    (true, metis_atom_from_atp type_enc phi)
fun metis_literals_from_atp type_enc (AConn (AOr, phis)) =
    maps (metis_literals_from_atp type_enc) phis
  | metis_literals_from_atp type_enc phi = [metis_literal_from_atp type_enc phi]
fun metis_axiom_from_atp type_enc clauses (Formula (ident, _, phi, _, _)) =
    let
      fun some isa =
        SOME (phi |> metis_literals_from_atp type_enc
                  |> Metis_LiteralSet.fromList
                  |> Metis_Thm.axiom, isa)
    in
      if ident = type_tag_idempotence_helper_name orelse
         String.isPrefix tags_sym_formula_prefix ident then
        Isa_Reflexive_or_Trivial |> some
      else if String.isPrefix conjecture_prefix ident then
        NONE
      else if String.isPrefix helper_prefix ident then
        case (String.isSuffix typed_helper_suffix ident,
              space_explode "_" ident) of
          (needs_fairly_sound, _ :: const :: j :: _) =>
          nth ((const, needs_fairly_sound)
               |> AList.lookup (op =) helper_table |> the)
              (the (Int.fromString j) - 1)
          |> prepare_helper
          |> Isa_Raw |> some
        | _ => raise Fail ("malformed helper identifier " ^ quote ident)
      else case try (unprefix fact_prefix) ident of
        SOME s =>
        let val s = s |> space_explode "_" |> tl |> space_implode "_"
          in
          case Int.fromString s of
            SOME j =>
            Meson.make_meta_clause (snd (nth clauses j)) |> Isa_Raw |> some
          | NONE =>
            if String.isPrefix lam_fact_prefix (unascii_of s) then
              Isa_Lambda_Lifted |> some
            else
              raise Fail ("malformed fact identifier " ^ quote ident)
        end
      | NONE => TrueI |> Isa_Raw |> some
    end
  | metis_axiom_from_atp _ _ _ = raise Fail "not CNF -- expected formula"

fun eliminate_lam_wrappers (Const (@{const_name Metis.lambda}, _) $ t) =
    eliminate_lam_wrappers t
  | eliminate_lam_wrappers (t $ u) =
    eliminate_lam_wrappers t $ eliminate_lam_wrappers u
  | eliminate_lam_wrappers (Abs (s, T, t)) =
    Abs (s, T, eliminate_lam_wrappers t)
  | eliminate_lam_wrappers t = t

(* Function to generate metis clauses, including comb and type clauses *)
fun prepare_metis_problem ctxt type_enc lam_trans conj_clauses fact_clauses =
  let
    val (conj_clauses, fact_clauses) =
      if polymorphism_of_type_enc type_enc = Polymorphic then
        (conj_clauses, fact_clauses)
      else
        conj_clauses @ fact_clauses
        |> map (pair 0)
        |> rpair (ctxt |> Config.put Monomorph.keep_partial_instances false)
        |-> Monomorph.monomorph atp_schematic_consts_of
        |> fst |> chop (length conj_clauses)
        |> pairself (maps (map (zero_var_indexes o snd)))
    val num_conjs = length conj_clauses
    val clauses =
      map2 (fn j => pair (Int.toString j, (Local, General)))
           (0 upto num_conjs - 1) conj_clauses @
      map2 (fn j => pair (Int.toString (num_conjs + j), (Local, General)))
           (0 upto length fact_clauses - 1) fact_clauses
    val (old_skolems, props) =
      fold_rev (fn (name, th) => fn (old_skolems, props) =>
                   th |> prop_of |> Logic.strip_imp_concl
                      |> conceal_old_skolem_terms (length clauses) old_skolems
                      ||> (lam_trans = liftingN orelse lam_trans = lam_liftingN)
                          ? eliminate_lam_wrappers
                      ||> (fn prop => (name, prop) :: props))
               clauses ([], [])
    (*
    val _ =
      tracing ("PROPS:\n" ^
               cat_lines (map (Syntax.string_of_term ctxt o snd) props))
    *)
    val lam_trans = if lam_trans = combsN then no_lamsN else lam_trans
    val (atp_problem, _, _, lifted, sym_tab) =
      prepare_atp_problem ctxt CNF Hypothesis Axiom type_enc false lam_trans
                          false false [] @{prop False} props
    (*
    val _ = tracing ("ATP PROBLEM: " ^
                     cat_lines (lines_for_atp_problem CNF atp_problem))
    *)
    (* "rev" is for compatibility with existing proof scripts. *)
    val axioms =
      atp_problem
      |> maps (map_filter (metis_axiom_from_atp type_enc clauses) o snd) |> rev
  in (sym_tab, axioms, (lifted, old_skolems)) end

end;
