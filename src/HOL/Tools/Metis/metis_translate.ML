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

  datatype isa_thm =
    Isa_Reflexive_or_Trivial |
    Isa_Raw of thm

  val metis_equal : string
  val metis_predicator : string
  val metis_app_op : string
  val metis_type_tag : string
  val metis_generated_var_prefix : string
  val trace : bool Config.T
  val verbose : bool Config.T
  val trace_msg : Proof.context -> (unit -> string) -> unit
  val verbose_warning : Proof.context -> string -> unit
  val metis_name_table : ((string * int) * (string * bool)) list
  val reveal_old_skolem_terms : (string * term) list -> term -> term
  val prepare_metis_problem :
    Proof.context -> string -> thm list -> thm list
    -> int Symtab.table * (Metis_Thm.thm * isa_thm) list * (string * term) list
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

val trace = Attrib.setup_config_bool @{binding metis_trace} (K false)
val verbose = Attrib.setup_config_bool @{binding metis_verbose} (K true)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()
fun verbose_warning ctxt msg =
  if Config.get ctxt verbose then warning ("Metis: " ^ msg) else ()

val metis_name_table =
  [((tptp_equal, 2), (metis_equal, false)),
   ((tptp_old_equal, 2), (metis_equal, false)),
   ((prefixed_predicator_name, 1), (metis_predicator, false)),
   ((prefixed_app_op_name, 2), (metis_app_op, false)),
   ((prefixed_type_tag_name, 2), (metis_type_tag, true))]

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
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

datatype isa_thm =
  Isa_Reflexive_or_Trivial |
  Isa_Raw of thm

val proxy_defs = map (fst o snd o snd) proxy_table
val prepare_helper =
  Meson.make_meta_clause #> rewrite_rule (map safe_mk_meta_eq proxy_defs)

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
    let
      fun some isa =
        SOME (phi |> metis_literals_from_atp |> Metis_LiteralSet.fromList
                  |> Metis_Thm.axiom, isa)
    in
      if ident = type_tag_idempotence_helper_name orelse
         String.isPrefix lightweight_tags_sym_formula_prefix ident then
        Isa_Reflexive_or_Trivial |> some
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
      else case try (unprefix conjecture_prefix) ident of
        SOME s =>
        let val j = the (Int.fromString s) in
          if j = length clauses then NONE
          else Meson.make_meta_clause (nth clauses j) |> Isa_Raw |> some
        end
      | NONE => TrueI |> Isa_Raw |> some
    end
  | metis_axiom_from_atp _ _ = raise Fail "not CNF -- expected formula"

(* Function to generate metis clauses, including comb and type clauses *)
fun prepare_metis_problem ctxt type_sys conj_clauses fact_clauses =
  let
    val type_sys = type_sys_from_string type_sys
    val explicit_apply = NONE
    val clauses =
      conj_clauses @ fact_clauses
      |> (if polymorphism_of_type_sys type_sys = Polymorphic then
            I
          else
            map (pair 0)
            #> rpair ctxt
            #-> Monomorph.monomorph Monomorph.all_schematic_consts_of
            #> fst #> maps (map (zero_var_indexes o snd)))
    val (old_skolems, props) =
      fold_rev (fn clause => fn (old_skolems, props) =>
                   clause |> prop_of |> Logic.strip_imp_concl
                          |> conceal_old_skolem_terms (length clauses)
                                                      old_skolems
                          ||> (fn prop => prop :: props))
           clauses ([], [])
(*
val _ = tracing ("PROPS:\n" ^ cat_lines (map (Syntax.string_of_term ctxt) props))
*)
    val (atp_problem, _, _, _, _, _, sym_tab) =
      prepare_atp_problem ctxt CNF Hypothesis Axiom type_sys explicit_apply
                          false false props @{prop False} []
(*
val _ = tracing ("ATP PROBLEM: " ^ cat_lines (tptp_lines_for_atp_problem CNF atp_problem))
*)
    (* "rev" is for compatibility *)
    val axioms =
      atp_problem |> maps (map_filter (metis_axiom_from_atp clauses) o snd)
                  |> rev
  in (sym_tab, axioms, old_skolems) end

end;
