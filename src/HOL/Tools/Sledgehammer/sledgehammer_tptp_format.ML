(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_tptp_format.ML
    Author:     Jia Meng, NICTA
    Author:     Jasmin Blanchette, TU Muenchen

TPTP syntax.
*)

signature SLEDGEHAMMER_TPTP_FORMAT =
sig
  type name_pool = Sledgehammer_FOL_Clause.name_pool
  type type_literal = Sledgehammer_FOL_Clause.type_literal
  type classrel_clause = Sledgehammer_FOL_Clause.classrel_clause
  type arity_clause = Sledgehammer_FOL_Clause.arity_clause
  type hol_clause = Sledgehammer_HOL_Clause.hol_clause

  val tptp_of_type_literal :
    bool -> type_literal -> name_pool option -> string * name_pool option
  val write_tptp_file :
    bool -> bool -> bool -> Path.T
    -> hol_clause list * hol_clause list * hol_clause list * hol_clause list
       * classrel_clause list * arity_clause list
    -> name_pool option * int
end;

structure Sledgehammer_TPTP_Format : SLEDGEHAMMER_TPTP_FORMAT =
struct

open Sledgehammer_Util
open Sledgehammer_FOL_Clause
open Sledgehammer_HOL_Clause

val clause_prefix = "cls_"
val arity_clause_prefix = "clsarity_"

fun paren_pack [] = ""
  | paren_pack strings = "(" ^ commas strings ^ ")"

fun string_of_fol_type (TyVar sp) pool = nice_name sp pool
  | string_of_fol_type (TyFree sp) pool = nice_name sp pool
  | string_of_fol_type (TyConstr (sp, tys)) pool =
    let
      val (s, pool) = nice_name sp pool
      val (ss, pool) = pool_map string_of_fol_type tys pool
    in (s ^ paren_pack ss, pool) end

(* True if the constant ever appears outside of the top-level position in
   literals. If false, the constant always receives all of its arguments and is
   used as a predicate. *)
fun needs_hBOOL explicit_apply const_needs_hBOOL c =
  explicit_apply orelse the_default false (Symtab.lookup const_needs_hBOOL c)

fun head_needs_hBOOL explicit_apply const_needs_hBOOL
                     (CombConst ((c, _), _, _)) =
    needs_hBOOL explicit_apply const_needs_hBOOL c
  | head_needs_hBOOL _ _ _ = true

fun wrap_type full_types (s, ty) pool =
  if full_types then
    let val (s', pool) = string_of_fol_type ty pool in
      (type_wrapper_name ^ paren_pack [s, s'], pool)
    end
  else
    (s, pool)

fun wrap_type_if full_types explicit_apply cnh (head, s, tp) =
  if head_needs_hBOOL explicit_apply cnh head then
    wrap_type full_types (s, tp)
  else
    pair s

fun apply ss = "hAPP" ^ paren_pack ss;

fun rev_apply (v, []) = v
  | rev_apply (v, arg::args) = apply [rev_apply (v, args), arg];

fun string_apply (v, args) = rev_apply (v, rev args)

fun min_arity_of const_min_arity = the_default 0 o Symtab.lookup const_min_arity

(* Apply an operator to the argument strings, using either the "apply" operator
   or direct function application. *)
fun string_of_application full_types cma (CombConst ((s, s'), _, tvars), args)
                          pool =
    let
      val s = if s = "equal" then "c_fequal" else s
      val nargs = min_arity_of cma s
      val args1 = List.take (args, nargs)
        handle Subscript =>
               raise Fail (quote s ^ " has arity " ^ Int.toString nargs ^
                           " but is applied to " ^ commas (map quote args))
      val args2 = List.drop (args, nargs)
      val (targs, pool) = if full_types then ([], pool)
                          else pool_map string_of_fol_type tvars pool
      val (s, pool) = nice_name (s, s') pool
    in (string_apply (s ^ paren_pack (args1 @ targs), args2), pool) end
  | string_of_application _ _ (CombVar (name, _), args) pool =
    nice_name name pool |>> (fn s => string_apply (s, args))

fun string_of_combterm (params as (full_types, explicit_apply, cma, cnh)) t
                       pool =
  let
    val (head, args) = strip_combterm_comb t
    val (ss, pool) = pool_map (string_of_combterm params) args pool
    val (s, pool) = string_of_application full_types cma (head, ss) pool
  in
    wrap_type_if full_types explicit_apply cnh (head, s, type_of_combterm t)
                 pool
  end

(*Boolean-valued terms are here converted to literals.*)
fun boolify params c =
  string_of_combterm params c #>> prefix "hBOOL" o paren_pack o single

fun string_of_predicate (params as (_, explicit_apply, _, cnh)) t =
  case #1 (strip_combterm_comb t) of
    CombConst ((s, _), _, _) =>
    (if needs_hBOOL explicit_apply cnh s then boolify else string_of_combterm)
        params t
  | _ => boolify params t

fun tptp_of_equality params pos (t1, t2) =
  pool_map (string_of_combterm params) [t1, t2]
  #>> space_implode (if pos then " = " else " != ")

fun tptp_sign true s = s
  | tptp_sign false s = "~ " ^ s

fun tptp_literal params
        (Literal (pos, CombApp (CombApp (CombConst (("equal", _), _, _), t1),
                                         t2))) =
    tptp_of_equality params pos (t1, t2)
  | tptp_literal params (Literal (pos, pred)) =
    string_of_predicate params pred #>> tptp_sign pos
 
fun tptp_of_type_literal pos (TyLitVar (s, name)) =
    nice_name name #>> (fn s' => tptp_sign pos (s ^ "(" ^ s' ^ ")"))
  | tptp_of_type_literal pos (TyLitFree (s, name)) =
    nice_name name #>> (fn s' => tptp_sign pos (s ^ "(" ^ s' ^ ")"))

(* Given a clause, returns its literals paired with a list of literals
   concerning TFrees; the latter should only occur in conjecture clauses. *)
fun tptp_type_literals params pos (HOLClause {literals, ctypes_sorts, ...})
                       pool =
  let
    val (lits, pool) = pool_map (tptp_literal params) literals pool
    val (tylits, pool) = pool_map (tptp_of_type_literal pos)
                                  (type_literals_for_types ctypes_sorts) pool
  in ((lits, tylits), pool) end

fun tptp_cnf name kind formula =
  "cnf(" ^ name ^ ", " ^ kind ^ ",\n    " ^ formula ^ ").\n"

fun tptp_raw_clause strings = "(" ^ space_implode " | " strings ^ ")"

val tptp_tfree_clause =
  tptp_cnf "tfree_tcs" "negated_conjecture" o tptp_raw_clause o single

fun tptp_classrel_literals sub sup =
  let val tvar = "(T)" in
    tptp_raw_clause [tptp_sign false (sub ^ tvar), tptp_sign true (sup ^ tvar)]
  end

fun tptp_clause params (cls as HOLClause {axiom_name, clause_id, kind, ...})
                pool =
  let
    val ((lits, tylits), pool) =
      tptp_type_literals params (kind = Conjecture) cls pool
    val name = clause_prefix ^ ascii_of axiom_name ^ "_" ^
               Int.toString clause_id
    val cnf =
      case kind of
        Axiom => tptp_cnf name "axiom" (tptp_raw_clause (tylits @ lits))
      | Conjecture => tptp_cnf name "negated_conjecture" (tptp_raw_clause lits)
  in ((cnf, tylits), pool) end

fun tptp_classrel_clause (ClassrelClause {axiom_name, subclass, superclass,
                                          ...}) =
  tptp_cnf axiom_name "axiom" (tptp_classrel_literals subclass superclass)

fun tptp_of_arity_literal (TConsLit (c, t, args)) =
    tptp_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | tptp_of_arity_literal (TVarLit (c, str)) =
    tptp_sign false (make_type_class c ^ "(" ^ str ^ ")")

fun tptp_arity_clause (ArityClause {axiom_name, conclLit, premLits, ...}) =
  tptp_cnf (arity_clause_prefix ^ ascii_of axiom_name) "axiom"
           (tptp_raw_clause (map tptp_of_arity_literal (conclLit :: premLits)))

(*Find the minimal arity of each function mentioned in the term. Also, note which uses
  are not at top level, to see if hBOOL is needed.*)
fun count_constants_term toplev t (const_min_arity, const_needs_hBOOL) =
  let
    val (head, args) = strip_combterm_comb t
    val n = length args
    val (const_min_arity, const_needs_hBOOL) =
      (const_min_arity, const_needs_hBOOL)
      |> fold (count_constants_term false) args
  in
    case head of
      CombConst ((a, _), _, _) => (*predicate or function version of "equal"?*)
        let val a = if a="equal" andalso not toplev then "c_fequal" else a
        in
          (const_min_arity |> Symtab.map_default (a, n) (Integer.min n),
           const_needs_hBOOL |> not toplev ? Symtab.update (a, true))
        end
      | _ => (const_min_arity, const_needs_hBOOL)
  end
fun count_constants_lit (Literal (_, t)) = count_constants_term true t
fun count_constants_clause (HOLClause {literals, ...}) =
  fold count_constants_lit literals
fun count_constants explicit_apply
                    (conjectures, _, extra_clauses, helper_clauses, _, _) =
  (Symtab.empty, Symtab.empty)
  |> (if explicit_apply then
        I
      else
        fold (fold count_constants_clause)
             [conjectures, extra_clauses, helper_clauses])

fun write_tptp_file readable_names full_types explicit_apply file clauses =
  let
    fun section _ [] = []
      | section name ss =
        "\n% " ^ name ^ plural_s (length ss) ^ " (" ^ Int.toString (length ss) ^
        ")\n" :: ss
    val pool = empty_name_pool readable_names
    val (conjectures, axclauses, _, helper_clauses,
      classrel_clauses, arity_clauses) = clauses
    val (cma, cnh) = count_constants explicit_apply clauses
    val params = (full_types, explicit_apply, cma, cnh)
    val ((conjecture_clss, tfree_litss), pool) =
      pool_map (tptp_clause params) conjectures pool |>> ListPair.unzip
    val tfree_clss = map tptp_tfree_clause (fold (union (op =)) tfree_litss [])
    val (ax_clss, pool) =
      pool_map (apfst fst oo tptp_clause params) axclauses pool
    val classrel_clss = map tptp_classrel_clause classrel_clauses
    val arity_clss = map tptp_arity_clause arity_clauses
    val (helper_clss, pool) = pool_map (apfst fst oo tptp_clause params)
                                       helper_clauses pool
    val conjecture_offset =
      length ax_clss + length classrel_clss + length arity_clss
      + length helper_clss
    val _ =
      File.write_list file
          ("% This file was generated by Isabelle (most likely Sledgehammer)\n\
           \% " ^ timestamp () ^ "\n" ::
           section "Relevant fact" ax_clss @
           section "Class relationship" classrel_clss @
           section "Arity declaration" arity_clss @
           section "Helper fact" helper_clss @
           section "Conjecture" conjecture_clss @
           section "Type variable" tfree_clss)
  in (pool, conjecture_offset) end

end;
