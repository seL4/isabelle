(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_hol_clause.ML
    Author:     Jia Meng, NICTA
    Author:     Jasmin Blanchette, TU Muenchen

FOL clauses translated from HOL formulae.
*)

signature SLEDGEHAMMER_HOL_CLAUSE =
sig
  type cnf_thm = Sledgehammer_Fact_Preprocessor.cnf_thm
  type name = Sledgehammer_FOL_Clause.name
  type name_pool = Sledgehammer_FOL_Clause.name_pool
  type kind = Sledgehammer_FOL_Clause.kind
  type fol_type = Sledgehammer_FOL_Clause.fol_type
  type classrel_clause = Sledgehammer_FOL_Clause.classrel_clause
  type arity_clause = Sledgehammer_FOL_Clause.arity_clause
  type polarity = bool

  datatype combterm =
    CombConst of name * fol_type * fol_type list (* Const and Free *) |
    CombVar of name * fol_type |
    CombApp of combterm * combterm
  datatype literal = Literal of polarity * combterm
  datatype hol_clause =
    HOLClause of {clause_id: int, axiom_name: string, th: thm, kind: kind,
                  literals: literal list, ctypes_sorts: typ list}

  val type_of_combterm : combterm -> fol_type
  val strip_combterm_comb : combterm -> combterm * combterm list
  val literals_of_term : theory -> term -> literal list * typ list
  val conceal_skolem_somes :
    int -> (string * term) list -> term -> (string * term) list * term
  exception TRIVIAL
  val make_conjecture_clauses : theory -> thm list -> hol_clause list
  val make_axiom_clauses : theory -> cnf_thm list -> (string * hol_clause) list
  val type_wrapper_name : string
  val get_helper_clauses :
    theory -> bool -> bool -> hol_clause list -> cnf_thm list -> hol_clause list
  val write_tptp_file : bool -> bool -> bool -> Path.T ->
    hol_clause list * hol_clause list * hol_clause list * hol_clause list *
    classrel_clause list * arity_clause list -> name_pool option * int
end

structure Sledgehammer_HOL_Clause : SLEDGEHAMMER_HOL_CLAUSE =
struct

open Sledgehammer_Util
open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor

fun min_arity_of const_min_arity c =
  the_default 0 (Symtab.lookup const_min_arity c)

(*True if the constant ever appears outside of the top-level position in literals.
  If false, the constant always receives all of its arguments and is used as a predicate.*)
fun needs_hBOOL explicit_apply const_needs_hBOOL c =
  explicit_apply orelse the_default false (Symtab.lookup const_needs_hBOOL c)


(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

type polarity = bool

datatype combterm =
  CombConst of name * fol_type * fol_type list (* Const and Free *) |
  CombVar of name * fol_type |
  CombApp of combterm * combterm

datatype literal = Literal of polarity * combterm;

datatype hol_clause =
  HOLClause of {clause_id: int, axiom_name: string, th: thm, kind: kind,
                literals: literal list, ctypes_sorts: typ list}


(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

fun isFalse (Literal (pol, CombConst ((c, _), _, _))) =
      (pol andalso c = "c_False") orelse (not pol andalso c = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol, CombConst ((c, _), _, _))) =
      (pol andalso c = "c_True") orelse
      (not pol andalso c = "c_False")
  | isTrue _ = false;

fun isTaut (HOLClause {literals,...}) = exists isTrue literals;

fun type_of (Type (a, Ts)) =
    let val (folTypes,ts) = types_of Ts in
      (TyConstr (`make_fixed_type_const a, folTypes), ts)
    end
  | type_of (tp as TFree (a, _)) = (TyFree (`make_fixed_type_var a), [tp])
  | type_of (tp as TVar (x, _)) =
    (TyVar (make_schematic_type_var x, string_of_indexname x), [tp])
and types_of Ts =
    let val (folTyps, ts) = ListPair.unzip (map type_of Ts) in
      (folTyps, union_all ts)
    end

(* same as above, but no gathering of sort information *)
fun simp_type_of (Type (a, Ts)) =
      TyConstr (`make_fixed_type_const a, map simp_type_of Ts)
  | simp_type_of (TFree (a, _)) = TyFree (`make_fixed_type_var a)
  | simp_type_of (TVar (x, _)) =
    TyVar (make_schematic_type_var x, string_of_indexname x)


(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of thy (Const (c, T)) =
      let
        val (tp, ts) = type_of T
        val tvar_list =
          (if String.isPrefix skolem_theory_name c then
             [] |> Term.add_tvarsT T |> map TVar
           else
             (c, T) |> Sign.const_typargs thy)
          |> map simp_type_of
        val c' = CombConst (`make_fixed_const c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_of _ (Free(v, T)) =
      let val (tp,ts) = type_of T
          val v' = CombConst (`make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_of _ (Var(v, T)) =
      let val (tp,ts) = type_of T
          val v' = CombVar ((make_schematic_var v, string_of_indexname v), tp)
      in  (v',ts)  end
  | combterm_of thy (P $ Q) =
      let val (P', tsP) = combterm_of thy P
          val (Q', tsQ) = combterm_of thy Q
      in  (CombApp (P', Q'), union (op =) tsP tsQ)  end
  | combterm_of _ (t as Abs _) = raise CLAUSE ("HOL clause", t)

fun predicate_of thy ((@{const Not} $ P), polarity) =
    predicate_of thy (P, not polarity)
  | predicate_of thy (t, polarity) =
    (combterm_of thy (Envir.eta_contract t), polarity)

fun literals_of_term1 args thy (@{const Trueprop} $ P) =
    literals_of_term1 args thy P
  | literals_of_term1 args thy (@{const "op |"} $ P $ Q) =
    literals_of_term1 (literals_of_term1 args thy P) thy Q
  | literals_of_term1 (lits, ts) thy P =
    let val ((pred, ts'), pol) = predicate_of thy (P, true) in
      (Literal (pol, pred) :: lits, union (op =) ts ts')
    end
val literals_of_term = literals_of_term1 ([], [])

fun skolem_name i j num_T_args =
  skolem_prefix ^ (space_implode "_" (map Int.toString [i, j, num_T_args])) ^
  skolem_infix ^ "g"

fun conceal_skolem_somes i skolem_somes t =
  if exists_Const (curry (op =) @{const_name skolem_id} o fst) t then
    let
      fun aux skolem_somes
              (t as (Const (@{const_name skolem_id}, Type (_, [_, T])) $ _)) =
          let
            val t = Envir.beta_eta_contract t
            val (skolem_somes, s) =
              if i = ~1 then
                (skolem_somes, @{const_name undefined})
              else case AList.find (op aconv) skolem_somes t of
                s :: _ => (skolem_somes, s)
              | [] =>
                let
                  val s = skolem_theory_name ^ "." ^
                          skolem_name i (length skolem_somes)
                                        (length (Term.add_tvarsT T []))
                in ((s, t) :: skolem_somes, s) end
          in (skolem_somes, Const (s, T)) end
        | aux skolem_somes (t1 $ t2) =
          let
            val (skolem_somes, t1) = aux skolem_somes t1
            val (skolem_somes, t2) = aux skolem_somes t2
          in (skolem_somes, t1 $ t2) end
        | aux skolem_somes (Abs (s, T, t')) =
          let val (skolem_somes, t') = aux skolem_somes t' in
            (skolem_somes, Abs (s, T, t'))
          end
        | aux skolem_somes t = (skolem_somes, t)
    in aux skolem_somes t end
  else
    (skolem_somes, t)

(* Trivial problem, which resolution cannot handle (empty clause) *)
exception TRIVIAL;

(* making axiom and conjecture clauses *)
fun make_clause thy (clause_id, axiom_name, kind, th) skolem_somes =
  let
    val (skolem_somes, t) =
      th |> prop_of |> conceal_skolem_somes clause_id skolem_somes
    val (lits, ctypes_sorts) = literals_of_term thy t
  in
    if forall isFalse lits then
      raise TRIVIAL
    else
      (skolem_somes,
       HOLClause {clause_id = clause_id, axiom_name = axiom_name, th = th,
                  kind = kind, literals = lits, ctypes_sorts = ctypes_sorts})
  end

fun add_axiom_clause thy (th, ((name, id), _ : thm)) (skolem_somes, clss) =
  let
    val (skolem_somes, cls) = make_clause thy (id, name, Axiom, th) skolem_somes
  in (skolem_somes, clss |> not (isTaut cls) ? cons (name, cls)) end

fun make_axiom_clauses thy clauses =
  ([], []) |> fold (add_axiom_clause thy) clauses |> snd

fun make_conjecture_clauses thy =
  let
    fun aux _ _ [] = []
      | aux n skolem_somes (th :: ths) =
        let
          val (skolem_somes, cls) =
            make_clause thy (n, "conjecture", Conjecture, th) skolem_somes
        in cls :: aux (n + 1) skolem_somes ths end
  in aux 0 [] end

(**********************************************************************)
(* convert clause into TPTP format                                    *)
(**********************************************************************)

(*Result of a function type; no need to check that the argument type matches.*)
fun result_type (TyConstr (_, [_, tp2])) = tp2
  | result_type _ = raise Fail "non-function type"

fun type_of_combterm (CombConst (_, tp, _)) = tp
  | type_of_combterm (CombVar (_, tp)) = tp
  | type_of_combterm (CombApp (t1, _)) = result_type (type_of_combterm t1);

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_combterm_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in  stripc(u,[])  end;

val type_wrapper_name = "ti"

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

fun string_apply (v, args) = rev_apply (v, rev args);

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


(*** TPTP format ***)

fun tptp_of_equality params pos (t1, t2) =
  pool_map (string_of_combterm params) [t1, t2]
  #>> space_implode (if pos then " = " else " != ")

fun tptp_literal params
        (Literal (pos, CombApp (CombApp (CombConst (("equal", _), _, _), t1),
                                         t2))) =
    tptp_of_equality params pos (t1, t2)
  | tptp_literal params (Literal (pos, pred)) =
    string_of_predicate params pred #>> tptp_sign pos
 
(* Given a clause, returns its literals paired with a list of literals
   concerning TFrees; the latter should only occur in conjecture clauses. *)
fun tptp_type_literals params pos (HOLClause {literals, ctypes_sorts, ...})
                       pool =
  let
    val (lits, pool) = pool_map (tptp_literal params) literals pool
    val (tylits, pool) = pool_map (tptp_of_type_literal pos)
                                  (type_literals_for_types ctypes_sorts) pool
  in ((lits, tylits), pool) end

fun tptp_clause params (cls as HOLClause {axiom_name, clause_id, kind, ...})
                pool =
  let
    val ((lits, tylits), pool) =
      tptp_type_literals params (kind = Conjecture) cls pool
  in
    ((gen_tptp_cls (clause_id, axiom_name, kind, lits, tylits), tylits), pool)
  end


(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)

fun count_combterm (CombConst ((c, _), _, _)) =
    Symtab.map_entry c (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = count_combterm t1 #> count_combterm t2

fun count_literal (Literal (_, t)) = count_combterm t

fun count_clause (HOLClause {literals, ...}) = fold count_literal literals

val raw_cnf_rules_pairs = map (fn (name, thm) => (thm, ((name, 0), thm)))
fun cnf_helper_thms thy raw =
  map (`Thm.get_name_hint)
  #> (if raw then raw_cnf_rules_pairs else cnf_rules_pairs thy)

val optional_helpers =
  [(["c_COMBI", "c_COMBK"], (false, @{thms COMBI_def COMBK_def})),
   (["c_COMBB", "c_COMBC"], (false, @{thms COMBB_def COMBC_def})),
   (["c_COMBS"], (false, @{thms COMBS_def}))]
val optional_typed_helpers =
  [(["c_True", "c_False"], (true, @{thms True_or_False})),
   (["c_If"], (true, @{thms if_True if_False True_or_False}))]
val mandatory_helpers = @{thms fequal_imp_equal equal_imp_fequal}

val init_counters =
  Symtab.make (maps (maps (map (rpair 0) o fst))
                    [optional_helpers, optional_typed_helpers])

fun get_helper_clauses thy is_FO full_types conjectures axcls =
  let
    val axclauses = map snd (make_axiom_clauses thy axcls)
    val ct = fold (fold count_clause) [conjectures, axclauses] init_counters
    fun is_needed c = the (Symtab.lookup ct c) > 0
    val cnfs =
      (optional_helpers
       |> full_types ? append optional_typed_helpers
       |> maps (fn (ss, (raw, ths)) =>
                   if exists is_needed ss then cnf_helper_thms thy raw ths
                   else []))
      @ (if is_FO then [] else cnf_helper_thms thy false mandatory_helpers)
  in map snd (make_axiom_clauses thy cnfs) end

(*Find the minimal arity of each function mentioned in the term. Also, note which uses
  are not at top level, to see if hBOOL is needed.*)
fun count_constants_term toplev t (const_min_arity, const_needs_hBOOL) =
  let val (head, args) = strip_combterm_comb t
      val n = length args
      val (const_min_arity, const_needs_hBOOL) =
        (const_min_arity, const_needs_hBOOL)
        |> fold (count_constants_term false) args
  in
      case head of
          CombConst ((a, _),_,_) => (*predicate or function version of "equal"?*)
            let val a = if a="equal" andalso not toplev then "c_fequal" else a
            in
              (const_min_arity |> Symtab.map_default (a, n) (Integer.min n),
               const_needs_hBOOL |> not toplev ? Symtab.update (a, true))
            end
        | _ => (const_min_arity, const_needs_hBOOL)
  end;

(*A literal is a top-level term*)
fun count_constants_lit (Literal (_,t)) (const_min_arity, const_needs_hBOOL) =
  count_constants_term true t (const_min_arity, const_needs_hBOOL);

fun count_constants_clause (HOLClause {literals, ...})
                           (const_min_arity, const_needs_hBOOL) =
  fold count_constants_lit literals (const_min_arity, const_needs_hBOOL);

fun display_arity explicit_apply const_needs_hBOOL (c, n) =
  trace_msg (fn () => "Constant: " ^ c ^
                " arity:\t" ^ Int.toString n ^
                (if needs_hBOOL explicit_apply const_needs_hBOOL c then
                   " needs hBOOL"
                 else
                   ""))

fun count_constants explicit_apply
                    (conjectures, _, extra_clauses, helper_clauses, _, _) =
  if not explicit_apply then
     let val (const_min_arity, const_needs_hBOOL) =
          fold count_constants_clause conjectures (Symtab.empty, Symtab.empty)
       |> fold count_constants_clause extra_clauses
       |> fold count_constants_clause helper_clauses
     val _ = app (display_arity explicit_apply const_needs_hBOOL)
                 (Symtab.dest (const_min_arity))
     in (const_min_arity, const_needs_hBOOL) end
  else (Symtab.empty, Symtab.empty);

(* TPTP format *)

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
    val (ax_clss, pool) = pool_map (apfst fst oo tptp_clause params) axclauses
                                   pool
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
