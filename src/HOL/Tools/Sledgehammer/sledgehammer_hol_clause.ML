(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_hol_clause.ML
    Author:     Jia Meng, NICTA
    Author:     Jasmin Blanchette, TU Muenchen

FOL clauses translated from HOL formulae.
*)

signature SLEDGEHAMMER_HOL_CLAUSE =
sig
  type name = Sledgehammer_FOL_Clause.name
  type name_pool = Sledgehammer_FOL_Clause.name_pool
  type kind = Sledgehammer_FOL_Clause.kind
  type fol_type = Sledgehammer_FOL_Clause.fol_type
  type classrel_clause = Sledgehammer_FOL_Clause.classrel_clause
  type arity_clause = Sledgehammer_FOL_Clause.arity_clause
  type axiom_name = string
  type polarity = bool
  type hol_clause_id = int

  datatype combterm =
    CombConst of name * fol_type * fol_type list (* Const and Free *) |
    CombVar of name * fol_type |
    CombApp of combterm * combterm
  datatype literal = Literal of polarity * combterm
  datatype hol_clause =
    HOLClause of {clause_id: hol_clause_id, axiom_name: axiom_name, th: thm,
                  kind: kind, literals: literal list, ctypes_sorts: typ list}

  val type_of_combterm : combterm -> fol_type
  val strip_combterm_comb : combterm -> combterm * combterm list
  val literals_of_term : theory -> term -> literal list * typ list
  val conceal_skolem_somes :
    int -> (string * term) list -> term -> (string * term) list * term
  exception TRIVIAL
  val make_conjecture_clauses : bool -> theory -> thm list -> hol_clause list
  val make_axiom_clauses : bool -> theory ->
       (thm * (axiom_name * hol_clause_id)) list -> (axiom_name * hol_clause) list
  val type_wrapper_name : string
  val get_helper_clauses :
    bool -> theory -> bool -> hol_clause list
      -> (thm * (axiom_name * hol_clause_id)) list -> hol_clause list
  val write_tptp_file : bool -> bool -> bool -> Path.T ->
    hol_clause list * hol_clause list * hol_clause list * hol_clause list *
    classrel_clause list * arity_clause list -> name_pool option * int
  val write_dfg_file : bool -> bool -> Path.T ->
    hol_clause list * hol_clause list * hol_clause list * hol_clause list *
    classrel_clause list * arity_clause list -> name_pool option * int
end

structure Sledgehammer_HOL_Clause : SLEDGEHAMMER_HOL_CLAUSE =
struct

open Sledgehammer_Util
open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor

fun min_arity_of const_min_arity c = the_default 0 (Symtab.lookup const_min_arity c);

(*True if the constant ever appears outside of the top-level position in literals.
  If false, the constant always receives all of its arguments and is used as a predicate.*)
fun needs_hBOOL explicit_apply const_needs_hBOOL c =
  explicit_apply orelse
    the_default false (Symtab.lookup const_needs_hBOOL c);


(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

type axiom_name = string;
type polarity = bool;
type hol_clause_id = int;

datatype combterm =
  CombConst of name * fol_type * fol_type list (* Const and Free *) |
  CombVar of name * fol_type |
  CombApp of combterm * combterm

datatype literal = Literal of polarity * combterm;

datatype hol_clause =
  HOLClause of {clause_id: hol_clause_id, axiom_name: axiom_name, th: thm,
                kind: kind, literals: literal list, ctypes_sorts: typ list};


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

fun type_of dfg (Type (a, Ts)) =
    let val (folTypes,ts) = types_of dfg Ts in
      (TyConstr (`(make_fixed_type_const dfg) a, folTypes), ts)
    end
  | type_of _ (tp as TFree (a, _)) = (TyFree (`make_fixed_type_var a), [tp])
  | type_of _ (tp as TVar (x, _)) =
    (TyVar (make_schematic_type_var x, string_of_indexname x), [tp])
and types_of dfg Ts =
      let val (folTyps,ts) = ListPair.unzip (map (type_of dfg) Ts)
      in  (folTyps, union_all ts)  end;

(* same as above, but no gathering of sort information *)
fun simp_type_of dfg (Type (a, Ts)) =
      TyConstr (`(make_fixed_type_const dfg) a, map (simp_type_of dfg) Ts)
  | simp_type_of _ (TFree (a, _)) = TyFree (`make_fixed_type_var a)
  | simp_type_of _ (TVar (x, _)) =
    TyVar (make_schematic_type_var x, string_of_indexname x);


(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of dfg thy (Const (c, T)) =
      let
        val (tp, ts) = type_of dfg T
        val tvar_list =
          (if String.isPrefix skolem_theory_name c then
             [] |> Term.add_tvarsT T |> map TVar
           else
             (c, T) |> Sign.const_typargs thy)
          |> map (simp_type_of dfg)
        val c' = CombConst (`(make_fixed_const dfg) c, tp, tvar_list)
      in  (c',ts)  end
  | combterm_of dfg _ (Free(v, T)) =
      let val (tp,ts) = type_of dfg T
          val v' = CombConst (`make_fixed_var v, tp, [])
      in  (v',ts)  end
  | combterm_of dfg _ (Var(v, T)) =
      let val (tp,ts) = type_of dfg T
          val v' = CombVar ((make_schematic_var v, string_of_indexname v), tp)
      in  (v',ts)  end
  | combterm_of dfg thy (P $ Q) =
      let val (P',tsP) = combterm_of dfg thy P
          val (Q',tsQ) = combterm_of dfg thy Q
      in  (CombApp(P',Q'), union (op =) tsP tsQ)  end
  | combterm_of _ _ (t as Abs _) = raise CLAUSE ("HOL clause", t);

fun predicate_of dfg thy ((@{const Not} $ P), polarity) = predicate_of dfg thy (P, not polarity)
  | predicate_of dfg thy (t,polarity) = (combterm_of dfg thy (Envir.eta_contract t), polarity);

fun literals_of_term1 dfg thy args (@{const Trueprop} $ P) = literals_of_term1 dfg thy args P
  | literals_of_term1 dfg thy args (@{const "op |"} $ P $ Q) =
      literals_of_term1 dfg thy (literals_of_term1 dfg thy args P) Q
  | literals_of_term1 dfg thy (lits,ts) P =
      let val ((pred,ts'),pol) = predicate_of dfg thy (P,true)
      in
          (Literal(pol,pred)::lits, union (op =) ts ts')
      end;

fun literals_of_term_dfg dfg thy P = literals_of_term1 dfg thy ([],[]) P;
val literals_of_term = literals_of_term_dfg false;

fun skolem_name i j num_T_args =
  skolem_prefix ^ (space_implode "_" (map Int.toString [i, j, num_T_args])) ^
  skolem_infix ^ "g"

fun conceal_skolem_somes i skolem_somes t =
  if exists_Const (curry (op =) @{const_name skolem_id} o fst) t then
    let
      fun aux skolem_somes
              (t as (Const (@{const_name skolem_id}, Type (_, [_, T])) $ _)) =
          let
            val (skolem_somes, s) =
              if i = ~1 then
                (skolem_somes, @{const_name undefined})
              else case AList.find (op aconv) skolem_somes t of
                s :: _ => (skolem_somes, s)
              | _ =>
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
fun make_clause dfg thy (clause_id, axiom_name, kind, th) skolem_somes =
  let
    val (skolem_somes, t) =
      th |> prop_of |> conceal_skolem_somes clause_id skolem_somes
    val (lits, ctypes_sorts) = literals_of_term_dfg dfg thy t
  in
    if forall isFalse lits then
      raise TRIVIAL
    else
      (skolem_somes,
       HOLClause {clause_id = clause_id, axiom_name = axiom_name, th = th,
                  kind = kind, literals = lits, ctypes_sorts = ctypes_sorts})
  end

fun add_axiom_clause dfg thy (th, (name, id)) (skolem_somes, clss) =
  let
    val (skolem_somes, cls) =
      make_clause dfg thy (id, name, Axiom, th) skolem_somes
  in (skolem_somes, clss |> not (isTaut cls) ? cons (name, cls)) end

fun make_axiom_clauses dfg thy clauses =
  ([], []) |> fold (add_axiom_clause dfg thy) clauses |> snd

fun make_conjecture_clauses dfg thy =
  let
    fun aux _ _ [] = []
      | aux n skolem_somes (th :: ths) =
        let
          val (skolem_somes, cls) =
            make_clause dfg thy (n, "conjecture", Conjecture, th) skolem_somes
        in cls :: aux (n + 1) skolem_somes ths end
  in aux 0 [] end

(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
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
  case t of
    (CombApp (CombApp (CombConst (("equal", _), _, _), t1), t2)) =>
    (* DFG only: new TPTP prefers infix equality *)
    pool_map (string_of_combterm params) [t1, t2]
    #>> prefix "equal" o paren_pack
  | _ =>
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


(*** DFG format ***)

fun dfg_literal params (Literal (pos, pred)) =
  string_of_predicate params pred #>> dfg_sign pos

fun dfg_type_literals params pos (HOLClause {literals, ctypes_sorts, ...}) =
  pool_map (dfg_literal params) literals
  #>> rpair (map (dfg_of_type_literal pos)
                 (type_literals_for_types ctypes_sorts))

fun get_uvars (CombConst _) vars pool = (vars, pool)
  | get_uvars (CombVar (name, _)) vars pool =
    nice_name name pool |>> (fn var => var :: vars)
  | get_uvars (CombApp (P, Q)) vars pool =
    let val (vars, pool) = get_uvars P vars pool in get_uvars Q vars pool end

fun get_uvars_l (Literal (_, c)) = get_uvars c [];

fun dfg_vars (HOLClause {literals, ...}) =
  pool_map get_uvars_l literals #>> union_all

fun dfg_clause params (cls as HOLClause {axiom_name, clause_id, kind,
                                         ctypes_sorts, ...}) pool =
  let
    val ((lits, tylits), pool) =
      dfg_type_literals params (kind = Conjecture) cls pool
    val (vars, pool) = dfg_vars cls pool
    val tvars = get_tvar_strs ctypes_sorts
  in
    ((gen_dfg_cls (clause_id, axiom_name, kind, lits, tylits, tvars @ vars),
      tylits), pool)
  end


(** For DFG format: accumulate function and predicate declarations **)

fun add_types tvars = fold add_fol_type_funcs tvars

fun add_decls (full_types, explicit_apply, cma, cnh)
              (CombConst ((c, _), ctp, tvars)) (funcs, preds) =
      (if c = "equal" then
         (add_types tvars funcs, preds)
       else
         let val arity = min_arity_of cma c
             val ntys = if not full_types then length tvars else 0
             val addit = Symtab.update(c, arity + ntys)
         in
             if needs_hBOOL explicit_apply cnh c then
               (add_types tvars (addit funcs), preds)
             else
               (add_types tvars funcs, addit preds)
         end) |>> full_types ? add_fol_type_funcs ctp
  | add_decls _ (CombVar (_, ctp)) (funcs, preds) =
      (add_fol_type_funcs ctp funcs, preds)
  | add_decls params (CombApp (P, Q)) decls =
      decls |> add_decls params P |> add_decls params Q

fun add_literal_decls params (Literal (_, c)) = add_decls params c

fun add_clause_decls params (HOLClause {literals, ...}) decls =
    fold (add_literal_decls params) literals decls
    handle Symtab.DUP a => error ("function " ^ a ^ " has multiple arities")

fun decls_of_clauses (params as (full_types, explicit_apply, _, _)) clauses
                     arity_clauses =
  let
    val functab =
      init_functab
      |> fold Symtab.update [(type_wrapper_name, 2), ("hAPP", 2),
                             ("tc_bool", 0)]
      val predtab = Symtab.empty |> Symtab.update ("hBOOL", 1)
      val (functab, predtab) =
        (functab, predtab) |> fold (add_clause_decls params) clauses
                           |>> fold add_arity_clause_funcs arity_clauses
  in (Symtab.dest functab, Symtab.dest predtab) end

fun add_clause_preds (HOLClause {ctypes_sorts, ...}) preds =
  fold add_type_sort_preds ctypes_sorts preds
  handle Symtab.DUP a => error ("predicate " ^ a ^ " has multiple arities")

(*Higher-order clauses have only the predicates hBOOL and type classes.*)
fun preds_of_clauses clauses clsrel_clauses arity_clauses =
  Symtab.empty
  |> fold add_clause_preds clauses
  |> fold add_arity_clause_preds arity_clauses
  |> fold add_classrel_clause_preds clsrel_clauses
  |> Symtab.dest

(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)

val init_counters =
  Symtab.make [("c_COMBI", 0), ("c_COMBK", 0), ("c_COMBB", 0), ("c_COMBC", 0),
               ("c_COMBS", 0)];

fun count_combterm (CombConst ((c, _), _, _)) =
    Symtab.map_entry c (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = count_combterm t1 #> count_combterm t2

fun count_literal (Literal (_, t)) = count_combterm t

fun count_clause (HOLClause {literals, ...}) = fold count_literal literals

fun cnf_helper_thms thy = cnf_rules_pairs thy o map (`Thm.get_name_hint)

fun get_helper_clauses dfg thy isFO conjectures axcls =
  if isFO then
    []
  else
    let
        val axclauses = map snd (make_axiom_clauses dfg thy axcls)
        val ct = init_counters
                 |> fold (fold count_clause) [conjectures, axclauses]
        fun needed c = the (Symtab.lookup ct c) > 0
        val IK = if needed "c_COMBI" orelse needed "c_COMBK"
                 then cnf_helper_thms thy [@{thm COMBI_def}, @{thm COMBK_def}]
                 else []
        val BC = if needed "c_COMBB" orelse needed "c_COMBC"
                 then cnf_helper_thms thy [@{thm COMBB_def}, @{thm COMBC_def}]
                 else []
        val S = if needed "c_COMBS" then cnf_helper_thms thy [@{thm COMBS_def}]
                else []
        val other = cnf_helper_thms thy [@{thm fequal_imp_equal},
                                         @{thm equal_imp_fequal}]
    in map snd (make_axiom_clauses dfg thy (other @ IK @ BC @ S)) end

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

fun display_arity explicit_apply const_needs_hBOOL (c,n) =
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

fun header () =
  "% This file was generated by Isabelle (most likely Sledgehammer)\n" ^
  "% " ^ timestamp () ^ "\n"

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
          (header () ::
           section "Relevant fact" ax_clss @
           section "Class relationship" classrel_clss @
           section "Arity declaration" arity_clss @
           section "Helper fact" helper_clss @
           section "Conjecture" conjecture_clss @
           section "Type variable" tfree_clss)
  in (pool, conjecture_offset) end

(* DFG format *)

fun dfg_tfree_predicate s = (first_field "(" s |> the |> fst, 1)

fun write_dfg_file full_types explicit_apply file clauses =
  let
    (* Some of the helper functions below are not name-pool-aware. However,
       there's no point in adding name pool support if the DFG format is on its
       way out anyway. *)
    val pool = NONE
    val (conjectures, axclauses, _, helper_clauses,
      classrel_clauses, arity_clauses) = clauses
    val (cma, cnh) = count_constants explicit_apply clauses
    val params = (full_types, explicit_apply, cma, cnh)
    val ((conjecture_clss, tfree_litss), pool) =
      pool_map (dfg_clause params) conjectures pool |>> ListPair.unzip
    val tfree_lits = union_all tfree_litss
    val problem_name = Path.implode (Path.base file)
    val (axstrs, pool) = pool_map (apfst fst oo dfg_clause params) axclauses pool
    val tfree_clss = map dfg_tfree_clause tfree_lits
    val tfree_preds = map dfg_tfree_predicate tfree_lits
    val (helper_clauses_strs, pool) =
      pool_map (apfst fst oo dfg_clause params) helper_clauses pool
    val (funcs, cl_preds) =
      decls_of_clauses params (helper_clauses @ conjectures @ axclauses) arity_clauses
    val ty_preds = preds_of_clauses axclauses classrel_clauses arity_clauses
    val preds = tfree_preds @ cl_preds @ ty_preds
    val conjecture_offset =
      length axclauses + length classrel_clauses + length arity_clauses
      + length helper_clauses
    val _ =
      File.write_list file
          (header () ::
           string_of_start problem_name ::
           string_of_descrip problem_name ::
           string_of_symbols (string_of_funcs funcs)
                             (string_of_preds preds) ::
           "list_of_clauses(axioms, cnf).\n" ::
           axstrs @
           map dfg_classrel_clause classrel_clauses @
           map dfg_arity_clause arity_clauses @
           helper_clauses_strs @
           ["end_of_list.\n\nlist_of_clauses(conjectures, cnf).\n"] @
           conjecture_clss @
           tfree_clss @
           ["end_of_list.\n\n",
            "end_problem.\n"])
  in (pool, conjecture_offset) end

end;
