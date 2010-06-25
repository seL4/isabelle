(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_hol_clause.ML
    Author:     Jia Meng, NICTA
    Author:     Jasmin Blanchette, TU Muenchen

FOL clauses translated from HOL formulas.
*)

signature SLEDGEHAMMER_HOL_CLAUSE =
sig
  type cnf_thm = Sledgehammer_Fact_Preprocessor.cnf_thm
  type name = Sledgehammer_FOL_Clause.name
  type name_pool = Sledgehammer_FOL_Clause.name_pool
  type kind = Sledgehammer_FOL_Clause.kind
  type classrel_clause = Sledgehammer_FOL_Clause.classrel_clause
  type arity_clause = Sledgehammer_FOL_Clause.arity_clause
  type polarity = bool

  datatype combtyp =
    TyVar of name |
    TyFree of name |
    TyConstr of name * combtyp list
  datatype combterm =
    CombConst of name * combtyp * combtyp list (* Const and Free *) |
    CombVar of name * combtyp |
    CombApp of combterm * combterm
  datatype literal = Literal of polarity * combterm
  datatype hol_clause =
    HOLClause of {clause_id: int, axiom_name: string, th: thm, kind: kind,
                  literals: literal list, ctypes_sorts: typ list}
  exception TRIVIAL of unit

  val type_of_combterm : combterm -> combtyp
  val strip_combterm_comb : combterm -> combterm * combterm list
  val literals_of_term : theory -> term -> literal list * typ list
  val conceal_skolem_somes :
    int -> (string * term) list -> term -> (string * term) list * term
  val is_quasi_fol_theorem : theory -> thm -> bool
  val make_clause_table : (thm * 'a) list -> (thm * 'a) Termtab.table
  val tfree_classes_of_terms : term list -> string list
  val tvar_classes_of_terms : term list -> string list
  val type_consts_of_terms : theory -> term list -> string list
  val prepare_clauses :
    bool -> thm list -> cnf_thm list -> cnf_thm list -> theory
    -> string vector
       * (hol_clause list * hol_clause list * hol_clause list * hol_clause list
          * classrel_clause list * arity_clause list)
end

structure Sledgehammer_HOL_Clause : SLEDGEHAMMER_HOL_CLAUSE =
struct

open Sledgehammer_Util
open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor

(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

type polarity = bool

datatype combtyp =
  TyVar of name |
  TyFree of name |
  TyConstr of name * combtyp list

datatype combterm =
  CombConst of name * combtyp * combtyp list (* Const and Free *) |
  CombVar of name * combtyp |
  CombApp of combterm * combterm

datatype literal = Literal of polarity * combterm;

datatype hol_clause =
  HOLClause of {clause_id: int, axiom_name: string, th: thm, kind: kind,
                literals: literal list, ctypes_sorts: typ list}

(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

(*Result of a function type; no need to check that the argument type matches.*)
fun result_type (TyConstr (_, [_, tp2])) = tp2
  | result_type _ = raise Fail "non-function type"

fun type_of_combterm (CombConst (_, tp, _)) = tp
  | type_of_combterm (CombVar (_, tp)) = tp
  | type_of_combterm (CombApp (t1, _)) = result_type (type_of_combterm t1)

(*gets the head of a combinator application, along with the list of arguments*)
fun strip_combterm_comb u =
    let fun stripc (CombApp(t,u), ts) = stripc (t, u::ts)
        |   stripc  x =  x
    in stripc(u,[]) end

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

fun is_quasi_fol_theorem thy =
  Meson.is_fol_term thy o snd o conceal_skolem_somes ~1 [] o prop_of

(* Trivial problem, which resolution cannot handle (empty clause) *)
exception TRIVIAL of unit

(* making axiom and conjecture clauses *)
fun make_clause thy (clause_id, axiom_name, kind, th) skolem_somes =
  let
    val (skolem_somes, t) =
      th |> prop_of |> conceal_skolem_somes clause_id skolem_somes
    val (lits, ctypes_sorts) = literals_of_term thy t
  in
    if forall isFalse lits then
      raise TRIVIAL ()
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
  ([], []) |> fold_rev (add_axiom_clause thy) clauses |> snd

fun make_conjecture_clauses thy =
  let
    fun aux _ _ [] = []
      | aux n skolem_somes (th :: ths) =
        let
          val (skolem_somes, cls) =
            make_clause thy (n, "conjecture", Conjecture, th) skolem_somes
        in cls :: aux (n + 1) skolem_somes ths end
  in aux 0 [] end

(** Helper clauses **)

fun count_combterm (CombConst ((c, _), _, _)) =
    Symtab.map_entry c (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = count_combterm t1 #> count_combterm t2
fun count_literal (Literal (_, t)) = count_combterm t
fun count_clause (HOLClause {literals, ...}) = fold count_literal literals

fun raw_cnf_rules_pairs ps = map (fn (name, thm) => (thm, ((name, 0), thm))) ps
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

fun make_clause_table xs =
  fold (Termtab.update o `(prop_of o fst)) xs Termtab.empty


(***************************************************************)
(* Type Classes Present in the Axiom or Conjecture Clauses     *)
(***************************************************************)

fun set_insert (x, s) = Symtab.update (x, ()) s

fun add_classes (sorts, cset) = List.foldl set_insert cset (flat sorts)

(*Remove this trivial type class*)
fun delete_type cset = Symtab.delete_safe (the_single @{sort HOL.type}) cset;

fun tfree_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tfrees) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

fun tvar_classes_of_terms ts =
  let val sorts_list = map (map #2 o OldTerm.term_tvars) ts
  in  Symtab.keys (delete_type (List.foldl add_classes Symtab.empty sorts_list))  end;

(*fold type constructors*)
fun fold_type_consts f (Type (a, Ts)) x = fold (fold_type_consts f) Ts (f (a,x))
  | fold_type_consts _ _ x = x;

(*Type constructors used to instantiate overloaded constants are the only ones needed.*)
fun add_type_consts_in_term thy =
  let
    val const_typargs = Sign.const_typargs thy
    fun aux (Const x) = fold (fold_type_consts set_insert) (const_typargs x)
      | aux (Abs (_, _, u)) = aux u
      | aux (Const (@{const_name skolem_id}, _) $ _) = I
      | aux (t $ u) = aux t #> aux u
      | aux _ = I
  in aux end

fun type_consts_of_terms thy ts =
  Symtab.keys (fold (add_type_consts_in_term thy) ts Symtab.empty);

(* Remove existing axiom clauses from the conjecture clauses, as this can
   dramatically boost an ATP's performance (for some reason). *)
fun subtract_cls ax_clauses =
  filter_out (Termtab.defined (make_clause_table ax_clauses) o prop_of)

(* prepare for passing to writer,
   create additional clauses based on the information from extra_cls *)
fun prepare_clauses full_types goal_cls axcls extra_cls thy =
  let
    val is_FO = forall (Meson.is_fol_term thy o prop_of) goal_cls
    val ccls = subtract_cls extra_cls goal_cls
    val _ = app (fn th => trace_msg (fn _ => Display.string_of_thm_global thy th)) ccls
    val ccltms = map prop_of ccls
    and axtms = map (prop_of o #1) extra_cls
    val subs = tfree_classes_of_terms ccltms
    and supers = tvar_classes_of_terms axtms
    and tycons = type_consts_of_terms thy (ccltms @ axtms)
    (*TFrees in conjecture clauses; TVars in axiom clauses*)
    val conjectures = make_conjecture_clauses thy ccls
    val (_, extra_clauses) = ListPair.unzip (make_axiom_clauses thy extra_cls)
    val (clnames, axiom_clauses) = ListPair.unzip (make_axiom_clauses thy axcls)
    val helper_clauses =
      get_helper_clauses thy is_FO full_types conjectures extra_cls
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val classrel_clauses = make_classrel_clauses thy subs supers'
  in
    (Vector.fromList clnames,
      (conjectures, axiom_clauses, extra_clauses, helper_clauses, classrel_clauses, arity_clauses))
  end

end;
