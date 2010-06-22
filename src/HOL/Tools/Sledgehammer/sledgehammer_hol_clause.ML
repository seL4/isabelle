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

  val type_of_combterm : combterm -> combtyp
  val strip_combterm_comb : combterm -> combterm * combterm list
  val literals_of_term : theory -> term -> literal list * typ list
  val conceal_skolem_somes :
    int -> (string * term) list -> term -> (string * term) list * term
  exception TRIVIAL of unit
  val make_conjecture_clauses : theory -> thm list -> hol_clause list
  val make_axiom_clauses : theory -> cnf_thm list -> (string * hol_clause) list
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

end;
