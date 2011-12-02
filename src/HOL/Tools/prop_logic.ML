(*  Title:      HOL/Tools/prop_logic.ML
    Author:     Tjark Weber
    Copyright   2004-2009

Formulas of propositional logic.
*)

signature PROP_LOGIC =
sig
  datatype prop_formula =
      True
    | False
    | BoolVar of int  (* NOTE: only use indices >= 1 *)
    | Not of prop_formula
    | Or of prop_formula * prop_formula
    | And of prop_formula * prop_formula

  val SNot: prop_formula -> prop_formula
  val SOr: prop_formula * prop_formula -> prop_formula
  val SAnd: prop_formula * prop_formula -> prop_formula
  val simplify: prop_formula -> prop_formula  (* eliminates True/False and double-negation *)

  val indices: prop_formula -> int list  (* set of all variable indices *)
  val maxidx: prop_formula -> int       (* maximal variable index *)

  val exists: prop_formula list -> prop_formula  (* finite disjunction *)
  val all: prop_formula list -> prop_formula  (* finite conjunction *)
  val dot_product: prop_formula list * prop_formula list -> prop_formula

  val is_nnf: prop_formula -> bool  (* returns true iff the formula is in negation normal form *)
  val is_cnf: prop_formula -> bool  (* returns true iff the formula is in conjunctive normal form *)

  val nnf: prop_formula -> prop_formula  (* negation normal form *)
  val cnf: prop_formula -> prop_formula  (* conjunctive normal form *)
  val defcnf: prop_formula -> prop_formula  (* definitional cnf *)

  val eval: (int -> bool) -> prop_formula -> bool  (* semantics *)

  (* propositional representation of HOL terms *)
  val prop_formula_of_term: term -> int Termtab.table -> prop_formula * int Termtab.table
  (* HOL term representation of propositional formulae *)
  val term_of_prop_formula: prop_formula -> term
end;

structure Prop_Logic : PROP_LOGIC =
struct

(* ------------------------------------------------------------------------- *)
(* prop_formula: formulas of propositional logic, built from Boolean         *)
(*               variables (referred to by index) and True/False using       *)
(*               not/or/and                                                  *)
(* ------------------------------------------------------------------------- *)

datatype prop_formula =
    True
  | False
  | BoolVar of int  (* NOTE: only use indices >= 1 *)
  | Not of prop_formula
  | Or of prop_formula * prop_formula
  | And of prop_formula * prop_formula;

(* ------------------------------------------------------------------------- *)
(* The following constructor functions make sure that True and False do not  *)
(* occur within any of the other connectives (i.e. Not, Or, And), and        *)
(* perform double-negation elimination.                                      *)
(* ------------------------------------------------------------------------- *)

fun SNot True = False
  | SNot False = True
  | SNot (Not fm) = fm
  | SNot fm = Not fm;

fun SOr (True, _) = True
  | SOr (_, True) = True
  | SOr (False, fm) = fm
  | SOr (fm, False) = fm
  | SOr (fm1, fm2) = Or (fm1, fm2);

fun SAnd (True, fm) = fm
  | SAnd (fm, True) = fm
  | SAnd (False, _) = False
  | SAnd (_, False) = False
  | SAnd (fm1, fm2) = And (fm1, fm2);

(* ------------------------------------------------------------------------- *)
(* simplify: eliminates True/False below other connectives, and double-      *)
(*      negation                                                             *)
(* ------------------------------------------------------------------------- *)

fun simplify (Not fm) = SNot (simplify fm)
  | simplify (Or (fm1, fm2)) = SOr (simplify fm1, simplify fm2)
  | simplify (And (fm1, fm2)) = SAnd (simplify fm1, simplify fm2)
  | simplify fm = fm;

(* ------------------------------------------------------------------------- *)
(* indices: collects all indices of Boolean variables that occur in a        *)
(*      propositional formula 'fm'; no duplicates                            *)
(* ------------------------------------------------------------------------- *)

fun indices True = []
  | indices False = []
  | indices (BoolVar i) = [i]
  | indices (Not fm) = indices fm
  | indices (Or (fm1, fm2)) = union (op =) (indices fm1) (indices fm2)
  | indices (And (fm1, fm2)) = union (op =) (indices fm1) (indices fm2);

(* ------------------------------------------------------------------------- *)
(* maxidx: computes the maximal variable index occuring in a formula of      *)
(*      propositional logic 'fm'; 0 if 'fm' contains no variable             *)
(* ------------------------------------------------------------------------- *)

fun maxidx True = 0
  | maxidx False = 0
  | maxidx (BoolVar i) = i
  | maxidx (Not fm) = maxidx fm
  | maxidx (Or (fm1, fm2)) = Int.max (maxidx fm1, maxidx fm2)
  | maxidx (And (fm1, fm2)) = Int.max (maxidx fm1, maxidx fm2);

(* ------------------------------------------------------------------------- *)
(* exists: computes the disjunction over a list 'xs' of propositional        *)
(*      formulas                                                             *)
(* ------------------------------------------------------------------------- *)

fun exists xs = Library.foldl SOr (False, xs);

(* ------------------------------------------------------------------------- *)
(* all: computes the conjunction over a list 'xs' of propositional formulas  *)
(* ------------------------------------------------------------------------- *)

fun all xs = Library.foldl SAnd (True, xs);

(* ------------------------------------------------------------------------- *)
(* dot_product: ([x1,...,xn], [y1,...,yn]) -> x1*y1+...+xn*yn                *)
(* ------------------------------------------------------------------------- *)

fun dot_product (xs, ys) = exists (map SAnd (xs ~~ ys));

(* ------------------------------------------------------------------------- *)
(* is_nnf: returns 'true' iff the formula is in negation normal form (i.e.,  *)
(*         only variables may be negated, but not subformulas).              *)
(* ------------------------------------------------------------------------- *)

local
  fun is_literal (BoolVar _) = true
    | is_literal (Not (BoolVar _)) = true
    | is_literal _ = false
  fun is_conj_disj (Or (fm1, fm2)) = is_conj_disj fm1 andalso is_conj_disj fm2
    | is_conj_disj (And (fm1, fm2)) = is_conj_disj fm1 andalso is_conj_disj fm2
    | is_conj_disj fm = is_literal fm
in
  fun is_nnf True = true
    | is_nnf False = true
    | is_nnf fm = is_conj_disj fm
end;

(* ------------------------------------------------------------------------- *)
(* is_cnf: returns 'true' iff the formula is in conjunctive normal form      *)
(*         (i.e., a conjunction of disjunctions of literals). 'is_cnf'       *)
(*         implies 'is_nnf'.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun is_literal (BoolVar _) = true
    | is_literal (Not (BoolVar _)) = true
    | is_literal _ = false
  fun is_disj (Or (fm1, fm2)) = is_disj fm1 andalso is_disj fm2
    | is_disj fm = is_literal fm
  fun is_conj (And (fm1, fm2)) = is_conj fm1 andalso is_conj fm2
    | is_conj fm = is_disj fm
in
  fun is_cnf True = true
    | is_cnf False = true
    | is_cnf fm = is_conj fm
end;

(* ------------------------------------------------------------------------- *)
(* nnf: computes the negation normal form of a formula 'fm' of propositional *)
(*      logic (i.e., only variables may be negated, but not subformulas).    *)
(*      Simplification (cf. 'simplify') is performed as well. Not            *)
(*      surprisingly, 'is_nnf o nnf' always returns 'true'. 'nnf fm' returns *)
(*      'fm' if (and only if) 'is_nnf fm' returns 'true'.                    *)
(* ------------------------------------------------------------------------- *)

fun nnf fm =
  let
    fun
      (* constants *)
        nnf_aux True = True
      | nnf_aux False = False
      (* variables *)
      | nnf_aux (BoolVar i) = (BoolVar i)
      (* 'or' and 'and' as outermost connectives are left untouched *)
      | nnf_aux (Or  (fm1, fm2)) = SOr (nnf_aux fm1, nnf_aux fm2)
      | nnf_aux (And (fm1, fm2)) = SAnd (nnf_aux fm1, nnf_aux fm2)
      (* 'not' + constant *)
      | nnf_aux (Not True) = False
      | nnf_aux (Not False) = True
      (* 'not' + variable *)
      | nnf_aux (Not (BoolVar i)) = Not (BoolVar i)
      (* pushing 'not' inside of 'or'/'and' using de Morgan's laws *)
      | nnf_aux (Not (Or  (fm1, fm2))) = SAnd (nnf_aux (SNot fm1), nnf_aux (SNot fm2))
      | nnf_aux (Not (And (fm1, fm2))) = SOr  (nnf_aux (SNot fm1), nnf_aux (SNot fm2))
      (* double-negation elimination *)
      | nnf_aux (Not (Not fm)) = nnf_aux fm
  in
    if is_nnf fm then fm
    else nnf_aux fm
  end;

(* ------------------------------------------------------------------------- *)
(* cnf: computes the conjunctive normal form (i.e., a conjunction of         *)
(*      disjunctions of literals) of a formula 'fm' of propositional logic.  *)
(*      Simplification (cf. 'simplify') is performed as well. The result     *)
(*      is equivalent to 'fm', but may be exponentially longer. Not          *)
(*      surprisingly, 'is_cnf o cnf' always returns 'true'. 'cnf fm' returns *)
(*      'fm' if (and only if) 'is_cnf fm' returns 'true'.                    *)
(* ------------------------------------------------------------------------- *)

fun cnf fm =
  let
    (* function to push an 'Or' below 'And's, using distributive laws *)
    fun cnf_or (And (fm11, fm12), fm2) =
          And (cnf_or (fm11, fm2), cnf_or (fm12, fm2))
      | cnf_or (fm1, And (fm21, fm22)) =
          And (cnf_or (fm1, fm21), cnf_or (fm1, fm22))
    (* neither subformula contains 'And' *)
      | cnf_or (fm1, fm2) = Or (fm1, fm2)
    fun cnf_from_nnf True = True
      | cnf_from_nnf False = False
      | cnf_from_nnf (BoolVar i) = BoolVar i
    (* 'fm' must be a variable since the formula is in NNF *)
      | cnf_from_nnf (Not fm) = Not fm
    (* 'Or' may need to be pushed below 'And' *)
      | cnf_from_nnf (Or (fm1, fm2)) =
        cnf_or (cnf_from_nnf fm1, cnf_from_nnf fm2)
    (* 'And' as outermost connective is left untouched *)
      | cnf_from_nnf (And (fm1, fm2)) =
        And (cnf_from_nnf fm1, cnf_from_nnf fm2)
  in
    if is_cnf fm then fm
    else (cnf_from_nnf o nnf) fm
  end;

(* ------------------------------------------------------------------------- *)
(* defcnf: computes a definitional conjunctive normal form of a formula 'fm' *)
(*      of propositional logic. Simplification (cf. 'simplify') is performed *)
(*      as well. 'defcnf' may introduce auxiliary Boolean variables to avoid *)
(*      an exponential blowup of the formula.  The result is equisatisfiable *)
(*      (i.e., satisfiable if and only if 'fm' is satisfiable), but not      *)
(*      necessarily equivalent to 'fm'. Not surprisingly, 'is_cnf o defcnf'  *)
(*      always returns 'true'. 'defcnf fm' returns 'fm' if (and only if)     *)
(*      'is_cnf fm' returns 'true'.                                          *)
(* ------------------------------------------------------------------------- *)

fun defcnf fm =
  if is_cnf fm then fm
  else
    let
      val fm' = nnf fm
      (* 'new' specifies the next index that is available to introduce an auxiliary variable *)
      (* int ref *)
      val new = Unsynchronized.ref (maxidx fm' + 1)
      (* unit -> int *)
      fun new_idx () = let val idx = !new in new := idx+1; idx end
      (* replaces 'And' by an auxiliary variable (and its definition) *)
      (* prop_formula -> prop_formula * prop_formula list *)
      fun defcnf_or (And x) =
            let
              val i = new_idx ()
            in
              (* Note that definitions are in NNF, but not CNF. *)
              (BoolVar i, [Or (Not (BoolVar i), And x)])
            end
        | defcnf_or (Or (fm1, fm2)) =
            let
              val (fm1', defs1) = defcnf_or fm1
              val (fm2', defs2) = defcnf_or fm2
            in
              (Or (fm1', fm2'), defs1 @ defs2)
            end
        | defcnf_or fm = (fm, [])
      (* prop_formula -> prop_formula *)
      fun defcnf_from_nnf True = True
        | defcnf_from_nnf False = False
        | defcnf_from_nnf (BoolVar i) = BoolVar i
      (* 'fm' must be a variable since the formula is in NNF *)
        | defcnf_from_nnf (Not fm) = Not fm
      (* 'Or' may need to be pushed below 'And' *)
      (* 'Or' of literal and 'And': use distributivity *)
        | defcnf_from_nnf (Or (BoolVar i, And (fm1, fm2))) =
            And (defcnf_from_nnf (Or (BoolVar i, fm1)),
                 defcnf_from_nnf (Or (BoolVar i, fm2)))
        | defcnf_from_nnf (Or (Not (BoolVar i), And (fm1, fm2))) =
            And (defcnf_from_nnf (Or (Not (BoolVar i), fm1)),
                 defcnf_from_nnf (Or (Not (BoolVar i), fm2)))
        | defcnf_from_nnf (Or (And (fm1, fm2), BoolVar i)) =
            And (defcnf_from_nnf (Or (fm1, BoolVar i)),
                 defcnf_from_nnf (Or (fm2, BoolVar i)))
        | defcnf_from_nnf (Or (And (fm1, fm2), Not (BoolVar i))) =
            And (defcnf_from_nnf (Or (fm1, Not (BoolVar i))),
                 defcnf_from_nnf (Or (fm2, Not (BoolVar i))))
      (* all other cases: turn the formula into a disjunction of literals, *)
      (*                  adding definitions as necessary                  *)
        | defcnf_from_nnf (Or x) =
            let
              val (fm, defs) = defcnf_or (Or x)
              val cnf_defs = map defcnf_from_nnf defs
            in
              all (fm :: cnf_defs)
            end
      (* 'And' as outermost connective is left untouched *)
        | defcnf_from_nnf (And (fm1, fm2)) =
            And (defcnf_from_nnf fm1, defcnf_from_nnf fm2)
    in
      defcnf_from_nnf fm'
    end;

(* ------------------------------------------------------------------------- *)
(* eval: given an assignment 'a' of Boolean values to variable indices, the  *)
(*      truth value of a propositional formula 'fm' is computed              *)
(* ------------------------------------------------------------------------- *)

fun eval a True = true
  | eval a False = false
  | eval a (BoolVar i) = (a i)
  | eval a (Not fm) = not (eval a fm)
  | eval a (Or (fm1, fm2)) = (eval a fm1) orelse (eval a fm2)
  | eval a (And (fm1, fm2)) = (eval a fm1) andalso (eval a fm2);

(* ------------------------------------------------------------------------- *)
(* prop_formula_of_term: returns the propositional structure of a HOL term,  *)
(*      with subterms replaced by Boolean variables.  Also returns a table   *)
(*      of terms and corresponding variables that extends the table that was *)
(*      given as an argument.  Usually, you'll just want to use              *)
(*      'Termtab.empty' as value for 'table'.                                *)
(* ------------------------------------------------------------------------- *)

(* Note: The implementation is somewhat optimized; the next index to be used *)
(*       is computed only when it is actually needed.  However, when         *)
(*       'prop_formula_of_term' is invoked many times, it might be more      *)
(*       efficient to pass and return this value as an additional parameter, *)
(*       so that it does not have to be recomputed (by folding over the      *)
(*       table) for each invocation.                                         *)

fun prop_formula_of_term t table =
  let
    val next_idx_is_valid = Unsynchronized.ref false
    val next_idx = Unsynchronized.ref 0
    fun get_next_idx () =
      if !next_idx_is_valid then
        Unsynchronized.inc next_idx
      else (
        next_idx := Termtab.fold (Integer.max o snd) table 0;
        next_idx_is_valid := true;
        Unsynchronized.inc next_idx
      )
    fun aux (Const (@{const_name True}, _)) table = (True, table)
      | aux (Const (@{const_name False}, _)) table = (False, table)
      | aux (Const (@{const_name Not}, _) $ x) table = apfst Not (aux x table)
      | aux (Const (@{const_name HOL.disj}, _) $ x $ y) table =
          let
            val (fm1, table1) = aux x table
            val (fm2, table2) = aux y table1
          in
            (Or (fm1, fm2), table2)
          end
      | aux (Const (@{const_name HOL.conj}, _) $ x $ y) table =
          let
            val (fm1, table1) = aux x table
            val (fm2, table2) = aux y table1
          in
            (And (fm1, fm2), table2)
          end
      | aux x table =
          (case Termtab.lookup table x of
            SOME i => (BoolVar i, table)
          | NONE =>
              let
                val i = get_next_idx ()
              in
                (BoolVar i, Termtab.update (x, i) table)
              end)
  in
    aux t table
  end;

(* ------------------------------------------------------------------------- *)
(* term_of_prop_formula: returns a HOL term that corresponds to a            *)
(*      propositional formula, with Boolean variables replaced by Free's     *)
(* ------------------------------------------------------------------------- *)

(* Note: A more generic implementation should take another argument of type  *)
(*       Term.term Inttab.table (or so) that specifies HOL terms for some    *)
(*       Boolean variables in the formula, similar to 'prop_formula_of_term' *)
(*       (but the other way round).                                          *)

fun term_of_prop_formula True = @{term True}
  | term_of_prop_formula False = @{term False}
  | term_of_prop_formula (BoolVar i) = Free ("v" ^ string_of_int i, HOLogic.boolT)
  | term_of_prop_formula (Not fm) = HOLogic.mk_not (term_of_prop_formula fm)
  | term_of_prop_formula (Or (fm1, fm2)) =
      HOLogic.mk_disj (term_of_prop_formula fm1, term_of_prop_formula fm2)
  | term_of_prop_formula (And (fm1, fm2)) =
      HOLogic.mk_conj (term_of_prop_formula fm1, term_of_prop_formula fm2);

end;
