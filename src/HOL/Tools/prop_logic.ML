(*  Title:      HOL/Tools/prop_logic.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2004

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

	val SNot : prop_formula -> prop_formula
	val SOr  : prop_formula * prop_formula -> prop_formula
	val SAnd : prop_formula * prop_formula -> prop_formula

	val indices : prop_formula -> int list  (* set of all variable indices *)
	val maxidx  : prop_formula -> int  (* maximal variable index *)

	val nnf    : prop_formula -> prop_formula  (* negation normal form *)
	val cnf    : prop_formula -> prop_formula  (* conjunctive normal form *)
	val defcnf : prop_formula -> prop_formula  (* definitional cnf *)

	val exists      : prop_formula list -> prop_formula  (* finite disjunction *)
	val all         : prop_formula list -> prop_formula  (* finite conjunction *)
	val dot_product : prop_formula list * prop_formula list -> prop_formula

	val eval : (int -> bool) -> prop_formula -> bool  (* semantics *)
end;

structure PropLogic : PROP_LOGIC =
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

	(* prop_formula -> prop_formula *)

	fun SNot True     = False
	  | SNot False    = True
	  | SNot (Not fm) = fm
	  | SNot fm       = Not fm;

	(* prop_formula * prop_formula -> prop_formula *)

	fun SOr (True, _)   = True
	  | SOr (_, True)   = True
	  | SOr (False, fm) = fm
	  | SOr (fm, False) = fm
	  | SOr (fm1, fm2)  = Or (fm1, fm2);

	(* prop_formula * prop_formula -> prop_formula *)

	fun SAnd (True, fm) = fm
	  | SAnd (fm, True) = fm
	  | SAnd (False, _) = False
	  | SAnd (_, False) = False
	  | SAnd (fm1, fm2) = And (fm1, fm2);

(* ------------------------------------------------------------------------- *)
(* indices: collects all indices of Boolean variables that occur in a        *)
(*      propositional formula 'fm'; no duplicates                            *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> int list *)

	fun indices True            = []
	  | indices False           = []
	  | indices (BoolVar i)     = [i]
	  | indices (Not fm)        = indices fm
	  | indices (Or (fm1,fm2))  = (indices fm1) union_int (indices fm2)
	  | indices (And (fm1,fm2)) = (indices fm1) union_int (indices fm2);

(* ------------------------------------------------------------------------- *)
(* maxidx: computes the maximal variable index occuring in a formula of      *)
(*      propositional logic 'fm'; 0 if 'fm' contains no variable             *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> int *)

	fun maxidx True            = 0
	  | maxidx False           = 0
	  | maxidx (BoolVar i)     = i
	  | maxidx (Not fm)        = maxidx fm
	  | maxidx (Or (fm1,fm2))  = Int.max (maxidx fm1, maxidx fm2)
	  | maxidx (And (fm1,fm2)) = Int.max (maxidx fm1, maxidx fm2);

(* ------------------------------------------------------------------------- *)
(* exception SAME: raised to indicate that the return value of a function is *)
(*                 identical to its argument (optimization to allow sharing, *)
(*                 rather than copying)                                      *)
(* ------------------------------------------------------------------------- *)

	exception SAME;

(* ------------------------------------------------------------------------- *)
(* nnf: computes the negation normal form of a formula 'fm' of propositional *)
(*      logic (i.e. only variables may be negated, but not subformulas)      *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun
	(* constants *)
	    nnf True                  = True
	  | nnf False                 = False
	(* variables *)
	  | nnf (BoolVar i)           = (BoolVar i)
	(* 'or' and 'and' as outermost connectives are left untouched *)
	  | nnf (Or  (fm1,fm2))       = SOr  (nnf fm1, nnf fm2)
	  | nnf (And (fm1,fm2))       = SAnd (nnf fm1, nnf fm2)
	(* 'not' + constant *)
	  | nnf (Not True)            = False
	  | nnf (Not False)           = True
	(* 'not' + variable *)
	  | nnf (Not (BoolVar i))     = Not (BoolVar i)
	(* pushing 'not' inside of 'or'/'and' using de Morgan's laws *)
	  | nnf (Not (Or  (fm1,fm2))) = SAnd (nnf (SNot fm1), nnf (SNot fm2))
	  | nnf (Not (And (fm1,fm2))) = SOr  (nnf (SNot fm1), nnf (SNot fm2))
	(* double-negation elimination *)
	  | nnf (Not (Not fm))        = nnf fm;

(* ------------------------------------------------------------------------- *)
(* cnf: computes the conjunctive normal form (i.e. a conjunction of          *)
(*      disjunctions) of a formula 'fm' of propositional logic.  The result  *)
(*      formula may be exponentially longer than 'fm'.                       *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun cnf fm =
	let
		fun
		(* constants *)
		    cnf_from_nnf True             = True
		  | cnf_from_nnf False            = False
		(* literals *)
		  | cnf_from_nnf (BoolVar i)      = BoolVar i
		  | cnf_from_nnf (Not fm1)        = Not fm1  (* 'fm1' must be a variable since the formula is in NNF *)
		(* pushing 'or' inside of 'and' using distributive laws *)
		  | cnf_from_nnf (Or (fm1, fm2))  =
			let
				fun cnf_or (And (fm11, fm12), fm2) =
					And (cnf_or (fm11, fm2), cnf_or (fm12, fm2))
				  | cnf_or (fm1, And (fm21, fm22)) =
					And (cnf_or (fm1, fm21), cnf_or (fm1, fm22))
				(* neither subformula contains 'and' *)
				  | cnf_or (fm1, fm2) =
					Or (fm1, fm2)
			in
				cnf_or (cnf_from_nnf fm1, cnf_from_nnf fm2)
			end
		(* 'and' as outermost connective is left untouched *)
		  | cnf_from_nnf (And (fm1, fm2)) = And (cnf_from_nnf fm1, cnf_from_nnf fm2)
	in
		(cnf_from_nnf o nnf) fm
	end;

(* ------------------------------------------------------------------------- *)
(* defcnf: computes the definitional conjunctive normal form of a formula    *)
(*      'fm' of propositional logic, introducing auxiliary variables if      *)
(*      necessary to avoid an exponential blowup of the formula.  The result *)
(*      formula is satisfiable if and only if 'fm' is satisfiable.           *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula -> prop_formula *)

	fun defcnf fm =
	let
		(* prop_formula * int -> prop_formula * int *)
		(* 'new' specifies the next index that is available to introduce an auxiliary variable *)
		fun
		(* constants *)
		    defcnf_from_nnf (True, new)            = (True, new)
		  | defcnf_from_nnf (False, new)           = (False, new)
		(* literals *)
		  | defcnf_from_nnf (BoolVar i, new)       = (BoolVar i, new)
		  | defcnf_from_nnf (Not fm1, new)         = (Not fm1, new)  (* 'fm1' must be a variable since the formula is in NNF *)
		(* pushing 'or' inside of 'and' using auxiliary variables *)
		  | defcnf_from_nnf (Or (fm1, fm2), new)   =
			let
				val (fm1', new')  = defcnf_from_nnf (fm1, new)
				val (fm2', new'') = defcnf_from_nnf (fm2, new')
				(* prop_formula * prop_formula -> int -> prop_formula * int *)
				fun defcnf_or (And (fm11, fm12), fm2) new =
					(case fm2 of
					(* do not introduce an auxiliary variable for literals *)
					  BoolVar _ =>
						let
							val (fm_a, new')  = defcnf_or (fm11, fm2) new
							val (fm_b, new'') = defcnf_or (fm12, fm2) new'
						in
							(And (fm_a, fm_b), new'')
						end
					| Not _ =>
						let
							val (fm_a, new')  = defcnf_or (fm11, fm2) new
							val (fm_b, new'') = defcnf_or (fm12, fm2) new'
						in
							(And (fm_a, fm_b), new'')
						end
					| _ =>
						let
							val aux            = BoolVar new
							val (fm_a, new')   = defcnf_or (fm11, aux)     (new+1)
							val (fm_b, new'')  = defcnf_or (fm12, aux)     new'
							val (fm_c, new''') = defcnf_or (fm2,  Not aux) new''
						in
							(And (And (fm_a, fm_b), fm_c), new''')
						end)
				  | defcnf_or (fm1, And (fm21, fm22)) new =
					(case fm1 of
					(* do not introduce an auxiliary variable for literals *)
					  BoolVar _ =>
						let
							val (fm_a, new')  = defcnf_or (fm1, fm21) new
							val (fm_b, new'') = defcnf_or (fm1, fm22) new'
						in
							(And (fm_a, fm_b), new'')
						end
					| Not _ =>
						let
							val (fm_a, new')  = defcnf_or (fm1, fm21) new
							val (fm_b, new'') = defcnf_or (fm1, fm22) new'
						in
							(And (fm_a, fm_b), new'')
						end
					| _ =>
						let
							val aux            = BoolVar new
							val (fm_a, new')   = defcnf_or (fm1,  Not aux) (new+1)
							val (fm_b, new'')  = defcnf_or (fm21, aux)     new'
							val (fm_c, new''') = defcnf_or (fm22, aux)     new''
						in
							(And (fm_a, And (fm_b, fm_c)), new''')
						end)
				(* neither subformula contains 'and' *)
				  | defcnf_or (fm1, fm2) new =
					(Or (fm1, fm2), new)
			in
				defcnf_or (fm1', fm2') new''
			end
		(* 'and' as outermost connective is left untouched *)
		  | defcnf_from_nnf (And (fm1, fm2), new)   =
			let
				val (fm1', new')  = defcnf_from_nnf (fm1, new)
				val (fm2', new'') = defcnf_from_nnf (fm2, new')
			in
				(And (fm1', fm2'), new'')
			end
		val fm' = nnf fm
	in
		(fst o defcnf_from_nnf) (fm', (maxidx fm')+1)
	end;

(* ------------------------------------------------------------------------- *)
(* exists: computes the disjunction over a list 'xs' of propositional        *)
(*      formulas                                                             *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list -> prop_formula *)

	fun exists xs = foldl SOr (False, xs);

(* ------------------------------------------------------------------------- *)
(* all: computes the conjunction over a list 'xs' of propositional formulas  *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list -> prop_formula *)

	fun all xs = foldl SAnd (True, xs);

(* ------------------------------------------------------------------------- *)
(* dot_product: ([x1,...,xn], [y1,...,yn]) -> x1*y1+...+xn*yn                *)
(* ------------------------------------------------------------------------- *)

	(* prop_formula list * prop_formula list -> prop_formula *)

	fun dot_product (xs,ys) = exists (map SAnd (xs~~ys));

(* ------------------------------------------------------------------------- *)
(* eval: given an assignment 'a' of Boolean values to variable indices, the  *)
(*      truth value of a propositional formula 'fm' is computed              *)
(* ------------------------------------------------------------------------- *)

	(* (int -> bool) -> prop_formula -> bool *)

	fun eval a True            = true
	  | eval a False           = false
	  | eval a (BoolVar i)     = (a i)
	  | eval a (Not fm)        = not (eval a fm)
	  | eval a (Or (fm1,fm2))  = (eval a fm1) orelse (eval a fm2)
	  | eval a (And (fm1,fm2)) = (eval a fm1) andalso (eval a fm2);

end;
