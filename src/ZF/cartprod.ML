(*  Title:      ZF/cartprod.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Syntactic operations for Cartesian Products
*)

signature PR =                  (** Description of a Cartesian product **)
  sig
  val sigma     : term                  (*Cartesian product operator*)
  val pair      : term                  (*pairing operator*)
  val split_name : string               (*name of polymorphic split*)
  val pair_iff  : thm                   (*injectivity of pairing, using <->*)
  val split_eq  : thm                   (*equality rule for split*)
  val fsplitI   : thm                   (*intro rule for fsplit*)
  val fsplitD   : thm                   (*destruct rule for fsplit*)
  val fsplitE   : thm                   (*elim rule; apparently never used*)
  end;

signature CARTPROD =		(** Derived syntactic functions for produts **)
  sig
  val ap_split : typ -> typ -> term -> term
  val factors : typ -> typ list
  val mk_prod : typ * typ -> typ
  val mk_tuple : term -> typ -> term list -> term
  val pseudo_type : term -> typ
  val remove_split : thm -> thm
  val split_const : typ -> term
  val split_rule_var : term * thm -> thm
  end;


functor CartProd_Fun (Pr: PR) : CARTPROD =
struct

(* Some of these functions expect "pseudo-types" containing products,
   as in HOL; the true ZF types would just be "i" *)

fun mk_prod (T1,T2) = Type("*", [T1,T2]);

(*Bogus product type underlying a (possibly nested) Sigma.  
  Lets us share HOL code*)
fun pseudo_type (t $ A $ Abs(_,_,B)) = 
        if t = Pr.sigma  then  mk_prod(pseudo_type A, pseudo_type B)
                         else  Ind_Syntax.iT
  | pseudo_type _           =  Ind_Syntax.iT;

(*Maps the type T1*...*Tn to [T1,...,Tn], however nested*)
fun factors (Type("*", [T1,T2])) = factors T1 @ factors T2
  | factors T                    = [T];

(*Make a well-typed instance of "split"*)
fun split_const T = Const(Pr.split_name, 
			  [[Ind_Syntax.iT, Ind_Syntax.iT]--->T, 
			   Ind_Syntax.iT] ---> T);

(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type("*", [T1,T2])) T3 u   = 
       split_const T3 $ 
       Abs("v", Ind_Syntax.iT, (*Not T1, as it involves pseudo-product types*)
	   ap_split T2 T3
	   ((ap_split T1 (factors T2 ---> T3) (incr_boundvars 1 u)) $ 
	    Bound 0))
  | ap_split T T3 u = u;

(*Makes a nested tuple from a list, following the product type structure*)
fun mk_tuple pair (Type("*", [T1,T2])) tms = 
        pair $ (mk_tuple pair T1 tms)
             $ (mk_tuple pair T2 (drop (length (factors T1), tms)))
  | mk_tuple pair T (t::_) = t;

(*Attempts to remove occurrences of split, and pair-valued parameters*)
val remove_split = rewrite_rule [Pr.split_eq];

(*Uncurries any Var involving pseudo-product type T1 in the rule*)
fun split_rule_var (t as Var(v, Type("fun",[T1,T2])), rl) =
      let val T' = factors T1 ---> T2
	  val newt = ap_split T1 T2 (Var(v,T'))
	  val cterm = Thm.cterm_of (#sign(rep_thm rl))
      in
	  remove_split (instantiate ([], [(cterm (Var(v, Ind_Syntax.iT-->T2)), 
					   cterm newt)]) rl)
      end
  | split_rule_var (t,rl) = rl;

end;

