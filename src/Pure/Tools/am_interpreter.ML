(*  Title:      Pure/Tools/am_interpreter.ML
    ID:         $Id$
    Author:     Steven Obua
*)

signature ABSTRACT_MACHINE = sig							     
datatype term = Var of int | Const of int | App of term * term | Abs of term

datatype pattern = PVar | PConst of int * (pattern list)

type program

exception Compile of string;
val compile : (pattern * term) list -> program
 
exception Run of string;
val run : program -> term -> term

end

structure AM_Interpreter :> ABSTRACT_MACHINE = struct

datatype term = Var of int | Const of int | App of term * term | Abs of term

datatype pattern = PVar | PConst of int * (pattern list)

datatype closure = CVar of int | CConst of int
		 | CApp of closure * closure | CAbs of closure 
		 | Closure of (closure list) * closure 

structure prog_struct = TableFun(type key = int*int val ord = prod_ord int_ord int_ord);

type program = ((pattern * closure) list) prog_struct.table

datatype stack = SEmpty | SAppL of closure * stack | SAppR of closure * stack | SAbs of stack

exception Compile of string;
exception Run of string;

fun clos_of_term (Var x) = CVar x
  | clos_of_term (Const c) = CConst c
  | clos_of_term (App (u, v)) = CApp (clos_of_term u, clos_of_term v)
  | clos_of_term (Abs u) = CAbs (clos_of_term u)

fun term_of_clos (CVar x) = Var x
  | term_of_clos (CConst c) = Const c
  | term_of_clos (CApp (u, v)) = App (term_of_clos u, term_of_clos v)
  | term_of_clos (CAbs u) = Abs (term_of_clos u)
  | term_of_clos (Closure (e, u)) = raise (Run "internal error: closure in normalized term found")

fun strip_closure args (CApp (a,b)) = strip_closure (b::args) a
  | strip_closure args x = (x, args)

fun len_head_of_closure n (CApp (a,b)) = len_head_of_closure (n+1) a
  | len_head_of_closure n x = (n, x)


(* earlier occurrence of PVar corresponds to higher de Bruijn index *)
fun pattern_match args PVar clos = SOME (clos::args)
  | pattern_match args (PConst (c, patterns)) clos = 
    let
	val (f, closargs) = strip_closure [] clos
    in
	case f of 
	    CConst d => 
	    if c = d then 
		pattern_match_list args patterns closargs
	    else 
		NONE
	  | _ => NONE
    end
and pattern_match_list args [] [] = SOME args
  | pattern_match_list args (p::ps) (c::cs) = 
    (case pattern_match args p c of
	NONE => NONE
      | SOME args => pattern_match_list args ps cs)
  | pattern_match_list _ _ _ = NONE

(* Returns true iff at most 0 .. (free-1) occur unbound. therefore check_freevars 0 t iff t is closed *)
fun check_freevars free (Var x) = x < free
  | check_freevars free (Const c) = true
  | check_freevars free (App (u, v)) = check_freevars free u andalso check_freevars free v
  | check_freevars free (Abs m) = check_freevars (free+1) m

fun count_patternvars PVar = 1
  | count_patternvars (PConst (_, ps)) = List.foldl (fn (p, count) => (count_patternvars p)+count) 0 ps

fun pattern_key (PConst (c, ps)) = (c, length ps)
  | pattern_key _ = raise (Compile "pattern reduces to variable")

fun compile eqs = 
    let
	val eqs = map (fn (p, r) => (check_freevars (count_patternvars p) r; 
				     (pattern_key p, (p, clos_of_term r)))) eqs
    in
	prog_struct.make (map (fn (k, a) => (k, [a])) eqs)
    end	

fun match_rules n [] clos = NONE
  | match_rules n ((p,eq)::rs) clos =
    case pattern_match [] p clos of
	NONE => match_rules (n+1) rs clos
      | SOME args => SOME (Closure (args, eq))

fun match_closure prog clos = 
    case len_head_of_closure 0 clos of
	(len, CConst c) =>
	(case prog_struct.lookup (prog, (c, len)) of
	    NONE => NONE
	  | SOME rules => match_rules 0 rules clos)
      | _ => NONE

fun lift n (c as (CConst _)) = c
  | lift n (v as CVar m) = if m < n then v else CVar (m+1)
  | lift n (CAbs t) = CAbs (lift (n+1) t)
  | lift n (CApp (a,b)) = CApp (lift n a, lift n b)
  | lift n (Closure (e, a)) = Closure (lift_env n e, lift (n+(length e)) a)
and lift_env n e = map (lift n) e

fun weak prog stack (Closure (e, CApp (a, b))) = weak prog (SAppL (Closure (e, b), stack)) (Closure (e, a))
  | weak prog (SAppL (b, stack)) (Closure (e, CAbs m)) = weak prog stack (Closure (b::e, m))
  | weak prog stack (Closure (e, CVar n)) = weak prog stack (List.nth (e, n) handle Subscript => (CVar (n-(length e))))
  | weak prog stack (Closure (e, c as CConst _)) = weak prog stack c
  | weak prog stack clos =    
    case match_closure prog clos of
	NONE => weak_last prog stack clos
      | SOME r => weak prog stack r
and weak_last prog (SAppR (a, stack)) b = weak prog stack (CApp (a,b))
  | weak_last prog (s as (SAppL (b, stack))) a = weak prog (SAppR (a, stack)) b
  | weak_last prog stack c = (stack, c) 

fun strong prog stack (Closure (e, CAbs m)) = 
    let
	val (stack', wnf) = weak prog SEmpty (Closure ((CVar 0)::(lift_env 0 e), m))
    in
	case stack' of
	    SEmpty => strong prog (SAbs stack) wnf
	  | _ => raise (Run "internal error in strong: weak failed")
    end
  | strong prog stack (clos as (CApp (u, v))) = strong prog (SAppL (v, stack)) u
  | strong prog stack clos = strong_last prog stack clos
and strong_last prog (SAbs stack) m = strong prog stack (CAbs m)
  | strong_last prog (SAppL (b, stack)) a = strong prog (SAppR (a, stack)) b
  | strong_last prog (SAppR (a, stack)) b = strong_last prog stack (CApp (a, b))
  | strong_last prog stack clos = (stack, clos)

fun run prog t = 
    let
	val (stack, wnf) = weak prog SEmpty (Closure ([], clos_of_term t))
    in
	case stack of 
	    SEmpty => (case strong prog SEmpty wnf of
			   (SEmpty, snf) => term_of_clos snf
			 | _ => raise (Run "internal error in run: strong failed"))
	  | _ => raise (Run "internal error in run: weak failed")
    end
	  
end

structure AbstractMachine = AM_Interpreter
