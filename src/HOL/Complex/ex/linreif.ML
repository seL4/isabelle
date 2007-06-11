(* 
 The oracle for Mixed Real-Integer auantifier elimination 
     based on the verified Code in ~/work/MIR/MIR.thy 
*)

structure ReflectedFerrack =
struct

open Ferrack;

exception LINR;

(* pseudo reification : term -> intterm *)
val iT = HOLogic.intT;
val rT = Type ("RealDef.real",[]);
val bT = HOLogic.boolT;
val realC = Const("RealDef.real",iT --> rT);
val rzero = Const("0",rT);

fun num_of_term vs t = 
    case t of
	Free(xn,xT) => (case AList.lookup (op =) vs t of 
			   NONE   => error "Variable not found in the list!!"
			 | SOME n => Bound n)
      | Const("RealDef.real",_)$ @{term "0::int"} => C 0
      | Const("RealDef.real",_)$ @{term "1::int"} => C 1
      | @{term "0::real"} => C 0
      | @{term "0::real"} => C 1
      | Term.Bound i => Bound (nat i)
      | Const(@{const_name "HOL.uminus"},_)$t' => Neg (num_of_term vs t')
      | Const (@{const_name "HOL.plus"},_)$t1$t2 => Add (num_of_term vs t1,num_of_term vs t2)
      | Const (@{const_name "HOL.minus"},_)$t1$t2 => Sub (num_of_term vs t1,num_of_term vs t2)
      | Const (@{const_name "HOL.times"},_)$t1$t2 => 
	(case (num_of_term vs t1) of C i => 
				     Mul (i,num_of_term vs t2)
				   | _ => error "num_of_term: unsupported Multiplication")
      | Const("RealDef.real",_) $ Const (@{const_name "Numeral.number_of"},_)$t' => C (HOLogic.dest_numeral t')
      | Const (@{const_name "Numeral.number_of"},_)$t' => C (HOLogic.dest_numeral t')
      | _ => error ("num_of_term: unknown term " ^ (Display.raw_string_of_term t));
	

(* pseudo reification : term -> fm *)
fun fm_of_term vs t = 
    case t of 
	Const("True",_) => T
      | Const("False",_) => F
      | Const(@{const_name "Orderings.less"},_)$t1$t2 => Lt (Sub (num_of_term vs t1,num_of_term vs t2))
      | Const(@{const_name "Orderings.less_eq"},_)$t1$t2 => Le (Sub (num_of_term vs t1,num_of_term vs t2))
      | Const("op =",eqT)$t1$t2 => 
	if (domain_type eqT = rT)
	then Eq (Sub (num_of_term vs t1,num_of_term vs t2)) 
	else Iff(fm_of_term vs t1,fm_of_term vs t2)
      | Const("op &",_)$t1$t2 => And(fm_of_term vs t1,fm_of_term vs t2)
      | Const("op |",_)$t1$t2 => Or(fm_of_term vs t1,fm_of_term vs t2)
      | Const("op -->",_)$t1$t2 => Imp(fm_of_term vs t1,fm_of_term vs t2)
      | Const("Not",_)$t' => NOT(fm_of_term vs t')
      | Const("Ex",_)$Term.Abs(xn,xT,p) => 
	E(fm_of_term (map (fn(v,n) => (v,1+ n)) vs) p)
      | Const("All",_)$Term.Abs(xn,xT,p) => 
	A(fm_of_term (map (fn(v,n) => (v,1+ n)) vs) p)
      | _ => error ("fm_of_term : unknown term!" ^ (Display.raw_string_of_term t));

fun zip [] [] = []
  | zip (x::xs) (y::ys) = (x,y)::(zip xs ys);


fun start_vs t =
    let val fs = term_frees t
    in zip fs (map nat (0 upto  (length fs - 1)))
    end ;

(* transform num and fm back to terms *)

fun myassoc2 l v =
    case l of
	[] => NONE
      | (x,v')::xs => if v = v' then SOME x
		      else myassoc2 xs v;

fun term_of_num vs t =
    case t of 
	C i => realC $ (HOLogic.mk_number HOLogic.intT i)
      | Bound n => valOf (myassoc2 vs n)
      | Neg t' => Const(@{const_name "HOL.uminus"},rT --> rT)$(term_of_num vs t')
      | Add(t1,t2) => Const(@{const_name "HOL.plus"},[rT,rT] ---> rT)$
			   (term_of_num vs t1)$(term_of_num vs t2)
      | Sub(t1,t2) => Const(@{const_name "HOL.minus"},[rT,rT] ---> rT)$
			   (term_of_num vs t1)$(term_of_num vs t2)
      | Mul(i,t2) => Const(@{const_name "HOL.times"},[rT,rT] ---> rT)$
			   (term_of_num vs (C i))$(term_of_num vs t2)
      | CN(n,i,t) => term_of_num vs (Add (Mul(i,Bound n),t));

fun term_of_fm vs t = 
    case t of 
	T => HOLogic.true_const 
      | F => HOLogic.false_const
      | Lt t => Const(@{const_name "Orderings.less"},[rT,rT] ---> bT)$
			   (term_of_num vs t)$ rzero
      | Le t => Const(@{const_name "Orderings.less_eq"},[rT,rT] ---> bT)$
			  (term_of_num vs t)$ rzero
      | Gt t => Const(@{const_name "Orderings.less"},[rT,rT] ---> bT)$
			   rzero $(term_of_num vs t)
      | Ge t => Const(@{const_name "Orderings.less_eq"},[rT,rT] ---> bT)$
			  rzero $(term_of_num vs t)
      | Eq t => Const("op =",[rT,rT] ---> bT)$
			   (term_of_num vs t)$ rzero
      | NEq t => term_of_fm vs (NOT (Eq t))
      | NOT t' => HOLogic.Not$(term_of_fm vs t')
      | And(t1,t2) => HOLogic.conj$(term_of_fm vs t1)$(term_of_fm vs t2)
      | Or(t1,t2) => HOLogic.disj$(term_of_fm vs t1)$(term_of_fm vs t2)
      | Imp(t1,t2) => HOLogic.imp$(term_of_fm vs t1)$(term_of_fm vs t2)
      | Iff(t1,t2) => (HOLogic.eq_const bT)$(term_of_fm vs t1)$
					   (term_of_fm vs t2)
      | _ => error "If this is raised, Isabelle/HOL or generate_code is inconsistent!";

(* The oracle *)

fun linrqe_oracle thy t = 
    let 
	val vs = start_vs t
    in HOLogic.mk_Trueprop (HOLogic.mk_eq(t, term_of_fm vs (linrqe (fm_of_term vs t))))
    end;
end;
