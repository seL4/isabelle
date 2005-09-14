(* $Id$ *)
(* The oracle for Presburger arithmetic based on the verified Code *)
    (* in HOL/ex/Reflected_Presburger.thy *)

structure ReflectedCooper =
struct

open Generated;
(* pseudo reification : term -> intterm *)

fun i_of_term vs t = 
    case t of
	Free(xn,xT) => (case assoc(vs,t) of 
			   NONE   => error "Variable not found in the list!!"
			 | SOME n => Var n)
      | Const("0",iT) => Cst 0
      | Const("1",iT) => Cst 1
      | Bound i => Var (nat i)
      | Const("uminus",_)$t' => Neg (i_of_term vs t')
      | Const ("op +",_)$t1$t2 => Add (i_of_term vs t1,i_of_term vs t2)
      | Const ("op -",_)$t1$t2 => Sub (i_of_term vs t1,i_of_term vs t2)
      | Const ("op *",_)$t1$t2 => Mult (i_of_term vs t1,i_of_term vs t2)
      | Const ("Numeral.number_of",_)$t' => Cst (HOLogic.dest_binum t')
      | _ => error "i_of_term: unknown term";
	

(* pseudo reification : term -> QF *)
fun qf_of_term vs t = 
    case t of 
	Const("True",_) => T
      | Const("False",_) => F
      | Const("op <",_)$t1$t2 => Lt (i_of_term vs t1,i_of_term vs t2)
      | Const("op <=",_)$t1$t2 => Le (i_of_term vs t1,i_of_term vs t2)
      | Const ("Divides.op dvd",_)$t1$t2 => 
	Divides(i_of_term vs t1,i_of_term vs t2)
      | Const("op =",eqT)$t1$t2 => 
	if (domain_type eqT = HOLogic.intT)
	then let val i1 = i_of_term vs t1
		 val i2 = i_of_term vs t2
	     in	Eq (i1,i2)
	     end 
	else Equ(qf_of_term vs t1,qf_of_term vs t2)
      | Const("op &",_)$t1$t2 => And(qf_of_term vs t1,qf_of_term vs t2)
      | Const("op |",_)$t1$t2 => Or(qf_of_term vs t1,qf_of_term vs t2)
      | Const("op -->",_)$t1$t2 => Imp(qf_of_term vs t1,qf_of_term vs t2)
      | Const("Not",_)$t' => NOT(qf_of_term vs t')
      | Const("Ex",_)$Abs(xn,xT,p) => 
	QEx(qf_of_term (map (fn(v,n) => (v,n + 1)) vs) p)
      | Const("All",_)$Abs(xn,xT,p) => 
	QAll(qf_of_term (map (fn(v,n) => (v,n + 1)) vs) p)
      | _ => error "qf_of_term : unknown term!";

(*
fun parse s = term_of (read_cterm (sign_of Main.thy) (s,HOLogic.boolT));

val t = parse "ALL (i::int) (j::int). i < 8* j --> (i - 1 = j + 3 + 2*j) & (j <= -i + k ) | 4 = i | 5 dvd i";
*)
fun zip [] [] = []
  | zip (x::xs) (y::ys) = (x,y)::(zip xs ys);


fun start_vs t =
    let val fs = term_frees t
    in zip fs (map nat (0 upto (length fs - 1)))
    end ;

(* transform intterm and QF back to terms *)
val iT = HOLogic.intT;
val bT = HOLogic.boolT;
fun myassoc2 l v =
    case l of
	[] => NONE
      | (x,v')::xs => if v = v' then SOME x
		      else myassoc2 xs v;

fun term_of_i vs t =
    case t of 
	Cst i => CooperDec.mk_numeral i
      | Var n => valOf (myassoc2 vs n)
      | Neg t' => Const("uminus",iT --> iT)$(term_of_i vs t')
      | Add(t1,t2) => Const("op +",[iT,iT] ---> iT)$
			   (term_of_i vs t1)$(term_of_i vs t2)
      | Sub(t1,t2) => Const("op -",[iT,iT] ---> iT)$
			   (term_of_i vs t1)$(term_of_i vs t2)
      | Mult(t1,t2) => Const("op *",[iT,iT] ---> iT)$
			   (term_of_i vs t1)$(term_of_i vs t2);

fun term_of_qf vs t = 
    case t of 
	T => HOLogic.true_const 
      | F => HOLogic.false_const
      | Lt(t1,t2) => Const("op <",[iT,iT] ---> bT)$
			   (term_of_i vs t1)$(term_of_i vs t2)
      | Le(t1,t2) => Const("op <=",[iT,iT] ---> bT)$
			  (term_of_i vs t1)$(term_of_i vs t2)
      | Gt(t1,t2) => Const("op <",[iT,iT] ---> bT)$
			   (term_of_i vs t2)$(term_of_i vs t1)
      | Ge(t1,t2) => Const("op <=",[iT,iT] ---> bT)$
			  (term_of_i vs t2)$(term_of_i vs t1)
      | Eq(t1,t2) => Const("op =",[iT,iT] ---> bT)$
			   (term_of_i vs t1)$(term_of_i vs t2)
      | Divides(t1,t2) => Const("Divides.op dvd",[iT,iT] ---> bT)$
			       (term_of_i vs t1)$(term_of_i vs t2)
      | NOT t' => HOLogic.Not$(term_of_qf vs t')
      | And(t1,t2) => HOLogic.conj$(term_of_qf vs t1)$(term_of_qf vs t2)
      | Or(t1,t2) => HOLogic.disj$(term_of_qf vs t1)$(term_of_qf vs t2)
      | Imp(t1,t2) => HOLogic.imp$(term_of_qf vs t1)$(term_of_qf vs t2)
      | Equ(t1,t2) => (HOLogic.eq_const bT)$(term_of_qf vs t1)$
					   (term_of_qf vs t2)
      | _ => error "If this is raised, Isabelle/HOL or generate_code is inconsistent!";

(* The oracle *)
 exception COOPER; 

fun presburger_oracle thy t =
    let val vs = start_vs t
	val result = lift_un (term_of_qf vs) (pa (qf_of_term vs t))
    in 
    case result of 
	None => raise COOPER
      | Some t' => HOLogic.mk_Trueprop (HOLogic.mk_eq(t,t'))
    end ;
 
end;