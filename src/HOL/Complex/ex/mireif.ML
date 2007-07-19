(*  Title:      HOL/Complex/ex/mireif.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Oracle for Mixed Real-Integer auantifier elimination
based on the verified code in HOL/Complex/ex/MIR.thy.
*)

structure ReflectedMir =
struct

open Mir;

exception MIR;

fun num_of_term vs t = 
    case t of
        Free(xn,xT) => (case AList.lookup (op =) vs t of 
                           NONE   => error "Variable not found in the list!"
                         | SOME n => Bound n)
      | Const("RealDef.real",_)$ @{term "0::int"} => C 0
      | Const("RealDef.real",_)$ @{term "1::int"} => C 1
      | @{term "0::real"} => C 0
      | @{term "1::real"} => C 1
      | Term.Bound i => Bound (nat i)
      | Const(@{const_name "HOL.uminus"},_)$t' => Neg (num_of_term vs t')
      | Const (@{const_name "HOL.plus"},_)$t1$t2 => Add (num_of_term vs t1,num_of_term vs t2)
      | Const (@{const_name "HOL.minus"},_)$t1$t2 => Sub (num_of_term vs t1,num_of_term vs t2)
      | Const (@{const_name "HOL.times"},_)$t1$t2 => 
        (case (num_of_term vs t1) of C i => 
                                     Mul (i,num_of_term vs t2)
                                   | _ => error "num_of_term: unsupported Multiplication")
      | Const("RealDef.real",_)$ (Const (@{const_name "RComplete.floor"},_)$ t') => Floor (num_of_term vs t')
      | Const("RealDef.real",_)$ (Const (@{const_name "RComplete.ceiling"},_)$ t') => Neg(Floor (Neg (num_of_term vs t')))
      | Const("RealDef.real",_) $ Const (@{const_name "Numeral.number_of"},_)$t' => C (HOLogic.dest_numeral t')
      | Const (@{const_name "Numeral.number_of"},_)$t' => C (HOLogic.dest_numeral t')
      | _ => error ("num_of_term: unknown term " ^ (Display.raw_string_of_term t));
        

(* pseudo reification : term -> fm *)
fun fm_of_term vs t = 
    case t of 
        Const("True",_) => T
      | Const("False",_) => F
      | Const(@{const_name "Orderings.less"},_)$t1$t2 => Lta (Sub (num_of_term vs t1,num_of_term vs t2))
      | Const(@{const_name "Orderings.less_eq"},_)$t1$t2 => Lea (Sub (num_of_term vs t1,num_of_term vs t2))
      | Const (@{const_name "MIR.rdvd"},_ )$ (Const("RealDef.real",_) $ (Const(@{const_name "Numeral.number_of"},_)$t1))$t2 => 
        Dvda (HOLogic.dest_numeral t1, num_of_term vs t2)
      | Const("op =",eqT)$t1$t2 => 
        if (domain_type eqT = @{typ real})
        then Eqa (Sub (num_of_term vs t1, num_of_term vs t2)) 
        else Iffa (fm_of_term vs t1, fm_of_term vs t2)
      | Const("op &",_)$t1$t2 => And (fm_of_term vs t1, fm_of_term vs t2)
      | Const("op |",_)$t1$t2 => Or (fm_of_term vs t1, fm_of_term vs t2)
      | Const("op -->",_)$t1$t2 => Impa (fm_of_term vs t1, fm_of_term vs t2)
      | Const("Not",_)$t' => Nota (fm_of_term vs t')
      | Const("Ex",_)$Abs(xn,xT,p) => 
        E (fm_of_term (map (fn (v, n) => (v, Suc n)) vs) p)
      | Const("All",_)$Abs(xn,xT,p) => 
        A (fm_of_term (map (fn(v, n) => (v, Suc n)) vs) p)
      | _ => error ("fm_of_term : unknown term!" ^ Display.raw_string_of_term t);

fun start_vs t =
    let val fs = term_frees t
    in fs ~~ map nat (0 upto  (length fs - 1))
    end ;

(* transform num and fm back to terms *)

fun myassoc2 l v =
    case l of
        [] => NONE
      | (x,v')::xs => if v = v' then SOME x
                      else myassoc2 xs v;

val realC = @{term "real :: int => _"};
val rzero = @{term "0::real"};

fun term_of_num vs t =
    case t of 
        C i => realC $ (HOLogic.mk_number HOLogic.intT i)
      | Bound n => valOf (myassoc2 vs n)
      | Neg (Floor (Neg t')) => realC $ (@{term "ceiling"} $ term_of_num vs t')
      | Neg t' => @{term "uminus:: real => _"} $ term_of_num vs t'
      | Add(t1,t2) => @{term "op +:: real => _"} $ term_of_num vs t1 $ term_of_num vs t2
      | Sub(t1,t2) => @{term "op -:: real => _"} $ term_of_num vs t1 $ term_of_num vs t2
      | Mul(i,t2) => @{term "op -:: real => _"} $ term_of_num vs (C i) $ term_of_num vs t2
      | Floor t => realC $ (@{term "floor"} $ term_of_num vs t)
      | Cn(n,i,t) => term_of_num vs (Add(Mul(i,Bound n),t))
      | Cf(c,t,s) => term_of_num vs (Add(Mul(c,Floor t),s));

fun term_of_fm vs t = 
    case t of 
        T => HOLogic.true_const 
      | F => HOLogic.false_const
      | Lta t => @{term "op <:: real => _"} $ term_of_num vs t $ rzero
      | Lea t => @{term "op <=:: real => _"} $ term_of_num vs t $ rzero
      | Gta t => @{term "op <:: real => _"}$ rzero $ term_of_num vs t
      | Gea t => @{term "op <=:: real => _"} $ rzero $ term_of_num vs t
      | Eqa t => @{term "op = :: real => _"}$ term_of_num vs t $ rzero
      | NEq t => term_of_fm vs (Nota (Eqa t))
      | NDvd (i,t) => term_of_fm vs (Nota (Dvda (i,t)))
      | Dvda (i,t) => @{term "op rdvd"} $ term_of_num vs (C i) $ term_of_num vs t
      | Nota t' => HOLogic.Not$(term_of_fm vs t')
      | And(t1,t2) => HOLogic.conj $ term_of_fm vs t1 $ term_of_fm vs t2
      | Or(t1,t2) => HOLogic.disj $ term_of_fm vs t1 $ term_of_fm vs t2
      | Impa(t1,t2) => HOLogic.imp $ term_of_fm vs t1 $ term_of_fm vs t2
      | Iffa(t1,t2) => HOLogic.mk_eq (term_of_fm vs t1, term_of_fm vs t2)
      | _ => error "If this is raised, Isabelle/HOL or generate_code is inconsistent!";

(* The oracle *)

fun mircfr_oracle thy t = 
    let 
        val vs = start_vs t
    in HOLogic.mk_Trueprop (HOLogic.mk_eq(t, term_of_fm vs (mircfrqe (fm_of_term vs t))))
    end;

fun mirlfr_oracle thy t = 
    let 
        val vs = start_vs t
    in HOLogic.mk_Trueprop (HOLogic.mk_eq(t, term_of_fm vs (mirlfrqe (fm_of_term vs t))))
    end;

end;
