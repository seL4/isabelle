(* $Id$ *)

(* Reification for the autimatically generated oracle for Presburger arithmetic 
   in HOL/ex/Reflected_Presburger.thy 
 Author : Amine Chaieb
*)

structure Coopereif =
struct

open GeneratedCooper;

fun i_of_term vs t = 
    case t of
	Free(xn,xT) => (case AList.lookup (op aconv) vs t of 
			   NONE   => error "Variable not found in the list!!"
			 | SOME n => Bound n)
      | @{term "0::int"} => C 0
      | @{term "1::int"} => C 1
      | Term.Bound i => Bound (nat (IntInf.fromInt i))
      | Const(@{const_name "HOL.uminus"},_)$t' => Neg (i_of_term vs t')
      | Const(@{const_name "HOL.plus"},_)$t1$t2 => Add (i_of_term vs t1,i_of_term vs t2)
      | Const(@{const_name "HOL.minus"},_)$t1$t2 => Sub (i_of_term vs t1,i_of_term vs t2)
      | Const(@{const_name "HOL.times"},_)$t1$t2 => 
	     (Mul (HOLogic.dest_number t1 |> snd,i_of_term vs t2)
        handle TERM _ => 
           (Mul (HOLogic.dest_number t2 |> snd,i_of_term vs t1)
            handle TERM _ => error "i_of_term: Unsupported kind of multiplication"))
      | _ => (C (HOLogic.dest_number t |> snd) 
               handle TERM _ => error "i_of_term: unknown term");
	
fun qf_of_term ps vs t = 
    case t of 
	Const("True",_) => T
      | Const("False",_) => F
      | Const(@{const_name "Orderings.less"},_)$t1$t2 => Lt (Sub (i_of_term vs t1,i_of_term vs t2))
      | Const(@{const_name "Orderings.less_eq"},_)$t1$t2 => Le (Sub(i_of_term vs t1,i_of_term vs t2))
      | Const(@{const_name "Divides.dvd"},_)$t1$t2 => 
	(Dvd(HOLogic.dest_number t1 |> snd, i_of_term vs t2) handle _ => error "qf_of_term: unsupported dvd")
      | @{term "op = :: int => _"}$t1$t2 => Eq (Sub (i_of_term vs t1,i_of_term vs t2))
      | @{term "op = :: bool => _ "}$t1$t2 => Iff(qf_of_term ps vs t1,qf_of_term ps vs t2)
      | Const("op &",_)$t1$t2 => And(qf_of_term ps vs t1,qf_of_term ps vs t2)
      | Const("op |",_)$t1$t2 => Or(qf_of_term ps vs t1,qf_of_term ps vs t2)
      | Const("op -->",_)$t1$t2 => Imp(qf_of_term ps vs t1,qf_of_term ps vs t2)
      | Const("Not",_)$t' => NOT(qf_of_term ps vs t')
      | Const("Ex",_)$Abs(xn,xT,p) => 
         let val (xn',p') = variant_abs (xn,xT,p)
             val vs' = (Free (xn',xT), nat 0) :: (map (fn(v,n) => (v,1 + n)) vs)
         in E (qf_of_term ps vs' p')
         end
      | Const("All",_)$Abs(xn,xT,p) => 
         let val (xn',p') = variant_abs (xn,xT,p)
             val vs' = (Free (xn',xT), nat 0) :: (map (fn(v,n) => (v,1 + n)) vs)
         in A (qf_of_term ps vs' p')
         end
      | _ =>(case AList.lookup (op aconv) ps t of 
               NONE => error "qf_of_term ps : unknown term!"
             | SOME n => Closed n);

local
 val ops = [@{term "op &"}, @{term "op |"}, @{term "op -->"}, @{term "op = :: bool => _"},
             @{term "op = :: int => _"}, @{term "op < :: int => _"}, 
             @{term "op <= :: int => _"}, @{term "Not"}, @{term "All:: (int => _) => _"}, 
             @{term "Ex:: (int => _) => _"}, @{term "True"}, @{term "False"}]
fun ty t = Bool.not (fastype_of t = HOLogic.boolT)
in
fun term_bools acc t =
case t of 
    (l as f $ a) $ b => if ty t orelse f mem ops then term_bools (term_bools acc l)b 
            else insert (op aconv) t acc
  | f $ a => if ty t orelse f mem ops then term_bools (term_bools acc f) a  
            else insert (op aconv) t acc
  | Abs p => term_bools acc (snd (variant_abs p))
  | _ => if ty t orelse t mem ops then acc else insert (op aconv) t acc
end;
 

fun start_vs t =
let
 val fs = term_frees t
 val ps = term_bools [] t
in (fs ~~ (map (nat o IntInf.fromInt) (0 upto  (length fs - 1))),
    ps ~~ (map (nat o IntInf.fromInt) (0 upto  (length ps - 1))))
end ;

val iT = HOLogic.intT;
val bT = HOLogic.boolT;
fun myassoc2 l v =
    case l of
	[] => NONE
      | (x,v')::xs => if v = v' then SOME x
		      else myassoc2 xs v;

fun term_of_i vs t =
    case t of 
	C i => HOLogic.mk_number HOLogic.intT i
      | Bound n => valOf (myassoc2 vs n)
      | Neg t' => @{term "uminus :: int => _"}$(term_of_i vs t')
      | Add(t1,t2) => @{term "op +:: int => _"}$ (term_of_i vs t1)$(term_of_i vs t2)
      | Sub(t1,t2) => Const(@{const_name "HOL.minus"},[iT,iT] ---> iT)$
			   (term_of_i vs t1)$(term_of_i vs t2)
      | Mul(i,t2) => Const(@{const_name "HOL.times"},[iT,iT] ---> iT)$
			   (HOLogic.mk_number HOLogic.intT i)$(term_of_i vs t2)
      | CX(i,t')=> term_of_i vs (Add(Mul (i,Bound (nat 0)),t'));

fun term_of_qf ps vs t = 
 case t of 
   T => HOLogic.true_const 
 | F => HOLogic.false_const
 | Lt t' => @{term "op < :: int => _ "}$ term_of_i vs t'$ @{term "0::int"}
 | Le t' => @{term "op <= :: int => _ "}$ term_of_i vs t' $ @{term "0::int"}
 | Gt t' => @{term "op < :: int => _ "}$ @{term "0::int"}$ term_of_i vs t'
 | Ge t' => @{term "op <= :: int => _ "}$ @{term "0::int"}$ term_of_i vs t'
 | Eq t' => @{term "op = :: int => _ "}$ term_of_i vs t'$ @{term "0::int"}
 | NEq t' => term_of_qf ps vs (NOT(Eq t'))
 | Dvd(i,t') => @{term "op dvd :: int => _ "}$ 
                 (HOLogic.mk_number HOLogic.intT i)$(term_of_i vs t')
 | NDvd(i,t')=> term_of_qf ps vs (NOT(Dvd(i,t')))
 | NOT t' => HOLogic.Not$(term_of_qf ps vs t')
 | And(t1,t2) => HOLogic.conj$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Or(t1,t2) => HOLogic.disj$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Imp(t1,t2) => HOLogic.imp$(term_of_qf ps vs t1)$(term_of_qf ps vs t2)
 | Iff(t1,t2) => (HOLogic.eq_const bT)$(term_of_qf ps vs t1)$ (term_of_qf ps vs t2)
 | Closed n => valOf (myassoc2 ps n)
 | NClosed n => term_of_qf ps vs (NOT (Closed n))
 | _ => error "If this is raised, Isabelle/HOL or generate_code is inconsistent!";

(* The oracle *)
fun cooper_oracle thy t = 
    let val (vs,ps) = start_vs t
    in HOLogic.mk_Trueprop (HOLogic.mk_eq (t, term_of_qf ps vs (pa (qf_of_term ps vs t))))
    end;

end;