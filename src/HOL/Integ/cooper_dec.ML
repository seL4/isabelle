(*  Title:      HOL/Integ/cooper_dec.ML
    ID:         $Id$
    Author:     Amine Chaieb and Tobias Nipkow, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

File containing the implementation of Cooper Algorithm
decision procedure (intensively inspired from J.Harrison)
*)


signature COOPER_DEC = 
sig
  exception COOPER
  exception COOPER_ORACLE of term
  val is_arith_rel : term -> bool
  val mk_numeral : int -> term
  val dest_numeral : term -> int
  val zero : term
  val one : term
  val linear_cmul : int -> term -> term
  val linear_add : string list -> term -> term -> term 
  val linear_sub : string list -> term -> term -> term 
  val linear_neg : term -> term
  val lint : string list -> term -> term
  val linform : string list -> term -> term
  val formlcm : term -> term -> int
  val adjustcoeff : term -> int -> term -> term
  val unitycoeff : term -> term -> term
  val divlcm : term -> term -> int
  val bset : term -> term -> term list
  val aset : term -> term -> term list
  val linrep : string list -> term -> term -> term -> term
  val list_disj : term list -> term
  val list_conj : term list -> term
  val simpl : term -> term
  val fv : term -> string list
  val negate : term -> term
  val operations : (string * (int * int -> bool)) list
  val conjuncts : term -> term list
  val disjuncts : term -> term list
  val has_bound : term -> bool
  val minusinf : term -> term -> term
  val plusinf : term -> term -> term
  val onatoms : (term -> term) -> term -> term
  val evalc : term -> term
  val integer_qelim : Term.term -> Term.term
  val mk_presburger_oracle : (Sign.sg * exn) -> term
end;

structure  CooperDec : COOPER_DEC =
struct

(* ========================================================================= *) 
(* Cooper's algorithm for Presburger arithmetic.                             *) 
(* ========================================================================= *) 
exception COOPER;

(* Exception for the oracle *)
exception COOPER_ORACLE of term;


(* ------------------------------------------------------------------------- *) 
(* Lift operations up to numerals.                                           *) 
(* ------------------------------------------------------------------------- *) 
 
(*Assumption : The construction of atomar formulas in linearl arithmetic is based on 
relation operations of Type : [int,int]---> bool *) 
 
(* ------------------------------------------------------------------------- *) 
 
(*Function is_arith_rel returns true if and only if the term is an atomar presburger 
formula *) 
fun is_arith_rel tm = case tm of 
	 Const(p,Type ("fun",[Type ("Numeral.bin", []),Type ("fun",[Type ("Numeral.bin", 
	 []),Type ("bool",[])] )])) $ _ $_ => true 
	|Const(p,Type ("fun",[Type ("IntDef.int", []),Type ("fun",[Type ("IntDef.int", 
	 []),Type ("bool",[])] )])) $ _ $_ => true 
	|_ => false; 
 
(*Function is_arith_rel returns true if and only if the term is an operation of the 
form [int,int]---> int*) 
 
(*Transform a natural number to a term*) 
 
fun mk_numeral 0 = Const("0",HOLogic.intT)
   |mk_numeral 1 = Const("1",HOLogic.intT)
   |mk_numeral n = (HOLogic.number_of_const HOLogic.intT) $ (HOLogic.mk_bin n); 
 
(*Transform an Term to an natural number*)	  
	  
fun dest_numeral (Const("0",Type ("IntDef.int", []))) = 0
   |dest_numeral (Const("1",Type ("IntDef.int", []))) = 1
   |dest_numeral (Const ("Numeral.number_of",_) $ n)= HOLogic.dest_binum n; 
(*Some terms often used for pattern matching*) 
 
val zero = mk_numeral 0; 
val one = mk_numeral 1; 
 
(*Tests if a Term is representing a number*) 
 
fun is_numeral t = (t = zero) orelse (t = one) orelse (can dest_numeral t); 
 
(*maps a unary natural function on a term containing an natural number*) 
 
fun numeral1 f n = mk_numeral (f(dest_numeral n)); 
 
(*maps a binary natural function on 2 term containing  natural numbers*) 
 
fun numeral2 f m n = mk_numeral(f(dest_numeral m) (dest_numeral n)); 
 
(* ------------------------------------------------------------------------- *) 
(* Operations on canonical linear terms c1 * x1 + ... + cn * xn + k          *) 
(*                                                                           *) 
(* Note that we're quite strict: the ci must be present even if 1            *) 
(* (but if 0 we expect the monomial to be omitted) and k must be there       *) 
(* even if it's zero. Thus, it's a constant iff not an addition term.        *) 
(* ------------------------------------------------------------------------- *) 
 
 
fun linear_cmul n tm =  if n = 0 then zero else let fun times n k = n*k in  
  ( case tm of  
     (Const("op +",T)  $  (Const ("op *",T1 ) $c1 $  x1) $ rest) => 
       Const("op +",T) $ ((Const("op *",T1) $ (numeral1 (times n) c1) $ x1)) $ (linear_cmul n rest) 
    |_ =>  numeral1 (times n) tm) 
    end ; 
 
 
 
 
(* Whether the first of two items comes earlier in the list  *) 
fun earlier [] x y = false 
	|earlier (h::t) x y =if h = y then false 
              else if h = x then true 
              	else earlier t x y ; 
 
fun earlierv vars (Bound i) (Bound j) = i < j 
   |earlierv vars (Bound _) _ = true 
   |earlierv vars _ (Bound _)  = false 
   |earlierv vars (Free (x,_)) (Free (y,_)) = earlier vars x y; 
 
 
fun linear_add vars tm1 tm2 = 
  let fun addwith x y = x + y in
 (case (tm1,tm2) of 
	((Const ("op +",T1) $ ( Const("op *",T2) $ c1 $  x1) $ rest1),(Const 
	("op +",T3)$( Const("op *",T4) $ c2 $  x2) $ rest2)) => 
         if x1 = x2 then 
              let val c = (numeral2 (addwith) c1 c2) 
	      in 
              if c = zero then (linear_add vars rest1  rest2)  
	      else (Const("op +",T1) $ (Const("op *",T2) $ c $ x1) $ (linear_add vars  rest1 rest2)) 
              end 
	   else 
		if earlierv vars x1 x2 then (Const("op +",T1) $  
		(Const("op *",T2)$ c1 $ x1) $ (linear_add vars rest1 tm2)) 
    	       else (Const("op +",T1) $ (Const("op *",T2) $ c2 $ x2) $ (linear_add vars tm1 rest2)) 
   	|((Const("op +",T1) $ (Const("op *",T2) $ c1 $ x1) $ rest1) ,_) => 
    	  (Const("op +",T1)$ (Const("op *",T2) $ c1 $ x1) $ (linear_add vars 
	  rest1 tm2)) 
   	|(_, (Const("op +",T1) $(Const("op *",T2) $ c2 $ x2) $ rest2)) => 
      	  (Const("op +",T1) $ (Const("op *",T2) $ c2 $ x2) $ (linear_add vars tm1 
	  rest2)) 
   	| (_,_) => numeral2 (addwith) tm1 tm2) 
	 
	end; 
 
(*To obtain the unary - applyed on a formula*) 
 
fun linear_neg tm = linear_cmul (0 - 1) tm; 
 
(*Substraction of two terms *) 
 
fun linear_sub vars tm1 tm2 = linear_add vars tm1 (linear_neg tm2); 
 
 
(* ------------------------------------------------------------------------- *) 
(* Linearize a term.                                                         *) 
(* ------------------------------------------------------------------------- *) 
 
(* linearises a term from the point of view of Variable Free (x,T). 
After this fuction the all expressions containig ths variable will have the form  
 c*Free(x,T) + t where c is a constant ant t is a Term which is not containing 
 Free(x,T)*) 
  
fun lint vars tm = if is_numeral tm then tm else case tm of 
   (Free (x,T)) =>  (HOLogic.mk_binop "op +" ((HOLogic.mk_binop "op *" ((mk_numeral 1),Free (x,T))), zero)) 
  |(Bound i) =>  (Const("op +",HOLogic.intT -->HOLogic.intT -->HOLogic.intT) $ 
  (Const("op *",HOLogic.intT -->HOLogic.intT -->HOLogic.intT) $ (mk_numeral 1) $ (Bound i)) $ zero) 
  |(Const("uminus",_) $ t ) => (linear_neg (lint vars t)) 
  |(Const("op +",_) $ s $ t) => (linear_add vars (lint vars s) (lint vars t)) 
  |(Const("op -",_) $ s $ t) => (linear_sub vars (lint vars s) (lint vars t)) 
  |(Const ("op *",_) $ s $ t) => 
        let val s' = lint vars s  
            val t' = lint vars t  
        in 
        if is_numeral s' then (linear_cmul (dest_numeral s') t') 
        else if is_numeral t' then (linear_cmul (dest_numeral t') s') 
 
         else (warning "lint: apparent nonlinearity"; raise COOPER)
         end 
  |_ =>   (error "COOPER:lint: unknown term  ")
   
 
 
(* ------------------------------------------------------------------------- *) 
(* Linearize the atoms in a formula, and eliminate non-strict inequalities.  *) 
(* ------------------------------------------------------------------------- *) 
 
fun mkatom vars p t = Const(p,HOLogic.intT --> HOLogic.intT --> HOLogic.boolT) $ zero $ (lint vars t); 
 
fun linform vars (Const ("Divides.op dvd",_) $ c $ t) =  
      let val c' = (mk_numeral(abs(dest_numeral c)))  
      in (HOLogic.mk_binrel "Divides.op dvd" (c,lint vars t)) 
      end 
  |linform vars  (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ s $ t ) = (mkatom vars "op =" (Const ("op -",HOLogic.intT --> HOLogic.intT --> HOLogic.intT) $ t $ s) ) 
  |linform vars  (Const("op <",_)$ s $t ) = (mkatom vars "op <" (Const ("op -",HOLogic.intT --> HOLogic.intT --> HOLogic.intT) $ t $ s))
  |linform vars  (Const("op >",_) $ s $ t ) = (mkatom vars "op <" (Const ("op -",HOLogic.intT --> HOLogic.intT --> HOLogic.intT) $ s $ t)) 
  |linform vars  (Const("op <=",_)$ s $ t ) = 
        (mkatom vars "op <" (Const ("op -",HOLogic.intT --> HOLogic.intT --> HOLogic.intT) $ (Const("op +",HOLogic.intT --> HOLogic.intT --> HOLogic.intT) $t $(mk_numeral 1)) $ s)) 
  |linform vars  (Const("op >=",_)$ s $ t ) = 
        (mkatom vars "op <" (Const ("op -",HOLogic.intT --> HOLogic.intT --> 
	HOLogic.intT) $ (Const("op +",HOLogic.intT --> HOLogic.intT --> 
	HOLogic.intT) $s $(mk_numeral 1)) $ t)) 
 
   |linform vars  fm =  fm; 
 
(* ------------------------------------------------------------------------- *) 
(* Post-NNF transformation eliminating negated inequalities.                 *) 
(* ------------------------------------------------------------------------- *) 
 
fun posineq fm = case fm of  
 (Const ("Not",_)$(Const("op <",_)$ c $ t)) =>
   (HOLogic.mk_binrel "op <"  (zero , (linear_sub [] (mk_numeral 1) (linear_add [] c t ) ))) 
  | ( Const ("op &",_) $ p $ q)  => HOLogic.mk_conj (posineq p,posineq q)
  | ( Const ("op |",_) $ p $ q ) => HOLogic.mk_disj (posineq p,posineq q)
  | _ => fm; 
  

(* ------------------------------------------------------------------------- *) 
(* Find the LCM of the coefficients of x.                                    *) 
(* ------------------------------------------------------------------------- *) 
(*gcd calculates gcd (a,b) and helps lcm_num calculating lcm (a,b)*) 
 
fun gcd a b = if a=0 then b else gcd (b mod a) a ; 
fun lcm_num a b = (abs a*b) div (gcd (abs a) (abs b)); 
 
fun formlcm x fm = case fm of 
    (Const (p,_)$ _ $(Const ("op +", _)$(Const ("op *",_)$ c $ y ) $z ) ) =>  if 
    (is_arith_rel fm) andalso (x = y) then abs(dest_numeral c) else 1 
  | ( Const ("Not", _) $p) => formlcm x p 
  | ( Const ("op &",_) $ p $ q) => lcm_num (formlcm x p) (formlcm x q) 
  | ( Const ("op |",_) $ p $ q )=> lcm_num (formlcm x p) (formlcm x q) 
  |  _ => 1; 
 
(* ------------------------------------------------------------------------- *) 
(* Adjust all coefficients of x in formula; fold in reduction to +/- 1.      *) 
(* ------------------------------------------------------------------------- *) 
 
fun adjustcoeff x l fm = 
     case fm of  
      (Const(p,_) $d $( Const ("op +", _)$(Const ("op *",_) $ 
      c $ y ) $z )) => if (is_arith_rel fm) andalso (x = y) then  
        let val m = l div (dest_numeral c) 
            val n = (if p = "op <" then abs(m) else m) 
            val xtm = HOLogic.mk_binop "op *" ((mk_numeral (m div n)), x) 
	in
        (HOLogic.mk_binrel p ((linear_cmul n d),(HOLogic.mk_binop "op +" ( xtm ,( linear_cmul n z) )))) 
	end 
	else fm 
  |( Const ("Not", _) $ p) => HOLogic.Not $ (adjustcoeff x l p) 
  |( Const ("op &",_) $ p $ q) => HOLogic.conj$(adjustcoeff x l p) $(adjustcoeff x l q) 
  |( Const ("op |",_) $ p $ q) => HOLogic.disj $(adjustcoeff x l p)$ (adjustcoeff x l q) 
  |_ => fm; 
 
(* ------------------------------------------------------------------------- *) 
(* Hence make coefficient of x one in existential formula.                   *) 
(* ------------------------------------------------------------------------- *) 
 
fun unitycoeff x fm = 
  let val l = formlcm x fm 
      val fm' = adjustcoeff x l fm in
     if l = 1 then fm' else 
     let val xp = (HOLogic.mk_binop "op +"  
     		((HOLogic.mk_binop "op *" ((mk_numeral 1), x )), zero)) in 
      HOLogic.conj $(HOLogic.mk_binrel "Divides.op dvd" ((mk_numeral l) , xp )) $ (adjustcoeff x l fm) 
      end 
  end; 
 
(* adjustcoeffeq l fm adjusts the coeffitients c_i of x  overall in fm to l*)
(* Here l must be a multiple of all c_i otherwise the obtained formula is not equivalent*)
(*
fun adjustcoeffeq x l fm = 
    case fm of  
      (Const(p,_) $d $( Const ("op +", _)$(Const ("op *",_) $ 
      c $ y ) $z )) => if (is_arith_rel fm) andalso (x = y) then  
        let val m = l div (dest_numeral c) 
            val n = (if p = "op <" then abs(m) else m)  
            val xtm = (HOLogic.mk_binop "op *" ((mk_numeral ((m div n)*l) ), x))
            in (HOLogic.mk_binrel p ((linear_cmul n d),(HOLogic.mk_binop "op +" ( xtm ,( linear_cmul n z) )))) 
	    end 
	else fm 
  |( Const ("Not", _) $ p) => HOLogic.Not $ (adjustcoeffeq x l p) 
  |( Const ("op &",_) $ p $ q) => HOLogic.conj$(adjustcoeffeq x l p) $(adjustcoeffeq x l q) 
  |( Const ("op |",_) $ p $ q) => HOLogic.disj $(adjustcoeffeq x l p)$ (adjustcoeffeq x l q) 
  |_ => fm;
 

*)

(* ------------------------------------------------------------------------- *) 
(* The "minus infinity" version.                                             *) 
(* ------------------------------------------------------------------------- *) 
 
fun minusinf x fm = case fm of  
    (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ (c1 ) $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) => 
  	 if (is_arith_rel fm) andalso (x=y) andalso (c2 = one) andalso (c1 =zero) then HOLogic.false_const  
	 				 else fm 
 
  |(Const("op <",_) $ c $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z 
  )) => 
        if (x =y) andalso (pm1 = one) andalso (c = zero) then HOLogic.false_const else HOLogic.true_const 
	 
  |(Const ("Not", _) $ p) => HOLogic.Not $ (minusinf x p) 
  |(Const ("op &",_) $ p $ q) => HOLogic.conj $ (minusinf x p) $ (minusinf x q) 
  |(Const ("op |",_) $ p $ q) => HOLogic.disj $ (minusinf x p) $ (minusinf x q) 
  |_ => fm; 

(* ------------------------------------------------------------------------- *)
(* The "Plus infinity" version.                                             *)
(* ------------------------------------------------------------------------- *)

fun plusinf x fm = case fm of
    (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ (c1 ) $(Const ("op +", _) $(Const ("op *",_) $ c2 $ y) $z)) =>
  	 if (is_arith_rel fm) andalso (x=y) andalso (c2 = one) andalso (c1 =zero) then HOLogic.false_const
	 				 else fm

  |(Const("op <",_) $ c $(Const ("op +", _) $(Const ("op *",_) $ pm1 $ y ) $ z
  )) =>
        if (x =y) andalso (pm1 = one) andalso (c = zero) then HOLogic.true_const else HOLogic.false_const

  |(Const ("Not", _) $ p) => HOLogic.Not $ (plusinf x p)
  |(Const ("op &",_) $ p $ q) => HOLogic.conj $ (plusinf x p) $ (plusinf x q)
  |(Const ("op |",_) $ p $ q) => HOLogic.disj $ (plusinf x p) $ (plusinf x q)
  |_ => fm;
 
(* ------------------------------------------------------------------------- *) 
(* The LCM of all the divisors that involve x.                               *) 
(* ------------------------------------------------------------------------- *) 
 
fun divlcm x (Const("Divides.op dvd",_)$ d $ (Const ("op +",_) $ (Const ("op *",_) $ c $ y ) $ z ) ) =  
        if x = y then abs(dest_numeral d) else 1 
  |divlcm x ( Const ("Not", _) $ p) = divlcm x p 
  |divlcm x ( Const ("op &",_) $ p $ q) = lcm_num (divlcm x p) (divlcm x q) 
  |divlcm x ( Const ("op |",_) $ p $ q ) = lcm_num (divlcm x p) (divlcm x q) 
  |divlcm x  _ = 1; 
 
(* ------------------------------------------------------------------------- *) 
(* Construct the B-set.                                                      *) 
(* ------------------------------------------------------------------------- *) 
 
fun bset x fm = case fm of 
   (Const ("Not", _) $ p) => if (is_arith_rel p) then  
          (case p of  
	      (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $c2 $y) $a ) )  
	             => if (is_arith_rel p) andalso (x=	y) andalso (c2 = one) andalso (c1 = zero)  
	                then [linear_neg a] 
			else  bset x p 
   	  |_ =>[]) 
			 
			else bset x p 
  |(Const ("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +",_) $ (Const ("op *",_) $c2 $ x) $ a)) =>  if (c1 =zero) andalso (c2 = one) then [linear_neg(linear_add [] a (mk_numeral 1))]  else [] 
  |(Const ("op <",_) $ c1$ (Const ("op +",_) $(Const ("op *",_)$ c2 $ x) $ a)) => if (c1 =zero) andalso (c2 = one) then [linear_neg a] else [] 
  |(Const ("op &",_) $ p $ q) => (bset x p) union (bset x q) 
  |(Const ("op |",_) $ p $ q) => (bset x p) union (bset x q) 
  |_ => []; 
 
(* ------------------------------------------------------------------------- *)
(* Construct the A-set.                                                      *)
(* ------------------------------------------------------------------------- *)

fun aset x fm = case fm of
   (Const ("Not", _) $ p) => if (is_arith_rel p) then
          (case p of
	      (Const("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +", _) $(Const ("op *",_) $c2 $y) $a ) )
	             => if (x=	y) andalso (c2 = one) andalso (c1 = zero)
	                then [linear_neg a]
			else  []
   	  |_ =>[])

			else aset x p
  |(Const ("op =",Type ("fun",[Type ("IntDef.int", []),_])) $ c1 $ (Const ("op +",_) $ (Const ("op *",_) $c2 $ x) $ a)) =>  if (c1 =zero) andalso (c2 = one) then [linear_sub [] (mk_numeral 1) a]  else []
  |(Const ("op <",_) $ c1$ (Const ("op +",_) $(Const ("op *",_)$ c2 $ x) $ a)) => if (c1 =zero) andalso (c2 = (mk_numeral (~1))) then [a] else []
  |(Const ("op &",_) $ p $ q) => (aset x p) union (aset x q)
  |(Const ("op |",_) $ p $ q) => (aset x p) union (aset x q)
  |_ => [];


(* ------------------------------------------------------------------------- *) 
(* Replace top variable with another linear form, retaining canonicality.    *) 
(* ------------------------------------------------------------------------- *) 
 
fun linrep vars x t fm = case fm of  
   ((Const(p,_)$ d $ (Const("op +",_)$(Const("op *",_)$ c $ y) $ z))) => 
      if (x = y) andalso (is_arith_rel fm)  
      then  
        let val ct = linear_cmul (dest_numeral c) t  
	in (HOLogic.mk_binrel p (d, linear_add vars ct z)) 
	end 
	else fm 
  |(Const ("Not", _) $ p) => HOLogic.Not $ (linrep vars x t p) 
  |(Const ("op &",_) $ p $ q) => HOLogic.conj $ (linrep vars x t p) $ (linrep vars x t q) 
  |(Const ("op |",_) $ p $ q) => HOLogic.disj $ (linrep vars x t p) $ (linrep vars x t q) 
  |_ => fm; 
 
(* ------------------------------------------------------------------------- *) 
(* Evaluation of constant expressions.                                       *) 
(* ------------------------------------------------------------------------- *) 
 
val operations = 
  [("op =",op=), ("op <",op<), ("op >",op>), ("op <=",op<=) , ("op >=",op>=), 
   ("Divides.op dvd",fn (x,y) =>((y mod x) = 0))]; 
 
fun applyoperation (Some f) (a,b) = f (a, b) 
    |applyoperation _ (_, _) = false; 
 
(*Evaluation of constant atomic formulas*) 
 
fun evalc_atom at = case at of  
      (Const (p,_) $ s $ t) =>(  
         case assoc (operations,p) of 
             Some f => ((if (f ((dest_numeral s),(dest_numeral t))) then HOLogic.true_const else HOLogic.false_const)  
              handle _ => at) 
             | _ =>  at) 
     |Const("Not",_)$(Const (p,_) $ s $ t) =>(  
         case assoc (operations,p) of 
             Some f => ((if (f ((dest_numeral s),(dest_numeral t))) then 
	     HOLogic.false_const else HOLogic.true_const)  
              handle _ => at) 
             | _ =>  at) 
     | _ =>  at; 
 
(*Function onatoms apllys function f on the atomic formulas involved in a.*) 
 
fun onatoms f a = if (is_arith_rel a) then f a else case a of 
 
  	(Const ("Not",_) $ p) => if is_arith_rel p then HOLogic.Not $ (f p) 
				 
				else HOLogic.Not $ (onatoms f p) 
  	|(Const ("op &",_) $ p $ q) => HOLogic.conj $ (onatoms f p) $ (onatoms f q) 
  	|(Const ("op |",_) $ p $ q) => HOLogic.disj $ (onatoms f p) $ (onatoms f q) 
  	|(Const ("op -->",_) $ p $ q) => HOLogic.imp $ (onatoms f p) $ (onatoms f q) 
  	|((Const ("op =", Type ("fun",[Type ("bool", []),_]))) $ p $ q) => (Const ("op =", [HOLogic.boolT, HOLogic.boolT] ---> HOLogic.boolT)) $ (onatoms f p) $ (onatoms f q) 
  	|(Const("All",_) $ Abs(x,T,p)) => Const("All", [HOLogic.intT --> 
	HOLogic.boolT] ---> HOLogic.boolT)$ Abs (x ,T, (onatoms f p)) 
  	|(Const("Ex",_) $ Abs(x,T,p)) => Const("Ex", [HOLogic.intT --> HOLogic.boolT]---> HOLogic.boolT) $ Abs( x ,T, (onatoms f p)) 
  	|_ => a; 
 
val evalc = onatoms evalc_atom; 
 
(* ------------------------------------------------------------------------- *) 
(* Hence overall quantifier elimination.                                     *) 
(* ------------------------------------------------------------------------- *) 
 
(*Applyes a function iteratively on the list*) 
 
fun end_itlist f []     = error "end_itlist" 
   |end_itlist f [x]    = x 
   |end_itlist f (h::t) = f h (end_itlist f t); 
 
 
(*list_disj[conj] makes a disj[conj] of a given list. used with conjucts or disjuncts 
it liearises iterated conj[disj]unctions. *) 
 
fun disj_help p q = HOLogic.disj $ p $ q ; 
 
fun list_disj l = 
  if l = [] then HOLogic.false_const else end_itlist disj_help l; 
   
fun conj_help p q = HOLogic.conj $ p $ q ; 
 
fun list_conj l = 
  if l = [] then HOLogic.true_const else end_itlist conj_help l; 
   
(*Simplification of Formulas *) 
 
(*Function q_bnd_chk checks if a quantified Formula makes sens : Means if in 
the body of the existential quantifier there are bound variables to the 
existential quantifier.*) 
 
fun has_bound fm =let fun has_boundh fm i = case fm of 
		 Bound n => (i = n) 
		 |Abs (_,_,p) => has_boundh p (i+1) 
		 |t1 $ t2 => (has_boundh t1 i) orelse (has_boundh t2 i) 
		 |_ =>false

in  case fm of 
	Bound _ => true 
       |Abs (_,_,p) => has_boundh p 0 
       |t1 $ t2 => (has_bound t1 ) orelse (has_bound t2 ) 
       |_ =>false
end;
 
(*has_sub_abs checks if in a given Formula there are subformulas which are quantifed 
too. Is no used no more.*) 
 
fun has_sub_abs fm = case fm of  
		 Abs (_,_,_) => true 
		 |t1 $ t2 => (has_bound t1 ) orelse (has_bound t2 ) 
		 |_ =>false ; 
		  
(*update_bounds called with i=0 udates the numeration of bounded variables because the 
formula will not be quantified any more.*) 
 
fun update_bounds fm i = case fm of 
		 Bound n => if n >= i then Bound (n-1) else fm 
		 |Abs (x,T,p) => Abs(x,T,(update_bounds p (i+1))) 
		 |t1 $ t2 => (update_bounds t1 i) $ (update_bounds t2 i) 
		 |_ => fm ; 
 
(*psimpl : Simplification of propositions (general purpose)*) 
fun psimpl1 fm = case fm of 
    Const("Not",_) $ Const ("False",_) => HOLogic.true_const 
  | Const("Not",_) $ Const ("True",_) => HOLogic.false_const 
  | Const("op &",_) $ Const ("False",_) $ q => HOLogic.false_const 
  | Const("op &",_) $ p $ Const ("False",_)  => HOLogic.false_const 
  | Const("op &",_) $ Const ("True",_) $ q => q 
  | Const("op &",_) $ p $ Const ("True",_) => p 
  | Const("op |",_) $ Const ("False",_) $ q => q 
  | Const("op |",_) $ p $ Const ("False",_)  => p 
  | Const("op |",_) $ Const ("True",_) $ q => HOLogic.true_const 
  | Const("op |",_) $ p $ Const ("True",_)  => HOLogic.true_const 
  | Const("op -->",_) $ Const ("False",_) $ q => HOLogic.true_const 
  | Const("op -->",_) $ Const ("True",_) $  q => q 
  | Const("op -->",_) $ p $ Const ("True",_)  => HOLogic.true_const 
  | Const("op -->",_) $ p $ Const ("False",_)  => HOLogic.Not $  p 
  | Const("op =", Type ("fun",[Type ("bool", []),_])) $ Const ("True",_) $ q => q 
  | Const("op =", Type ("fun",[Type ("bool", []),_])) $ p $ Const ("True",_) => p 
  | Const("op =", Type ("fun",[Type ("bool", []),_])) $ Const ("False",_) $ q => HOLogic.Not $  q 
  | Const("op =", Type ("fun",[Type ("bool", []),_])) $ p $ Const ("False",_)  => HOLogic.Not $  p 
  | _ => fm; 
 
fun psimpl fm = case fm of 
   Const ("Not",_) $ p => psimpl1 (HOLogic.Not $ (psimpl p)) 
  | Const("op &",_) $ p $ q => psimpl1 (HOLogic.mk_conj (psimpl p,psimpl q)) 
  | Const("op |",_) $ p $ q => psimpl1 (HOLogic.mk_disj (psimpl p,psimpl q)) 
  | Const("op -->",_) $ p $ q => psimpl1 (HOLogic.mk_imp(psimpl p,psimpl q)) 
  | Const("op =", Type ("fun",[Type ("bool", []),_])) $ p $ q => psimpl1 (HOLogic.mk_eq(psimpl p,psimpl q)) 
  | _ => fm; 
 
 
(*simpl : Simplification of Terms involving quantifiers too. 
 This function is able to drop out some quantified expressions where there are no 
 bound varaibles.*) 
  
fun simpl1 fm  = 
  case fm of 
    Const("All",_) $Abs(x,_,p) => if (has_bound fm ) then fm  
    				else (update_bounds p 0) 
  | Const("Ex",_) $ Abs (x,_,p) => if has_bound fm then fm  
    				else (update_bounds p 0) 
  | _ => psimpl1 fm; 
 
fun simpl fm = case fm of 
    Const ("Not",_) $ p => simpl1 (HOLogic.Not $(simpl p))  
  | Const ("op &",_) $ p $ q => simpl1 (HOLogic.mk_conj (simpl p ,simpl q))  
  | Const ("op |",_) $ p $ q => simpl1 (HOLogic.mk_disj (simpl p ,simpl q ))  
  | Const ("op -->",_) $ p $ q => simpl1 (HOLogic.mk_imp(simpl p ,simpl q ))  
  | Const("op =", Type ("fun",[Type ("bool", []),_]))$ p $ q => simpl1 
  (HOLogic.mk_eq(simpl p ,simpl q ))  
(*  | Const ("All",Ta) $ Abs(Vn,VT,p) => simpl1(Const("All",Ta) $ 
  Abs(Vn,VT,simpl p ))  
  | Const ("Ex",Ta)  $ Abs(Vn,VT,p) => simpl1(Const("Ex",Ta)  $ 
  Abs(Vn,VT,simpl p ))  
*)
  | _ => fm; 
 
(* ------------------------------------------------------------------------- *) 
 
(* Puts fm into NNF*) 
 
fun  nnf fm = if (is_arith_rel fm) then fm  
else (case fm of 
  ( Const ("op &",_) $ p $ q)  => HOLogic.conj $ (nnf p) $(nnf q) 
  | (Const("op |",_) $ p $q) => HOLogic.disj $ (nnf p)$(nnf q) 
  | (Const ("op -->",_)  $ p $ q) => HOLogic.disj $ (nnf (HOLogic.Not $ p)) $ (nnf q) 
  | ((Const ("op =", Type ("fun",[Type ("bool", []),_]))) $ p $ q) =>(HOLogic.disj $ (HOLogic.conj $ (nnf p) $ (nnf q)) $ (HOLogic.conj $ (nnf (HOLogic.Not $ p) ) $ (nnf(HOLogic.Not $ q)))) 
  | (Const ("Not",_)) $ ((Const ("Not",_)) $ p) => (nnf p) 
  | (Const ("Not",_)) $ (( Const ("op &",_)) $ p $ q) =>HOLogic.disj $ (nnf(HOLogic.Not $ p)) $ (nnf(HOLogic.Not $q)) 
  | (Const ("Not",_)) $ (( Const ("op |",_)) $ p $ q) =>HOLogic.conj $ (nnf(HOLogic.Not $ p)) $ (nnf(HOLogic.Not $ q)) 
  | (Const ("Not",_)) $ (( Const ("op -->",_)) $ p $ q ) =>HOLogic.conj $ (nnf p) $(nnf(HOLogic.Not $ q)) 
  | (Const ("Not",_)) $ ((Const ("op =", Type ("fun",[Type ("bool", []),_]))) $ p $ q ) =>(HOLogic.disj $ (HOLogic.conj $(nnf p) $ (nnf(HOLogic.Not $ q))) $ (HOLogic.conj $(nnf(HOLogic.Not $ p)) $ (nnf q))) 
  | _ => fm); 
 
 
(* Function remred to remove redundancy in a list while keeping the order of appearance of the 
elements. but VERY INEFFICIENT!! *) 
 
fun remred1 el [] = [] 
    |remred1 el (h::t) = if el=h then (remred1 el t) else h::(remred1 el t); 
     
fun remred [] = [] 
    |remred (x::l) =  x::(remred1 x (remred l)); 
 
(*Makes sure that all free Variables are of the type integer but this function is only 
used temporarily, this job must be done by the parser later on.*) 
 
fun mk_uni_vars T  (node $ rest) = (case node of 
    Free (name,_) => Free (name,T) $ (mk_uni_vars T rest) 
    |_=> (mk_uni_vars T node) $ (mk_uni_vars T rest )  ) 
    |mk_uni_vars T (Free (v,_)) = Free (v,T) 
    |mk_uni_vars T tm = tm; 
 
fun mk_uni_int T (Const ("0",T2)) = if T = T2 then (mk_numeral 0) else (Const ("0",T2)) 
    |mk_uni_int T (Const ("1",T2)) = if T = T2 then (mk_numeral 1) else (Const ("1",T2)) 
    |mk_uni_int T (node $ rest) = (mk_uni_int T node) $ (mk_uni_int T rest )  
    |mk_uni_int T (Abs(AV,AT,p)) = Abs(AV,AT,mk_uni_int T p) 
    |mk_uni_int T tm = tm; 
 

(* Minusinfinity Version*) 
fun coopermi vars1 fm = 
  case fm of 
   Const ("Ex",_) $ Abs(x0,T,p0) => let 
    val (xn,p1) = variant_abs (x0,T,p0) 
    val x = Free (xn,T)  
    val vars = (xn::vars1) 
    val p = unitycoeff x  (posineq (simpl p1))
    val p_inf = simpl (minusinf x p) 
    val bset = bset x p 
    val js = 1 upto divlcm x p  
    fun p_element j b = linrep vars x (linear_add vars b (mk_numeral j)) p  
    fun stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: map (p_element j) bset)  
   in (list_disj (map stage js))
    end 
  | _ => error "cooper: not an existential formula"; 
 


(* The plusinfinity version of cooper*)
fun cooperpi vars1 fm =
  case fm of
   Const ("Ex",_) $ Abs(x0,T,p0) => let 
    val (xn,p1) = variant_abs (x0,T,p0)
    val x = Free (xn,T)
    val vars = (xn::vars1)
    val p = unitycoeff x  (posineq (simpl p1))
    val p_inf = simpl (plusinf x p)
    val aset = aset x p
    val js = 1 upto divlcm x p
    fun p_element j a = linrep vars x (linear_sub vars a (mk_numeral j)) p
    fun stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: map (p_element j) aset)
   in (list_disj (map stage js))
   end
  | _ => error "cooper: not an existential formula";
  


(*Cooper main procedure*) 
  
fun cooper vars1 fm =
  case fm of
   Const ("Ex",_) $ Abs(x0,T,p0) => let 
    val (xn,p1) = variant_abs (x0,T,p0)
    val x = Free (xn,T)
    val vars = (xn::vars1)
(*     val p = unitycoeff x  (posineq (simpl p1)) *)
    val p = unitycoeff x  p1 
    val ast = aset x p
    val bst = bset x p
    val js = 1 upto divlcm x p
    val (p_inf,f,S ) = 
    if (length bst) < (length ast) 
     then (minusinf x p,linear_add,bst)
     else (plusinf x p, linear_sub,ast)
    fun p_element j a = linrep vars x (f vars a (mk_numeral j)) p
    fun stage j = list_disj (linrep vars x (mk_numeral j) p_inf :: map (p_element j) S)
   in (list_disj (map stage js))
   end
  | _ => error "cooper: not an existential formula";



 
(*Function itlist applys a double parametred function f : 'a->'b->b iteratively to a List l : 'a 
list With End condition b. ict calculates f(e1,f(f(e2,f(e3,...(...f(en,b))..))))) 
 assuming l = [e1,e2,...,en]*) 
 
fun itlist f l b = case l of 
    [] => b 
  | (h::t) => f h (itlist f t b); 
 
(* ------------------------------------------------------------------------- *) 
(* Free variables in terms and formulas.	                             *) 
(* ------------------------------------------------------------------------- *) 
 
fun fvt tml = case tml of 
    [] => [] 
  | Free(x,_)::r => x::(fvt r) 
 
fun fv fm = fvt (term_frees fm); 
 
 
(* ========================================================================= *) 
(* Quantifier elimination.                                                   *) 
(* ========================================================================= *) 
(*conj[/disj]uncts lists iterated conj[disj]unctions*) 
 
fun disjuncts fm = case fm of 
    Const ("op |",_) $ p $ q => (disjuncts p) @ (disjuncts q) 
  | _ => [fm]; 
 
fun conjuncts fm = case fm of 
    Const ("op &",_) $p $ q => (conjuncts p) @ (conjuncts q) 
  | _ => [fm]; 
 
 
 
(* ------------------------------------------------------------------------- *) 
(* Lift procedure given literal modifier, formula normalizer & basic quelim. *) 
(* ------------------------------------------------------------------------- *)
(*
fun lift_qelim afn nfn qfn isat = 
let 
fun qelift vars fm = if (isat fm) then afn vars fm 
else  
case fm of 
  Const ("Not",_) $ p => HOLogic.Not $ (qelift vars p) 
  | Const ("op &",_) $ p $q => HOLogic.conj $ (qelift vars p) $ (qelift vars q) 
  | Const ("op |",_) $ p $ q => HOLogic.disj $ (qelift vars p) $ (qelift vars q) 
  | Const ("op -->",_) $ p $ q => HOLogic.imp $ (qelift vars p) $ (qelift vars q) 
  | Const ("op =",Type ("fun",[Type ("bool", []),_])) $ p $ q => HOLogic.mk_eq ((qelift vars p),(qelift vars q)) 
  | Const ("All",QT) $ Abs(x,T,p) => HOLogic.Not $(qelift vars (Const ("Ex",QT) $ Abs(x,T,(HOLogic.Not $ p)))) 
  | (e as Const ("Ex",_)) $ Abs (x,T,p)  =>  qfn vars (e$Abs (x,T,(nfn(qelift (x::vars) p))))
  | _ => fm 
 
in (fn fm => qelift (fv fm) fm)
end; 
*)
 
   
fun lift_qelim afn nfn qfn isat = 
 let   fun qelim x vars p = 
  let val cjs = conjuncts p 
      val (ycjs,ncjs) = partition (has_bound) cjs in 
      (if ycjs = [] then p else 
                          let val q = (qfn vars ((HOLogic.exists_const HOLogic.intT 
			  ) $ Abs(x,HOLogic.intT,(list_conj ycjs)))) in 
                          (itlist conj_help ncjs q)  
			  end) 
       end 
    
  fun qelift vars fm = if (isat fm) then afn vars fm 
    else  
    case fm of 
      Const ("Not",_) $ p => HOLogic.Not $ (qelift vars p) 
    | Const ("op &",_) $ p $q => HOLogic.conj $ (qelift vars p) $ (qelift vars q) 
    | Const ("op |",_) $ p $ q => HOLogic.disj $ (qelift vars p) $ (qelift vars q) 
    | Const ("op -->",_) $ p $ q => HOLogic.imp $ (qelift vars p) $ (qelift vars q) 
    | Const ("op =",Type ("fun",[Type ("bool", []),_])) $ p $ q => HOLogic.mk_eq ((qelift vars p),(qelift vars q)) 
    | Const ("All",QT) $ Abs(x,T,p) => HOLogic.Not $(qelift vars (Const ("Ex",QT) $ Abs(x,T,(HOLogic.Not $ p)))) 
    | Const ("Ex",_) $ Abs (x,T,p)  => let  val djs = disjuncts(nfn(qelift (x::vars) p)) in 
    			list_disj(map (qelim x vars) djs) end 
    | _ => fm 
 
  in (fn fm => simpl(qelift (fv fm) fm)) 
  end; 

 
(* ------------------------------------------------------------------------- *) 
(* Cleverer (proposisional) NNF with conditional and literal modification.   *) 
(* ------------------------------------------------------------------------- *) 
 
(*Function Negate used by cnnf, negates a formula p*) 
 
fun negate (Const ("Not",_) $ p) = p 
    |negate p = (HOLogic.Not $ p); 
 
fun cnnf lfn = 
  let fun cnnfh fm = case  fm of 
      (Const ("op &",_) $ p $ q) => HOLogic.mk_conj(cnnfh p,cnnfh q) 
    | (Const ("op |",_) $ p $ q) => HOLogic.mk_disj(cnnfh p,cnnfh q) 
    | (Const ("op -->",_) $ p $q) => HOLogic.mk_disj(cnnfh(HOLogic.Not $ p),cnnfh q) 
    | (Const ("op =",Type ("fun",[Type ("bool", []),_])) $ p $ q) => HOLogic.mk_disj( 
    		HOLogic.mk_conj(cnnfh p,cnnfh q), 
		HOLogic.mk_conj(cnnfh(HOLogic.Not $ p),cnnfh(HOLogic.Not $q))) 

    | (Const ("Not",_) $ (Const("Not",_) $ p)) => cnnfh p 
    | (Const ("Not",_) $ (Const ("op &",_) $ p $ q)) => HOLogic.mk_disj(cnnfh(HOLogic.Not $ p),cnnfh(HOLogic.Not $ q)) 
    | (Const ("Not",_) $(Const ("op |",_) $ (Const ("op &",_) $ p $ q) $  
    			(Const ("op &",_) $ p1 $ r))) => if p1 = negate p then 
		         HOLogic.mk_disj(  
			   cnnfh (HOLogic.mk_conj(p,cnnfh(HOLogic.Not $ q))), 
			   cnnfh (HOLogic.mk_conj(p1,cnnfh(HOLogic.Not $ r)))) 
			 else  HOLogic.mk_conj(
			  cnnfh (HOLogic.mk_disj(cnnfh (HOLogic.Not $ p),cnnfh(HOLogic.Not $ q))), 
			   cnnfh (HOLogic.mk_disj(cnnfh (HOLogic.Not $ p1),cnnfh(HOLogic.Not $ r)))
			 ) 
    | (Const ("Not",_) $ (Const ("op |",_) $ p $ q)) => HOLogic.mk_conj(cnnfh(HOLogic.Not $ p),cnnfh(HOLogic.Not $ q)) 
    | (Const ("Not",_) $ (Const ("op -->",_) $ p $q)) => HOLogic.mk_conj(cnnfh p,cnnfh(HOLogic.Not $ q)) 
    | (Const ("Not",_) $ (Const ("op =",Type ("fun",[Type ("bool", []),_]))  $ p $ q)) => HOLogic.mk_disj(HOLogic.mk_conj(cnnfh p,cnnfh(HOLogic.Not $ q)),HOLogic.mk_conj(cnnfh(HOLogic.Not $ p),cnnfh q)) 
    | _ => lfn fm  
in cnnfh
 end; 
 
(*End- function the quantifierelimination an decion procedure of presburger formulas.*)   

(*
val integer_qelim = simpl o evalc o (lift_qelim linform (simpl o (cnnf posineq o evalc)) cooper is_arith_rel) ; 
*)
val integer_qelim = simpl o evalc o (lift_qelim linform (cnnf posineq o evalc) cooper is_arith_rel) ; 

fun mk_presburger_oracle (sg,COOPER_ORACLE t) = 
    if (!quick_and_dirty) 
    then HOLogic.mk_Trueprop (HOLogic.mk_eq(t,integer_qelim t))
    else raise COOPER_ORACLE t;

end;


