(**************************************************************)
(*                                                            *)
(*                                                            *)
(*          Trying to implement an Bounded arithmetic         *)
(*                                                            *)
(*                                                            *)
(**************************************************************)
  
signature BARITH = 
sig
  val barith_tac : int -> tactic
  val setup      : (theory -> theory) list
  
end;


structure Barith =
struct

(* Theorems we use from Barith.thy*)
val abs_const = thm "abs_const";
val abs_var = thm "abs_var";
val abs_neg = thm "abs_neg";
val abs_add = thm "abs_add";
val abs_sub = thm "abs_sub";
val abs_sub_x = thm "abs_sub_x";
val abs_mul = thm "abs_mul";
val abs_mul_x = thm "abs_mul_x";
val subinterval = thm "subinterval";
val imp_commute = thm "imp_commute";
val imp_simplify = thm "imp_simplify";

exception NORMCONJ of string;

fun interval_of_conj t = case t of
 Const("op &",_) $
  (Const("op <=",_) $ l1 $(x as Free(xn,xT)))$
  (Const("op <=",_) $ y $ u1) => 
      if (x = y andalso type_of x = HOLogic.intT) 
        then (x,(l1,u1)) 
        else raise 
	  (NORMCONJ "Not in normal form -- not the same variable")
| Const("op &",_) $(Const("op <=",_) $ y $ u1)$
  (Const("op <=",_) $ l1 $(x as Free(xn,xT))) =>
      if (x = y andalso type_of x = HOLogic.intT) 
        then (x,(l1,u1)) 
        else raise 
	  (NORMCONJ "Not in normal form -- not the same variable")
|(Const("op <=",_) $ l $(x as Free(xn,xT))) => (x,(l,x))
|(Const("op <=",_) $ (x as Free(xn,xT))$ u) => (x,(x,u))
|_ => raise (NORMCONJ "Not in normal form - unknown conjunct");


(* The input to this function should be a list *)
(*of meta-implications of the following form:*)
(* l1 <= x1 & x1 <= u1 ==> ... ==> ln <= xn & xn <= un*)
(* the output will be a list of Var*interval*)

val iT = HOLogic.intT;
fun maxterm t1 t2 = Const("HOL.max",iT --> iT --> iT)$t1$t2;
fun minterm t1 t2 = Const("HOL.min",iT --> iT --> iT)$t1$t2;

fun intervals_of_premise p =  
  let val ps = map HOLogic.dest_Trueprop (Logic.strip_imp_prems p)
      fun tight [] = []
         |tight ((x,(l,u))::ls) = 
	   let val ls' = tight ls in
	     case assoc (ls',x) of
	      None => (x,(l,u))::ls'
	     |Some (l',u') => let val ln = if (CooperDec.is_numeral l) andalso (CooperDec.is_numeral l') then CooperDec.mk_numeral (Int.min (CooperDec.dest_numeral l,CooperDec.dest_numeral l')) else (maxterm l l')
		 val un = if (CooperDec.is_numeral u) andalso (CooperDec.is_numeral u') then CooperDec.mk_numeral (Int.min (CooperDec.dest_numeral u,CooperDec.dest_numeral u')) else (minterm u u')
		   in (x,(ln,un))::(filter (fn p => fst p = x) ls')
		   end
           end 
  in tight (map interval_of_conj ps)
end ;

fun exp_of_concl p = case p of
  Const("op &",_) $
  (Const("op <=",_) $ l $ e)$
  (Const("op <=",_) $ e' $ u) => 
     if e = e' then [(e,(Some l,Some u))]
     else raise NORMCONJ "Conclusion not in normal form-- different exp in conj"
|Const("op &",_) $
  (Const("op <=",_) $ e' $ u)$
  (Const("op <=",_) $ l $ e) => 
     if e = e' then [(e,(Some l,Some u))] 
     else raise NORMCONJ "Conclusion not in normal form-- different exp in conj"
|(Const("op <=",_) $ e $ u) =>
  if (CooperDec.is_numeral u) then [(e,(None,Some u))]
  else 
    if (CooperDec.is_numeral e) then [(u,(Some e,None))] 
    else raise NORMCONJ "Bounds has to be numerals" 
|(Const("op &",_)$a$b) => (exp_of_concl a) @ (exp_of_concl b)
|_ => raise NORMCONJ "Conclusion not in normal form---unknown connective";


fun strip_problem p = 
let 
  val is = intervals_of_premise p
  val e = exp_of_concl ((HOLogic.dest_Trueprop o Logic.strip_imp_concl) p)
in (is,e)
end;




(*Abstract interpretation of Intervals over theorems *)
exception ABSEXP of string;

fun decomp_absexp sg is e = case e of
 Free(xn,_) => ([], fn [] => case assoc (is,e) of 
   Some (l,u) => instantiate' [] 
     (map (fn a => Some (cterm_of sg a)) [l,e,u]) abs_var
  |_ => raise ABSEXP ("No Interval for Variable   " ^ xn) )
|Const("op +",_) $ e1 $ e2 => 
  ([e1,e2], fn [th1,th2] => [th1,th2] MRS abs_add)
|Const("op -",_) $ e1 $ e2 => 
  if e1 = e2 then 
    ([e1],fn [th] => th RS abs_sub_x)
  else
    ([e1,e2], fn [th1,th2] => [th1,th2] MRS abs_sub)
|Const("op *",_) $ e1 $ e2 => 
  if e1 = e2 then 
    ([e1],fn [th] => th RS abs_mul_x)
  else
  ([e1,e2], fn [th1,th2] => [th1,th2] MRS abs_mul)
|Const("op uminus",_) $ e' => 
  ([e'], fn [th] => th RS abs_neg)
|_ => if CooperDec.is_numeral e then
    ([], fn [] => instantiate' [] [Some (cterm_of sg e)] abs_const) 
        else raise ABSEXP "Unknown arithmetical expression";

fun absexp sg is (e,(lo,uo)) = case (lo,uo) of
  (Some l, Some u) =>
  let 
    val th1 = CooperProof.thm_of sg (decomp_absexp sg is) e
    val th2 = instantiate' [] [None,None,None,Some (cterm_of sg l),Some (cterm_of sg u)] subinterval
    val ss = (simpset_of (theory "Presburger")) addsimps [max_def,min_def]
    val my_ss = HOL_basic_ss addsimps [imp_commute, imp_simplify]
    val th' = th1
    val th = th' RS th2
  in th
  end 
|(None, Some u) => 
  let 
    val th1 = CooperProof.thm_of sg (decomp_absexp sg is) e
    val Const("op &",_)$
      (Const("op <=",_)$l$_)$_= (HOLogic.dest_Trueprop o concl_of) th1
    val th2 = instantiate' [] [None,None,None,Some (cterm_of sg l),Some (cterm_of sg u)] subinterval
    val ss = (simpset_of (theory "Presburger")) addsimps [max_def,min_def]
    val my_ss = HOL_basic_ss addsimps [imp_commute, imp_simplify]
    val th' = th1
    val th = th' RS th2
  in th RS conjunct2
  end 

|(Some l, None) => let 
    val th1 = CooperProof.thm_of sg (decomp_absexp sg is) e
    val Const("op &",_)$_$
      (Const("op <=",_)$_$u)= (HOLogic.dest_Trueprop o concl_of) th1
    val th2 = instantiate' [] [None,None,None,Some (cterm_of sg l),Some (cterm_of sg u)] subinterval
    val ss = (simpset_of (theory "Presburger")) addsimps [max_def,min_def]
    val my_ss = HOL_basic_ss addsimps [imp_commute, imp_simplify]
    val th' = th1
    val th = th' RS th2
  in th RS conjunct1
  end 

|(None,None) => raise ABSEXP "No bounds for conclusion";

fun free_occ e = case e of
 Free(_,i) => if i = HOLogic.intT then 1 else 0
|f$a => (free_occ f) + (free_occ a)
|Abs(_,_,p) => free_occ p
|_ => 0;


(*
fun simp_exp sg p = 
  let val (is,(e,(l,u))) = strip_problem p
      val th = absexp sg is (e,(l,u))
      val _ = prth th
  in (th, free_occ e)
end;
*)

fun simp_exp sg p = 
  let val (is,es) = strip_problem p
      val ths = map (absexp sg is) es
      val n = foldr (fn ((e,(_,_)),x) => (free_occ e) + x) (es,0)
  in (ths, n)
end;



(* ============================ *)
(*      The barith Tactic       *)
(* ============================ *)

(*
fun barith_tac i = ObjectLogic.atomize_tac i THEN (fn st =>
  let
    fun assm_tac n j = REPEAT_DETERM_N n ((assume_tac j) ORELSE (simple_arith_tac j))
    val g = BasisLibrary.List.nth (prems_of st, i - 1)
    val sg = sign_of_thm st
    val ss = (simpset_of (the_context())) addsimps [max_def,min_def]
    val (th,n) = simp_exp sg g
  in (rtac th i 
	THEN assm_tac n i  
	THEN (TRY (REPEAT_DETERM_N 2 (simp_tac ss i)))) st
end);

*)


fun barith_tac i = ObjectLogic.atomize_tac i THEN (fn st =>
  let
    fun assm_tac n j = REPEAT_DETERM_N n ((assume_tac j) ORELSE (simple_arith_tac j))
    val g = BasisLibrary.List.nth (prems_of st, i - 1)
    val sg = sign_of_thm st
    val ss = (simpset_of (theory "Barith")) addsimps [max_def,min_def]
    val (ths,n) = simp_exp sg g
    val cn = length ths - 1
    fun conjIs thn j = EVERY (map (rtac conjI) (j upto (thn + j - 1)))
    fun thtac thms j = EVERY (map 
	(fn t => rtac t j THEN assm_tac n j  
	THEN (TRY (REPEAT_DETERM_N 2 (simp_tac ss j)))) thms)
  in ((conjIs cn i) THEN (thtac ths i)) st
end);

fun barith_args meth =
 let val parse_flag = 
         Args.$$$ "no_quantify" >> K (apfst (K false))
      || Args.$$$ "abs" >> K (apsnd (K true));
 in
   Method.simple_args 
  (Scan.optional (Args.$$$ "(" |-- Scan.repeat1 parse_flag --| Args.$$$ ")") []
 >>
    curry (foldl op |>) (true, false))
    (fn (q,a) => fn _ => meth 1)
  end;

fun barith_method i = Method.METHOD (fn facts =>
  Method.insert_tac facts 1 THEN barith_tac i)

val setup =
  [Method.add_method ("barith",
     Method.no_args (barith_method 1),
     "VERY simple decision procedure for bounded arithmetic")];


(* End of Structure *)
end;

(* Test *)
(*
open Barith;

Goal "-1 <= (x::int) & x <= 1 ==> 0 <= (y::int) & y <= 5 + 7 ==> -13 <= x*x + y*x & x*x + y*x <= 20";
by(barith_tac 1);

Goal "-1 <= (x::int) & x <= 1 ==> 0 <= (y::int) & y <= 5 + 7 ==> 0 <= x - x  + y & x - x  + y<= 12";
by(barith_tac 1);

Goal "-1 <= (x::int) & x <= 1 ==> 0 <= (y::int) & y <= 5 + 7 ==> 0 <= x - x  + x*x & x - x  + x*x<= 1";
by(barith_tac 1);

Goal "(x::int) <= 1& 1 <= x ==> 0 <= (y::int) & y <= 5 + 7 ==> 0 <= x - x  + x*x & x - x  + x*x<= 1";
by(barith_tac 1);

Goal "(x::int) <= 1& 1 <= x ==> (t::int) <= 8 ==>(x::int) <= 2& 0 <= x ==> 0 <= (y::int) & y <= 5 + 7 ==> 0 <= x - x  + x*x & x - x  + x*x<= 1";
by(barith_tac 1);

Goal "-1 <= (x::int) & x <= 1 ==> 0 <= (y::int) & y <= 5 + 7 ==> -4 <= x - x  + x*x";
by(barith_tac 1);

Goal "[|(0::int) <= x & x <= 5 ; 0 <= (y::int) & y <= 7|]==> (0 <= x*x*x & x*x*x <= 125 ) & (0 <= x*x & x*x <= 100) & (0 <= x*x + x & x*x + x <= 30) & (0<= x*y & x*y <= 35)";
by (barith_tac 1);
*)


(*
val st = topthm();
val sg = sign_of_thm st; 
val g = BasisLibrary.List.nth (prems_of st, 0);
val (ths,n) = simp_exp sg g;
fun assm_tac n j = REPEAT_DETERM_N n ((assume_tac j) ORELSE (simple_arith_tac j));

*)
