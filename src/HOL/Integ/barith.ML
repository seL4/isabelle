(**************************************************************)
(*                                                            *)
(*                                                            *)
(*          Trying to implement an Bounded arithmetic         *)
(*           Chaieb Amine                                     *)
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
  (t1 as (Const("op <=",_) $ l1 $(x as Free(xn,xT))))$
  (t2 as (Const("op <=",_) $ y $ u1)) => 
      if (x = y andalso type_of x = HOLogic.intT) 
        then [(x,(l1,u1))]
        else (interval_of_conj t1) union (interval_of_conj t2)
| Const("op &",_) $(t1 as (Const("op <=",_) $ y $ u1))$
  (t2 as (Const("op <=",_) $ l1 $(x as Free(xn,xT)))) =>
      if (x = y andalso type_of x = HOLogic.intT) 
        then [(x,(l1,u1))]
        else (interval_of_conj t1) union (interval_of_conj t2)
|(Const("op <=",_) $ l $(x as Free(xn,xT))) => [(x,(l,HOLogic.false_const))]
|(Const("op <=",_) $ (x as Free(xn,xT))$ u) => [(x,(HOLogic.false_const,u))]
|Const("op &",_)$t1$t2 => (interval_of_conj t1) union (interval_of_conj t2)
|_ => raise (NORMCONJ "Not in normal form - unknown conjunct");


(* The input to this function should be a list *)
(*of meta-implications of the following form:*)
(* l1 <= x1 & x1 <= u1 ==> ... ==> ln <= xn & xn <= un*)
(* the output will be a list of Var*interval*)

val iT = HOLogic.intT;
fun  maxterm (Const("False",_)) t = t
    |maxterm t (Const("False",_)) = t 
    |maxterm t1 t2 = Const("HOL.max",iT --> iT --> iT)$t1$t2;

fun  minterm (Const("False",_)) t = t
    |minterm t (Const("False",_)) = t
    |minterm t1 t2 = Const("HOL.min",iT --> iT --> iT)$t1$t2;

fun intervals_of_premise p =  
  let val ps = map HOLogic.dest_Trueprop (Logic.strip_imp_prems p)
      fun tight [] = []
         |tight ((x,(Const("False",_),Const("False",_)))::ls) = tight ls
         |tight ((x,(l as Const("False",_),u))::ls) = 
	   let val ls' = tight ls in
	   case assoc (ls',x) of
	   None => (x,(l,u))::ls'
	   |Some (l',u') => 
	   let 
            val ln = l'
            val un = 
	     if (CooperDec.is_numeral u) andalso (CooperDec.is_numeral u') 
	     then CooperDec.mk_numeral 
		 (Int.min (CooperDec.dest_numeral u,CooperDec.dest_numeral u'))
	     else (minterm u u')
	   in (x,(ln,un))::(filter (fn p => not (fst p = x)) ls')
	   end
          end
         |tight ((x,(l,u as Const("False",_)))::ls) = 
	   let val ls' = tight ls in
	   case assoc (ls',x) of
	   None => (x,(l,u))::ls'
	   |Some (l',u') => 
	   let 
            val ln = 
	      if (CooperDec.is_numeral l) andalso (CooperDec.is_numeral l') 
	      then CooperDec.mk_numeral 
		(Int.max (CooperDec.dest_numeral l,CooperDec.dest_numeral l')) 
	      else (maxterm l l')
            val un = u'
	   in (x,(ln,un))::(filter (fn p => not (fst p = x)) ls')
	   end
          end
         |tight ((x,(l,u))::ls) = 
	   let val ls' = tight ls in
	     case assoc (ls',x) of
	      None => (x,(l,u))::ls'
	     |Some (l',u') => let val ln = if (CooperDec.is_numeral l) andalso (CooperDec.is_numeral l') then CooperDec.mk_numeral (Int.max (CooperDec.dest_numeral l,CooperDec.dest_numeral l')) else (maxterm l l')
		 val un = if (CooperDec.is_numeral u) andalso (CooperDec.is_numeral u') then CooperDec.mk_numeral (Int.min (CooperDec.dest_numeral u,CooperDec.dest_numeral u')) else (minterm u u')
		   in (x,(ln,un))::(filter (fn p => not (fst p = x)) ls')
		   end
           end 
  in tight (foldr (fn (p,l) => (interval_of_conj p) union l) (ps,[]))
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
    val cg = cterm_of sg g
    val mybinarith =
      map thm ["Pls_0_eq", "Min_1_eq",
               "bin_pred_Pls", "bin_pred_Min", "bin_pred_1",
	       "bin_pred_0",            "bin_succ_Pls", "bin_succ_Min",
	       "bin_succ_1", "bin_succ_0",
               "bin_add_Pls", "bin_add_Min", "bin_add_BIT_0",
	       "bin_add_BIT_10",
               "bin_add_BIT_11", "bin_minus_Pls", "bin_minus_Min",
	       "bin_minus_1",
               "bin_minus_0", "bin_mult_Pls", "bin_mult_Min",
	       "bin_mult_1", "bin_mult_0",
               "bin_add_Pls_right", "bin_add_Min_right",
	       "abs_zero", "abs_one",
               "eq_number_of_eq",
               "iszero_number_of_Pls", "nonzero_number_of_Min",
	       "iszero_number_of_0", "iszero_number_of_1",
               "less_number_of_eq_neg",
               "not_neg_number_of_Pls", "neg_number_of_Min",
	       "neg_number_of_BIT",
               "le_number_of_eq"]

     val myringarith =
       [number_of_add RS sym, number_of_minus RS sym,
	diff_number_of_eq, number_of_mult RS sym,
	thm "zero_eq_Numeral0_nring", thm "one_eq_Numeral1_nring"]

     val mynatarith =
       [thm "zero_eq_Numeral0_nat", thm "one_eq_Numeral1_nat",
	thm "add_nat_number_of", thm "diff_nat_number_of",
	thm "mult_nat_number_of", thm "eq_nat_number_of", thm
	  "less_nat_number_of"]
	 
     val mypowerarith =
       [thm "nat_number_of", thm "zpower_number_of_even", thm
	  "zpower_number_of_odd", thm "zpower_Pls", thm "zpower_Min"]

     val myiflet = [if_False, if_True, thm "Let_def"]
     val myifletcongs = [if_weak_cong, let_weak_cong]

     val mysimpset = HOL_basic_ss 
	 addsimps mybinarith 
	 addsimps myringarith
         addsimps mynatarith addsimps mypowerarith
         addsimps myiflet addsimps simp_thms
         addcongs myifletcongs

    val simpset0 = HOL_basic_ss 
	addsimps [thm "z_less_imp_le1", thm "z_eq_imp_le_conj"] 
    val pre_thm = Seq.hd (EVERY (map TRY 
	 [simp_tac simpset0 1, simp_tac mysimpset 1]) 
			    (trivial cg))
    val tac = case (prop_of pre_thm) of
        Const ("==>", _) $ t1 $ _ =>
      let  
         val (ths,n) = simp_exp sg t1
         val cn = length ths - 1
         fun conjIs thn j = EVERY (map (rtac conjI) (j upto (thn + j - 1)))
         fun thtac thms j = EVERY (map 
	(fn t => rtac t j THEN assm_tac n j  
	THEN (TRY (REPEAT_DETERM_N 2 (simp_tac ss j)))) thms)
      in ((conjIs cn i) THEN (thtac ths i))
      end
     |_ => assume_tac i
     in (tac st)
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

Goal "-1 <= (x::int) ==>  x <= 1 & 1 <= (z::int) ==> z <= 2+3 ==> 0 <= (y::int) & y <= 5 + 7 ==> -4 <= x - x  + x*x";
by(Barith.barith_tac 1);

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
