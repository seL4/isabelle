(*  Title: HOL/Real/Float.ML
    ID:    $Id$
    Author: Steven Obua
*)

structure ExactFloatingPoint :
sig
    exception Destruct_floatstr of string
    val destruct_floatstr : (char -> bool) -> (char -> bool) -> string -> bool * string * string * bool * string
									  
    exception Floating_point of string
				
    type floatrep = IntInf.int * IntInf.int
    val approx_dec_by_bin : IntInf.int -> floatrep -> floatrep * floatrep
    val approx_decstr_by_bin : int -> string -> floatrep * floatrep
end 
=
struct

exception Destruct_floatstr of string;

fun destruct_floatstr isDigit isExp number = 
    let
	val numlist = filter (not o Char.isSpace) (String.explode number)
	
	fun countsigns ((#"+")::cs) = countsigns cs
	  | countsigns ((#"-")::cs) = 
	    let	
		val (positive, rest) = countsigns cs 
	    in
		(not positive, rest)
	    end
	  | countsigns cs = (true, cs)

	fun readdigits [] = ([], [])
	  | readdigits (q as c::cs) = 
	    if (isDigit c) then 
		let
		    val (digits, rest) = readdigits cs
		in
		    (c::digits, rest)
		end
	    else
		([], q)		

	fun readfromexp_helper cs =
	    let
		val (positive, rest) = countsigns cs
		val (digits, rest') = readdigits rest
	    in
		case rest' of
		    [] => (positive, digits)
		  | _ => raise (Destruct_floatstr number)
	    end	    

	fun readfromexp [] = (true, [])
	  | readfromexp (c::cs) = 
	    if isExp c then
		readfromexp_helper cs
	    else 
		raise (Destruct_floatstr number)		

	fun readfromdot [] = ([], readfromexp [])
	  | readfromdot ((#".")::cs) = 
	    let		
		val (digits, rest) = readdigits cs
		val exp = readfromexp rest
	    in
		(digits, exp)
	    end		
	  | readfromdot cs = readfromdot ((#".")::cs)
			    
	val (positive, numlist) = countsigns numlist				 
	val (digits1, numlist) = readdigits numlist				 
 	val (digits2, exp) = readfromdot numlist
    in
	(positive, String.implode digits1, String.implode digits2, fst exp, String.implode (snd exp))
    end

type floatrep = IntInf.int * IntInf.int

exception Floating_point of string;

val ln2_10 = (Math.ln 10.0)/(Math.ln 2.0)
	
fun intmul a b = IntInf.* (a,b)
fun intsub a b = IntInf.- (a,b)	
fun intadd a b = IntInf.+ (a,b) 		 
fun intpow a b = IntInf.pow (a, IntInf.toInt b);
fun intle a b = IntInf.<= (a, b);
fun intless a b = IntInf.< (a, b);
fun intneg a = IntInf.~ a;
val zero = IntInf.fromInt 0;
val one = IntInf.fromInt 1;
val two = IntInf.fromInt 2;
val ten = IntInf.fromInt 10;
val five = IntInf.fromInt 5;

fun find_most_significant q r = 
    let 
	fun int2real i = 
	    case Real.fromString (IntInf.toString i) of 
		SOME r => r 
	      | NONE => raise (Floating_point "int2real")	
	fun subtract (q, r) (q', r') = 
	    if intle r r' then
		(intsub q (intmul q' (intpow ten (intsub r' r))), r)
	    else
		(intsub (intmul q (intpow ten (intsub r r'))) q', r')
	fun bin2dec d =
	    if intle zero d then 
		(intpow two d, zero)
	    else
		(intpow five (intneg d), d)				
		
	val L = IntInf.fromInt (Real.floor (int2real (IntInf.fromInt (IntInf.log2 q)) + (int2real r) * ln2_10))	
	val L1 = intadd L one

	val (q1, r1) = subtract (q, r) (bin2dec L1) 		
    in
	if intle zero q1 then 
	    let
		val (q2, r2) = subtract (q, r) (bin2dec (intadd L1 one))
	    in
		if intle zero q2 then 
		    raise (Floating_point "find_most_significant")
		else
		    (L1, (q1, r1))
	    end
	else
	    let
		val (q0, r0) = subtract (q, r) (bin2dec L)
	    in
		if intle zero q0 then
		    (L, (q0, r0))
		else
		    raise (Floating_point "find_most_significant")
	    end		    
    end

fun approx_dec_by_bin n (q,r) =
    let	
	fun addseq acc d' [] = acc
	  | addseq acc d' (d::ds) = addseq (intadd acc (intpow two (intsub d d'))) d' ds

	fun seq2bin [] = (zero, zero)
	  | seq2bin (d::ds) = (intadd (addseq zero d ds) one, d)

	fun approx d_seq d0 precision (q,r) = 
	    if q = zero then 
		let val x = seq2bin d_seq in
		    (x, x)
		end
	    else    
		let 
		    val (d, (q', r')) = find_most_significant q r
		in	
		    if intless precision (intsub d0 d) then 
			let 
			    val d' = intsub d0 precision
			    val x1 = seq2bin (d_seq)
			    val x2 = (intadd (intmul (fst x1) (intpow two (intsub (snd x1) d'))) one,  d') (* = seq2bin (d'::d_seq) *) 
			in
			    (x1, x2)
			end
		    else
			approx (d::d_seq) d0 precision (q', r') 						    		
		end		
	
	fun approx_start precision (q, r) =
	    if q = zero then 
		((zero, zero), (zero, zero))
	    else
		let 
		    val (d, (q', r')) = find_most_significant q r
		in	
		    if intle precision zero then 
			let
			    val x1 = seq2bin [d]
			in
			    if q' = zero then 
				(x1, x1)
			    else
				(x1, seq2bin [intadd d one])
			end
		    else
			approx [d] d precision (q', r')
		end		
    in
	if intle zero q then 
	    approx_start n (q,r)
	else
	    let 
		val ((a1,b1), (a2, b2)) = approx_start n (intneg q, r) 
	    in
		((intneg a2, b2), (intneg a1, b1))
	    end					
    end

fun approx_decstr_by_bin n decstr =
    let 
	fun str2int s = case IntInf.fromString s of SOME x => x | NONE => zero 
	fun signint p x = if p then x else intneg x

	val (p, d1, d2, ep, e) = destruct_floatstr Char.isDigit (fn e => e = #"e" orelse e = #"E") decstr
	val s = IntInf.fromInt (size d2)
		
	val q = signint p (intadd (intmul (str2int d1) (intpow ten s)) (str2int d2))
	val r = intsub (signint ep (str2int e)) s
    in
	approx_dec_by_bin (IntInf.fromInt n) (q,r)
    end

end;

structure FloatArith = 
struct

type float = IntInf.int * IntInf.int 

val izero = IntInf.fromInt 0
val ione = IntInf.fromInt 1
val imone = IntInf.fromInt ~1
val itwo = IntInf.fromInt 2
fun imul a b = IntInf.* (a,b)
fun isub a b = IntInf.- (a,b)
fun iadd a b = IntInf.+ (a,b)

val floatzero = (izero, izero)

fun positive_part (a,b) = 
    (if IntInf.< (a,izero) then izero else a, b)

fun negative_part (a,b) = 
    (if IntInf.< (a,izero) then a else izero, b)

fun is_negative (a,b) = 
    if IntInf.< (a, izero) then true else false

fun is_positive (a,b) = 
    if IntInf.< (izero, a) then true else false

fun is_zero (a,b) = 
    if a = izero then true else false

fun ipow2 a = IntInf.pow ((IntInf.fromInt 2), IntInf.toInt a)

fun add (a1, b1) (a2, b2) = 
    if IntInf.< (b1, b2) then
	(iadd a1 (imul a2 (ipow2 (isub b2 b1))), b1)
    else
	(iadd (imul a1 (ipow2 (isub b1 b2))) a2, b2)

fun sub (a1, b1) (a2, b2) = 
    if IntInf.< (b1, b2) then
	(isub a1 (imul a2 (ipow2 (isub b2 b1))), b1)
    else
	(isub (imul a1 (ipow2 (isub b1 b2))) a2, b2)

fun neg (a, b) = (IntInf.~ a, b)

fun is_equal a b = is_zero (sub a b)

fun is_less a b = is_negative (sub a b)

fun max a b = if is_less a b then b else a

fun min a b = if is_less a b then a else b

fun abs a = if is_negative a then neg a else a

fun mul (a1, b1) (a2, b2) = (imul a1 a2, iadd b1 b2)

end;


structure Float:
sig
    type float = FloatArith.float
    type floatfunc = float * float -> float * float

    val mk_intinf : typ -> IntInf.int -> term
    val mk_float : float -> term

    exception Dest_intinf;
    val dest_intinf : term -> IntInf.int
    val dest_nat : term -> IntInf.int
    
    exception Dest_float;
    val dest_float : term -> float

    val float_const : term

    val float_add_const : term
    val float_diff_const : term
    val float_uminus_const : term
    val float_pprt_const : term
    val float_nprt_const : term
    val float_abs_const : term
    val float_mult_const : term 
    val float_le_const : term

    val nat_le_const : term
    val nat_less_const : term
    val nat_eq_const : term

    val approx_float : int -> floatfunc -> string -> term * term

    val sign_term : term -> cterm

(*    exception Float_op_oracle_data of term
    exception Nat_op_oracle_data of term

    val float_op_oracle : Sign.sg * exn -> term
    val nat_op_oracle : Sign.sg * exn -> term

    val invoke_float_op : term -> thm
    val invoke_nat_op : term -> thm*)
end 
= 
struct

structure Inttab = TableFun(type key = int val ord = (rev_order o int_ord));

type float = IntInf.int*IntInf.int
type floatfunc = float*float -> float*float

val th = theory "Float"
val sg = sign_of th
		
val float_const = Const ("Float.float", HOLogic.mk_prodT (HOLogic.intT, HOLogic.intT) --> HOLogic.realT)

val float_add_const = Const ("HOL.plus", HOLogic.realT --> HOLogic.realT --> HOLogic.realT)
val float_diff_const = Const ("HOL.minus", HOLogic.realT --> HOLogic.realT --> HOLogic.realT)
val float_mult_const = Const ("HOL.times", HOLogic.realT --> HOLogic.realT --> HOLogic.realT)
val float_uminus_const = Const ("HOL.uminus", HOLogic.realT --> HOLogic.realT)
val float_abs_const = Const ("HOL.abs", HOLogic.realT --> HOLogic.realT)
val float_le_const = Const ("op <=", HOLogic.realT --> HOLogic.realT --> HOLogic.boolT)
val float_pprt_const = Const ("OrderedGroup.pprt", HOLogic.realT --> HOLogic.realT)
val float_nprt_const = Const ("OrderedGroup.nprt", HOLogic.realT --> HOLogic.realT)

val nat_le_const = Const ("op <=", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)
val nat_less_const = Const ("op <", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)
val nat_eq_const = Const ("op =", HOLogic.natT --> HOLogic.natT --> HOLogic.boolT)
 		  
val zero = FloatArith.izero
val minus_one = FloatArith.imone
val two = FloatArith.itwo
	  
exception Dest_intinf;
exception Dest_float;

fun mk_intinf ty n =
    let
	fun mk_bit n = if n = zero then HOLogic.B0_const else HOLogic.B1_const
								 
	fun bin_of n = 
	    if n = zero then HOLogic.pls_const
	    else if n = minus_one then HOLogic.min_const
	    else 
		let 
		    (*val (q,r) = IntInf.divMod (n, two): doesn't work in SML 10.0.7, but in newer versions!!!*)
	            val q = IntInf.div (n, two)
		    val r = IntInf.mod (n, two)
		in
		    HOLogic.bit_const $ bin_of q $ mk_bit r
		end
    in 
	HOLogic.number_of_const ty $ (bin_of n)
    end

fun dest_intinf n = 
    let
	fun dest_bit n = 
	    case n of 
		Const ("Numeral.bit.B0", _) => FloatArith.izero
	      | Const ("Numeral.bit.B1", _) => FloatArith.ione
	      | _ => raise Dest_intinf
			 
	fun int_of n = 
	    case n of
		Const ("Numeral.Pls", _) => FloatArith.izero
	      | Const ("Numeral.Min", _) => FloatArith.imone
	      | Const ("Numeral.Bit", _) $ q $ r => FloatArith.iadd (FloatArith.imul (int_of q) FloatArith.itwo) (dest_bit r)
	      | _ => raise Dest_intinf
    in
	case n of 
	    Const ("Numeral.number_of", _) $ n' => int_of n'
	  | Const ("Numeral0", _) => FloatArith.izero
	  | Const ("Numeral1", _) => FloatArith.ione    
	  | _ => raise Dest_intinf
    end

fun mk_float (a,b) = 
    float_const $ (HOLogic.mk_prod ((mk_intinf HOLogic.intT a), (mk_intinf HOLogic.intT b)))

fun dest_float f = 
    case f of 
	(Const ("Float.float", _) $ (Const ("Pair", _) $ a $ b)) => (dest_intinf a, dest_intinf b)
      | Const ("Numeral.number_of",_) $ a => (dest_intinf f, 0)
      | Const ("Numeral0", _) => (FloatArith.izero, FloatArith.izero)
      | Const ("Numeral1", _) => (FloatArith.ione, FloatArith.izero)
      | _ => raise Dest_float

fun dest_nat n = 
    let 
	val v = dest_intinf n
    in
	if IntInf.< (v, FloatArith.izero) then
	    FloatArith.izero
	else
	    v
    end

fun approx_float prec f value = 
    let
	val interval = ExactFloatingPoint.approx_decstr_by_bin prec value
	val (flower, fupper) = f interval
    in
	(mk_float flower, mk_float fupper)
    end

fun sign_term t = cterm_of sg t

(*exception Float_op_oracle_data of term;

fun float_op_oracle (sg, exn as Float_op_oracle_data t) =
    Logic.mk_equals (t,
		     case t of 
			 f $ a $ b => 
			 let 
			     val a' = dest_float a 
			     val b' = dest_float b
			 in
			     if f = float_add_const then
				 mk_float (FloatArith.add a' b')	
			     else if f = float_diff_const then
				 mk_float (FloatArith.sub a' b')
			     else if f = float_mult_const then
				 mk_float (FloatArith.mul a' b')		
			     else if f = float_le_const then
				 (if FloatArith.is_less b' a' then
				     HOLogic.false_const
				 else
				     HOLogic.true_const)
			     else raise exn	    		    	       
			 end
		       | f $ a => 
			 let
			     val a' = dest_float a
			 in
			     if f = float_uminus_const then
				 mk_float (FloatArith.neg a')
			     else if f = float_abs_const then
				 mk_float (FloatArith.abs a')
			     else if f = float_pprt_const then
				 mk_float (FloatArith.positive_part a')
			     else if f = float_nprt_const then
				 mk_float (FloatArith.negative_part a')
			     else
				 raise exn
			 end
		       | _ => raise exn
		    )
val th = ref ([]: Theory.theory list)
val sg = ref ([]: Sign.sg list)

fun invoke_float_op c = 
    let
	val th = (if length(!th) = 0 then th := [theory "MatrixLP"] else (); hd (!th))
	val sg = (if length(!sg) = 0 then sg := [sign_of th] else (); hd (!sg))
    in
	invoke_oracle th "float_op" (sg, Float_op_oracle_data c)
    end

exception Nat_op_oracle_data of term;

fun nat_op_oracle (sg, exn as Nat_op_oracle_data t) =
    Logic.mk_equals (t,
		     case t of 
			 f $ a $ b => 
			 let 
			     val a' = dest_nat a 
			     val b' = dest_nat b
			 in
			     if f = nat_le_const then
				 (if IntInf.<= (a', b') then
				     HOLogic.true_const
				 else
				     HOLogic.false_const)
			     else if f = nat_eq_const then
				 (if a' = b' then 
				      HOLogic.true_const
				  else
				      HOLogic.false_const)
			     else if f = nat_less_const then
				 (if IntInf.< (a', b') then
				      HOLogic.true_const
				  else
				      HOLogic.false_const)
			     else 
				 raise exn	    	
			 end
		       | _ => raise exn)

fun invoke_nat_op c = 
    let
	val th = (if length (!th) = 0 then th := [theory "MatrixLP"] else (); hd (!th))
	val sg = (if length (!sg) = 0 then sg := [sign_of th] else (); hd (!sg))
    in
	invoke_oracle th "nat_op" (sg, Nat_op_oracle_data c)
    end
*)
end;