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

fun fst (a,b) = a
fun snd (a,b) = b

val filter = List.filter;

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
