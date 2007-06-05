(*  Title: HOL/Real/Float.ML
    ID:    $Id$
    Author: Steven Obua
*)

signature FLOAT_ARITH =
sig
  exception Destruct_floatstr of string
  val destruct_floatstr: (char -> bool) -> (char -> bool) -> string -> bool * string * string * bool * string

  exception Floating_point of string
  val approx_dec_by_bin: integer -> Float.float -> Float.float * Float.float
  val approx_decstr_by_bin: int -> string -> Float.float * Float.float

  val mk_float: Float.float -> term
  val dest_float: term -> Float.float

  val approx_float: int -> (Float.float * Float.float -> Float.float * Float.float)
    -> string -> term * term
end;

structure FloatArith : FLOAT_ARITH =
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

exception Floating_point of string;

val ln2_10 = Math.ln 10.0 / Math.ln 2.0;
val exp5 = Integer.pow (Integer.int 5);
val exp10 = Integer.pow (Integer.int 10);

fun intle a b = not (Integer.cmp (a, b) = GREATER);
fun intless a b = Integer.cmp (a, b) = LESS;

fun find_most_significant q r =
  let
    fun int2real i =
      case (Real.fromString o Integer.string_of_int) i of
        SOME r => r
        | NONE => raise (Floating_point "int2real")
    fun subtract (q, r) (q', r') =
      if intle r r' then
        (Integer.sub q (Integer.mult q' (exp10 (Integer.sub r' r))), r)
      else
        (Integer.sub (Integer.mult q (exp10 (Integer.sub r r'))) q', r')
    fun bin2dec d =
      if intle Integer.zero d then
        (Integer.exp d, Integer.zero)
      else
        (exp5 (Integer.neg d), d)

    val L = Integer.int (Real.floor (int2real (Integer.log q) + int2real r * ln2_10))
    val L1 = Integer.inc L

    val (q1, r1) = subtract (q, r) (bin2dec L1) 
  in
    if intle Integer.zero q1 then
      let
        val (q2, r2) = subtract (q, r) (bin2dec (Integer.inc L1))
      in
        if intle Integer.zero q2 then
          raise (Floating_point "find_most_significant")
        else
          (L1, (q1, r1))
      end
    else
      let
        val (q0, r0) = subtract (q, r) (bin2dec L)
      in
        if intle Integer.zero q0 then
          (L, (q0, r0))
        else
          raise (Floating_point "find_most_significant")
      end
  end

fun approx_dec_by_bin n (q,r) =
  let
    fun addseq acc d' [] = acc
      | addseq acc d' (d::ds) = addseq (Integer.add acc (Integer.exp (Integer.sub d d'))) d' ds

    fun seq2bin [] = (Integer.zero, Integer.zero)
      | seq2bin (d::ds) = (Integer.inc (addseq Integer.zero d ds), d)

    fun approx d_seq d0 precision (q,r) =
      if q = Integer.zero then
        let val x = seq2bin d_seq in
          (x, x)
        end
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if intless precision (Integer.sub d0 d) then
            let
              val d' = Integer.sub d0 precision
              val x1 = seq2bin (d_seq)
              val x2 = (Integer.inc
                (Integer.mult (fst x1)
                (Integer.exp (Integer.sub (snd x1) d'))),  d') (* = seq2bin (d'::d_seq) *)
            in
              (x1, x2)
            end
          else
            approx (d::d_seq) d0 precision (q', r')
        end

    fun approx_start precision (q, r) =
      if q = Integer.zero then
        ((Integer.zero, Integer.zero), (Integer.zero, Integer.zero))
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if intle precision Integer.zero then
            let
              val x1 = seq2bin [d]
            in
              if q' = Integer.zero then
                (x1, x1)
              else
                (x1, seq2bin [Integer.inc d])
            end
          else
            approx [d] d precision (q', r')
        end
  in
    if intle Integer.zero q then
      approx_start n (q,r)
    else
      let
        val ((a1,b1), (a2, b2)) = approx_start n (Integer.neg q, r)
      in
        ((Integer.neg a2, b2), (Integer.neg a1, b1))
      end
  end

fun approx_decstr_by_bin n decstr =
  let
    fun str2int s = the_default Integer.zero (Integer.int_of_string s);
    fun signint p x = if p then x else Integer.neg x

    val (p, d1, d2, ep, e) = destruct_floatstr Char.isDigit (fn e => e = #"e" orelse e = #"E") decstr
    val s = Integer.int (size d2)

    val q = signint p (Integer.add (Integer.mult (str2int d1) (exp10 s)) (str2int d2))
    val r = Integer.sub (signint ep (str2int e)) s
  in
    approx_dec_by_bin (Integer.int n) (q,r)
  end

fun mk_float (a, b) = @{term "float"} $
  HOLogic.mk_prod (pairself (HOLogic.mk_number HOLogic.intT) (a, b));

fun dest_float (Const ("Float.float", _) $ (Const ("Pair", _) $ a $ b)) =
      pairself (snd o HOLogic.dest_number) (a, b)
  | dest_float t = ((snd o HOLogic.dest_number) t, Integer.zero);

fun approx_float prec f value =
  let
    val interval = approx_decstr_by_bin prec value
    val (flower, fupper) = f interval
  in
    (mk_float flower, mk_float fupper)
  end;

end;
