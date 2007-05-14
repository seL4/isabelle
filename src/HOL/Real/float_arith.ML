(*  Title: HOL/Real/Float.ML
    ID:    $Id$
    Author: Steven Obua
*)

signature FLOAT_ARITH =
sig
  exception Destruct_floatstr of string
  val destruct_floatstr: (char -> bool) -> (char -> bool) -> string -> bool * string * string * bool * string

  exception Floating_point of string
  val approx_dec_by_bin: Intt.int -> Float.float -> Float.float * Float.float
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
val exp5 = Intt.pow (Intt.int 5);
val exp10 = Intt.pow (Intt.int 10);

fun intle a b = not (Intt.cmp (a, b) = GREATER);
fun intless a b = Intt.cmp (a, b) = LESS;

fun find_most_significant q r =
  let
    fun int2real i =
      case (Real.fromString o Intt.string_of_int) i of
        SOME r => r
        | NONE => raise (Floating_point "int2real")
    fun subtract (q, r) (q', r') =
      if intle r r' then
        (Intt.sub q (Intt.mult q' (exp10 (Intt.sub r' r))), r)
      else
        (Intt.sub (Intt.mult q (exp10 (Intt.sub r r'))) q', r')
    fun bin2dec d =
      if intle Intt.zero d then
        (Intt.exp d, Intt.zero)
      else
        (exp5 (Intt.neg d), d)

    val L = Intt.int (Real.floor (int2real (Intt.log q) + int2real r * ln2_10))
    val L1 = Intt.inc L

    val (q1, r1) = subtract (q, r) (bin2dec L1) 
  in
    if intle Intt.zero q1 then
      let
        val (q2, r2) = subtract (q, r) (bin2dec (Intt.inc L1))
      in
        if intle Intt.zero q2 then
          raise (Floating_point "find_most_significant")
        else
          (L1, (q1, r1))
      end
    else
      let
        val (q0, r0) = subtract (q, r) (bin2dec L)
      in
        if intle Intt.zero q0 then
          (L, (q0, r0))
        else
          raise (Floating_point "find_most_significant")
      end
  end

fun approx_dec_by_bin n (q,r) =
  let
    fun addseq acc d' [] = acc
      | addseq acc d' (d::ds) = addseq (Intt.add acc (Intt.exp (Intt.sub d d'))) d' ds

    fun seq2bin [] = (Intt.zero, Intt.zero)
      | seq2bin (d::ds) = (Intt.inc (addseq Intt.zero d ds), d)

    fun approx d_seq d0 precision (q,r) =
      if q = Intt.zero then
        let val x = seq2bin d_seq in
          (x, x)
        end
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if intless precision (Intt.sub d0 d) then
            let
              val d' = Intt.sub d0 precision
              val x1 = seq2bin (d_seq)
              val x2 = (Intt.inc
                (Intt.mult (fst x1)
                (Intt.exp (Intt.sub (snd x1) d'))),  d') (* = seq2bin (d'::d_seq) *)
            in
              (x1, x2)
            end
          else
            approx (d::d_seq) d0 precision (q', r')
        end

    fun approx_start precision (q, r) =
      if q = Intt.zero then
        ((Intt.zero, Intt.zero), (Intt.zero, Intt.zero))
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if intle precision Intt.zero then
            let
              val x1 = seq2bin [d]
            in
              if q' = Intt.zero then
                (x1, x1)
              else
                (x1, seq2bin [Intt.inc d])
            end
          else
            approx [d] d precision (q', r')
        end
  in
    if intle Intt.zero q then
      approx_start n (q,r)
    else
      let
        val ((a1,b1), (a2, b2)) = approx_start n (Intt.neg q, r)
      in
        ((Intt.neg a2, b2), (Intt.neg a1, b1))
      end
  end

fun approx_decstr_by_bin n decstr =
  let
    fun str2int s = the_default Intt.zero (Intt.int_of_string s);
    fun signint p x = if p then x else Intt.neg x

    val (p, d1, d2, ep, e) = destruct_floatstr Char.isDigit (fn e => e = #"e" orelse e = #"E") decstr
    val s = Intt.int (size d2)

    val q = signint p (Intt.add (Intt.mult (str2int d1) (exp10 s)) (str2int d2))
    val r = Intt.sub (signint ep (str2int e)) s
  in
    approx_dec_by_bin (Intt.int n) (q,r)
  end

fun mk_float (a, b) = @{term "float"} $
  HOLogic.mk_prod (pairself (HOLogic.mk_number HOLogic.intT) (a, b));

fun dest_float (Const ("Float.float", _) $ (Const ("Pair", _) $ a $ b)) =
      pairself (snd o HOLogic.dest_number) (a, b)
  | dest_float t = ((snd o HOLogic.dest_number) t, Intt.zero);

fun approx_float prec f value =
  let
    val interval = approx_decstr_by_bin prec value
    val (flower, fupper) = f interval
  in
    (mk_float flower, mk_float fupper)
  end;

end;
