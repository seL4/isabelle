(*  Title:      HOL/Matrix_LP/float_arith.ML
    Author:     Steven Obua
*)

signature FLOAT_ARITH =
sig
  exception Destruct_floatstr of string
  val destruct_floatstr: (char -> bool) -> (char -> bool) -> string -> bool * string * string * bool * string

  exception Floating_point of string
  val approx_dec_by_bin: int -> Float.float -> Float.float * Float.float
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
fun exp5 x = Integer.pow x 5;
fun exp10 x = Integer.pow x 10;
fun exp2 x = Integer.pow x 2;

fun find_most_significant q r =
  let
    fun int2real i =
      case (Real.fromString o string_of_int) i of
        SOME r => r
        | NONE => raise (Floating_point "int2real")
    fun subtract (q, r) (q', r') =
      if r <= r' then
        (q - q' * exp10 (r' - r), r)
      else
        (q * exp10 (r - r') - q', r')
    fun bin2dec d =
      if 0 <= d then
        (exp2 d, 0)
      else
        (exp5 (~ d), d)

    val L = Real.floor (int2real (Integer.log2 q) + int2real r * ln2_10)
    val L1 = L + 1

    val (q1, r1) = subtract (q, r) (bin2dec L1) 
  in
    if 0 <= q1 then
      let
        val (q2, r2) = subtract (q, r) (bin2dec (L1 + 1))
      in
        if 0 <= q2 then
          raise (Floating_point "find_most_significant")
        else
          (L1, (q1, r1))
      end
    else
      let
        val (q0, r0) = subtract (q, r) (bin2dec L)
      in
        if 0 <= q0 then
          (L, (q0, r0))
        else
          raise (Floating_point "find_most_significant")
      end
  end

fun approx_dec_by_bin n (q,r) =
  let
    fun addseq acc d' [] = acc
      | addseq acc d' (d::ds) = addseq (acc + exp2 (d - d')) d' ds

    fun seq2bin [] = (0, 0)
      | seq2bin (d::ds) = (addseq 0 d ds + 1, d)

    fun approx d_seq d0 precision (q,r) =
      if q = 0 then
        let val x = seq2bin d_seq in
          (x, x)
        end
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if precision < d0 - d then
            let
              val d' = d0 - precision
              val x1 = seq2bin (d_seq)
              val x2 = (fst x1 * exp2 (snd x1 - d') + 1,  d') (* = seq2bin (d'::d_seq) *)
            in
              (x1, x2)
            end
          else
            approx (d::d_seq) d0 precision (q', r')
        end

    fun approx_start precision (q, r) =
      if q = 0 then
        ((0, 0), (0, 0))
      else
        let
          val (d, (q', r')) = find_most_significant q r
        in
          if precision <= 0 then
            let
              val x1 = seq2bin [d]
            in
              if q' = 0 then
                (x1, x1)
              else
                (x1, seq2bin [d + 1])
            end
          else
            approx [d] d precision (q', r')
        end
  in
    if 0 <= q then
      approx_start n (q,r)
    else
      let
        val ((a1,b1), (a2, b2)) = approx_start n (~ q, r)
      in
        ((~ a2, b2), (~ a1, b1))
      end
  end

fun approx_decstr_by_bin n decstr =
  let
    fun str2int s = the_default 0 (Int.fromString s)
    fun signint p x = if p then x else ~ x

    val (p, d1, d2, ep, e) = destruct_floatstr Char.isDigit (fn e => e = #"e" orelse e = #"E") decstr
    val s = size d2

    val q = signint p (str2int d1 * exp10 s + str2int d2)
    val r = signint ep (str2int e) - s
  in
    approx_dec_by_bin n (q,r)
  end

fun mk_float (a, b) = \<^term>\<open>float\<close> $
  HOLogic.mk_prod (apply2 (HOLogic.mk_number HOLogic.intT) (a, b));

fun dest_float (Const (\<^const_name>\<open>float\<close>, _) $ (Const (\<^const_name>\<open>Pair\<close>, _) $ a $ b)) =
      apply2 (snd o HOLogic.dest_number) (a, b)
  | dest_float t = ((snd o HOLogic.dest_number) t, 0);

fun approx_float prec f value =
  let
    val interval = approx_decstr_by_bin prec value
    val (flower, fupper) = f interval
  in
    (mk_float flower, mk_float fupper)
  end;

end;
