(*  Title:      HOL/Library/Tools/smt_word.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

SMT setup for words.
*)

signature SMT_WORD =
sig
  val mk_bv_from_int_base: term -> term -> term
end

structure SMT_Word : SMT_WORD =
struct

open Word_Lib

(* SMT-LIB logic *)

(* "QF_AUFBV" is too restrictive for Isabelle's problems, which contain aritmetic and quantifiers.
   Better set the logic to "" and make at least Z3 happy. *)
fun smtlib_logic "z3" ts _ =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts
    then SOME (SMT_Translate.NO_LOGIC)
    else NONE
  | smtlib_logic "verit" _ _ = NONE
  | smtlib_logic _ ts _ =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts
    then SOME (SMT_Translate.SL ({fixedSizeBitVectors=true,real=true,set=false,
      datatypes=false}:SMT_Translate.smtlib_theories))
    else NONE


(* Utils *)

val smtlibC = SMTLIB_Interface.bvsmtlibC
val wordT = \<^typ>\<open>'a::len word\<close>
fun index1 s i = "(_ " ^ s ^ " " ^ string_of_int i ^ ")"
fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"
val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

fun remove_cast (Const (\<^const_name>\<open>Int.nat\<close>, _) $ x) = x |
    remove_cast x = x

fun if_fixed pred m n T ts =
  let
    val (Us, U) = Term.strip_type T
  in
    if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
  end

fun if_concrete_bw_all_args m = if_fixed (forall (can dest_wordT) o (op ::)) m
fun if_fixed_args m = if_fixed (forall (can dest_wordT) o snd) m


fun add_word_fun f (t, n) =
  let
    val m = dest_Const_name t
  in
    SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n))
  end

(*
Translation. The translation functions are unfortunatley applied several times. So if a translation
is not faithful this leads to problems. E.g., even if we know that an argument always has the form
(word_of_int t2') the first time this is called. But if we change the term on subsequent calls we do not know this.
*)



(** Translate bv constants and types **)

fun word_typ (Type (\<^type_name>\<open>word\<close>, [T])) = Option.map (rpair [] o index1 "BitVec") (try dest_binT T) |
    word_typ (Type (_, [T])) = Option.map (rpair [] o index1 "BitVec") (try dest_binT T) |
    word_typ _ = NONE

(*
CVC4 and cvc5 do not support "_bvk T" when k does not fit in the BV of size T, so remove the bits that
will be ignored according to the SMT-LIB. This is only important if nat to int lifting is not used.

*)

fun word_num (Type (\<^type_name>\<open>word\<close>, [T])) k =
let
  val size = try dest_binT T
  fun max_int size = Integer.pow size 2
in
  (case size of
    NONE => NONE
  | SOME size => SOME (index1 ("bv" ^ string_of_int (Int.rem(k, max_int size))) size))
  end
| word_num _ _ = NONE



(*shifts*)


  fun mk_shift c [u, t] = Const c $ mk_nat (snd (HOLogic.dest_number u)) $ t
    | mk_shift c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd (tl ts), HOLogic.mk_number U i], mk_shift (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

fun mk_extract c i ts = Term.list_comb (Const c, mk_nat i :: ts)

fun slice m n (T as (Type(_,[_,Type(_,[Tx,U])]))) ts =
   (case (try (snd o HOLogic.dest_number o remove_cast o hd) ts,
          try dest_wordT U,
          try dest_wordT Tx) of
    (SOME j, SOME k, SOME i') =>
     let
      val i = i' - 1
     in
      if i >= j andalso k = i' - j (*i > k is implicit*)
      then (SOME (index2 n i j, 1, tl ts, mk_extract (m, T) j))
      else NONE
     end
    | _ => NONE) |
  slice _ _ _ _ = (NONE)


fun take_bit m _ T ts =
    let

      val ts = ts |> map (fn (Const (\<^const_name>\<open>Int.nat\<close>, _) $ x) => x | x => x)
      val word= hd (tl ts)
      val U = Term.domain_type (Term.range_type T)

    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          let
            val str=""
            val offset' = HOLogic.mk_number @{typ "nat"} i
            val minus=  Const(\<^const_name>\<open>minus\<close>, U --> U --> U)

            val drop=  Const(\<^const_name>\<open>drop_bit\<close>, @{typ "nat"} --> U --> U)
            val push=  Const(\<^const_name>\<open>push_bit\<close>, @{typ "nat"} --> U --> U)
            fun mk_take_bit _ ts = hd ts

            val new_term = minus $ word $
 (push $ offset' $ (drop $ offset' $ word))
          in
          SOME (str, 1, [new_term], mk_take_bit (m, T)) end
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

fun bit m n T ts =
    let

      val word = hd ts
      val pos = hd (tl ts)

      val suc_simplified =
      (case (try (snd o HOLogic.dest_number o remove_cast) pos) of
        SOME i' => (HOLogic.mk_number @{typ "nat"} (i'+1))
      | NONE => (Const(\<^const_name>\<open>Nat.Suc\<close>,@{typ "nat"} --> @{typ "nat"}) $ pos))

      val pos_simplified =
        (case (try (snd o HOLogic.dest_number o remove_cast) pos) of
          SOME i' => (HOLogic.mk_number @{typ "nat"} (i'))
        | NONE => (Const(\<^const_name>\<open>Nat.Suc\<close>,@{typ "nat"} --> @{typ "nat"}) $ pos))

     fun cond i i_suc =
       (Const("smt_extract", @{typ "nat"} --> @{typ "nat"} --> fastype_of (word) -->
         @{typ "1 word"}) $ i $ i $ word)

      fun new_ts i i_suc =
          Const(\<^const_name>\<open>HOL.eq\<close>, @{typ "1 word"} -->  @{typ "1 word"} --> @{typ "bool"}) $
          cond i i_suc $
          @{term "1::1 word"}

      fun mk_bit ts = (hd ts)

    in  SOME ("", 1, [new_ts pos_simplified suc_simplified ], mk_bit) end


  fun mk_extend c ts = Term.list_comb (Const c, ts)

  fun extend m n T ts =
    let val (U1, U2) = Term.dest_funT T
    in
      (case (try dest_wordT U1, try dest_wordT U2) of
        (SOME i, SOME j) =>
          if j-i >= 0 then SOME (index1 n (j-i), 1, ts, mk_extend (m, T))
          else NONE
      | _ => NONE)
    end
  fun mk_extend (m,T) ts = Term.list_comb (Const (m,T),ts)


  fun is_numeral x = try HOLogic.dest_numeral x

(*
Wird zweimal uebersetzt wie alles...
*)
  fun power m n T ts =
    let

      val (U1, U2) = Term.dest_funT T

      val bitwidth = U1  |> Term.dest_Type |> snd |> hd |> dest_binT
      val wordT = mk_wordT bitwidth
      val one = Const(\<^const_name>\<open>Groups.one_class.one\<close>, wordT)
      (*val shift_amount = Const ("Word.Word", @{typ "int"} --> wordT) $ (nth ts 1)*)
      val t1 = nth ts 1
      val (t2 $ t3) = t1
      val shift_amount =
        (case is_numeral t3 of
          NONE => @{term "unsigned"} $ t3 |
          SOME _ => Const (\<^const_name>\<open>Num.numeral_class.numeral\<close>, @{typ "num"} --> wordT) $ t3)
    in

         (SOME ("bvshl", 2, [one,shift_amount], (fn _ =>  mk_extend (m,T) ts) ))
    end


  (*Is currently not used for constants anymore. Thus, it should be deleted once it is clear we want
    to keep using the normalization.*)
  fun len_of_lift m n T [t1] =
  let
    val (_,b) = dest_Const t1
    val (_,[c]) = dest_Type b
  in
  (case try dest_binT c of
   NONE =>  NONE |
   SOME len =>
     let
       val d = len |> HOLogic.mk_number @{typ int}
     in
         (SOME ("", 1, [d], fn _ => d))
     end
   ) end |
 len_of_lift _ _ _ _  = NONE


  fun mk_rotate c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun rotate m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) => SOME (index1 n i, 1, tl ts, mk_rotate (m, T) i)
      | _ => NONE)
    end

  fun len_of t m n T ts =
    let
      fun mk_num T x =
        let
          val _ = HOLogic.mk_number HOLogic.intT (dest_binT T)
        in Const (\<^const_name>\<open>nat\<close>, @{typ "int => nat"}) $
            HOLogic.mk_number HOLogic.intT (dest_binT T) end
    in
     (case head_of (hd ts) of
         Const (_, Type (\<^type_name>\<open>itself\<close>, [T])) =>
           SOME ("len_of" (*fudge*), 0, [], (mk_num T))
       | _ => NONE)
    end
  fun add_len_of (t,n) =
    let val (m, _) = Term.dest_Const (head_of t)
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t), fn _ => (fn x => fn y =>len_of t m n x y))
 end

  fun mk_op m T ts = Term.list_comb (Const(m,T),ts)
  fun word_of_int m n T ts =
  let
    val U = Term.range_type T
  in
   (case try dest_wordT U of
     NONE => NONE |
     SOME U' => SOME (index1 n U', 1, ts,mk_op m T))
  end

  fun word_constructor m n T [t1] =
  let
    in
    (SOME (n, 1, [t1], (fn t =>mk_extend (m,T) [t1])))
    end |
  word_constructor _ _ _ _ = NONE

  fun of_nat t m n T ts =
    let
      fun mk_num T x =
        let
          val _ = HOLogic.mk_number HOLogic.natT (dest_binT T)
        in HOLogic.mk_number HOLogic.natT (dest_binT T) end
    in
     (case (head_of (hd ts)) of
         Const (_, Type (\<^type_name>\<open>itself\<close>, [T])) =>
           SOME ("LENGTHXXXXX", 0, [], (mk_num T))
       | _ => NONE)
    end
  fun add_of_nat (a as t,n) =
    let val (m, _) = Term.dest_Const t
      val n = HOLogic.dest_number t |> snd |> K true
               handle TERM _ => false

    in
      if n then SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t), fn x => (@{print} x;
         fn x => fn y =>(of_nat t m n x y)))
       else  SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const (head_of t),  K (K (K (NONE))))
   end

fun concat op_name smt_name (typ as (Type(_,[T1,Type(_,[T2,T])]))) terms =
 (case (try dest_wordT T1, try dest_wordT T2, try dest_wordT T) of
  (SOME i, SOME j, SOME k) =>
   (if (i + j = k)
    then (if_fixed (forall (can dest_wordT) o (op ::)) op_name smt_name typ terms)
     else NONE) |
  _ => NONE) |
 concat _ _ _ _ = NONE


val bit_ops_table = [
  (\<^const_name>\<open>bit\<close>, @{thm min_def_raw})]

val setup_bit_ops_table = fold (SMT_Builtin.add_builtin_fun_ext'' o fst) bit_ops_table

val _ = Theory.setup (Context.theory_map (setup_bit_ops_table))


val setup_builtins =
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmtlibC (wordT, word_typ, word_num) #>
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmtlibC
    (\<^typ>\<open>Num.num \<Rightarrow> 'a::len word\<close>, word_typ, word_num) #>
  fold (add_word_fun if_concrete_bw_all_args) [
    (\<^term>\<open>uminus :: 'a::len word \<Rightarrow> _\<close>, "bvneg"),
    (\<^term>\<open>plus :: 'a::len word \<Rightarrow> _\<close>, "bvadd"),
    (\<^term>\<open>minus :: 'a::len word \<Rightarrow> _\<close>, "bvsub"),
    (\<^term>\<open>times :: 'a::len word \<Rightarrow> _\<close>, "bvmul"),
    (\<^term>\<open>not :: 'a::len word \<Rightarrow> _\<close>, "bvnot"),
    (\<^term>\<open>and :: 'a::len word \<Rightarrow> _\<close>, "bvand"),
    (\<^term>\<open>or :: 'a::len word \<Rightarrow> _\<close>, "bvor"),
    (\<^term>\<open>xor :: 'a::len word \<Rightarrow> _\<close>, "bvxor"),
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat") ] #>
  fold (add_word_fun shift) [
    (\<^term>\<open>push_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _ \<close>, "bvshl"),
    (\<^term>\<open>drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>signed_drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvashr") ] #>
  (*If lifting nats to ints is not active*)


  add_word_fun concat
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat")  #>
  add_word_fun slice
    (\<^term>\<open>slice :: _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "extract") #>
  fold (add_word_fun extend) [
    (\<^term>\<open>ucast :: 'a::len word \<Rightarrow> _\<close>, "zero_extend"),
    (\<^term>\<open>scast :: 'a::len word \<Rightarrow> _\<close>, "sign_extend") ] #>
  fold (add_word_fun rotate) [
    (\<^term>\<open>word_rotl\<close>, "rotate_left"),
    (\<^term>\<open>word_rotr\<close>, "rotate_right") ] #>
  fold (add_word_fun if_fixed_args) [
    (\<^term>\<open>less :: 'a::len word \<Rightarrow> _\<close>, "bvult"),
    (\<^term>\<open>less_eq :: 'a::len word \<Rightarrow> _\<close>, "bvule"),
    (\<^term>\<open>word_sless\<close>, "bvslt"),
    (\<^term>\<open>word_sle\<close>, "bvsle") ] #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.bvsmtlibC) [
    (\<^term>\<open>unsigned :: 'a::len word \<Rightarrow> Int.int\<close>, "ubv_to_int"),
    (\<^term>\<open>unsigned :: 'a::len word \<Rightarrow> Nat.nat\<close>, "ubv_to_int")
   ] #>
  fold (add_word_fun word_of_int) [
    (\<^term>\<open>of_int :: Int.int => 'a::len word\<close>, "int_to_bv"),
    (\<^term>\<open>of_nat :: Nat.nat => 'a::len word\<close>, "int_to_bv"),(*TODO: This should be done as embedding.*)

    (\<^term>\<open>Word.Word :: Int.int \<Rightarrow> 'a::len word\<close>, "int_to_bv")
  ] #>
  fold (add_word_fun take_bit) [
    (\<^term>\<open>take_bit :: _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "TODO")

   ] #>
  fold (add_word_fun bit) [
    (\<^term>\<open>bit :: 'a::len word \<Rightarrow> _ \<Rightarrow> _\<close>, "bit")
   ]




(* Proof Reconstruction *)

open SMT_Parser_Util

val split_last =
  let fun split_last [a] = ([], a)
       | split_last (x :: xs) = apfst (curry (op ::) x) (split_last xs)
  in apfst List.rev o split_last end

fun mk_word_of_int i u = SOME (Const (\<^const_name>\<open>of_int\<close>, @{typ int} --> (Word_Lib.mk_wordT i)) $ u)
fun mk_word_of_int' i u = SOME (Const (\<^const_name>\<open>of_int\<close>, @{typ int} --> (Word_Lib.mk_wordT (snd (HOLogic.dest_number i)))) $ u)

fun mk_zero_extend i u =
  let
    val T = fastype_of u
  in
    case (try dest_wordT T) of
      (SOME j) => SOME (Const (\<^const_name>\<open>Word.cast\<close>, T --> (Word_Lib.mk_wordT (i+j))) $ u) |
      _ => NONE
  end

fun mk_scast i u =
  let
    val T = fastype_of u
    val j = Word_Lib.dest_wordT T
    val TU = Word_Lib.mk_wordT (i + j)
  in Const (\<^const_name>\<open>Word.signed\<close>, T --> TU) $ u end;

fun mk_bv_from_int_base int base =
 let
        val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
         handle TERM ("dest_number", [t ]) => (@{print}("t",t); raise Alethe_Proof.ALETHE_PROOF_PARSE "Could not parse bit-vector value")
      in
        (HOLogic.mk_number ty num)
      end



fun
  (*From the FixedSizeBitVectors theory*)
  bv_term_parser (SMTLIB.BVNum (i, base), []) = SOME (HOLogic.mk_number (mk_wordT(base)) (i) )
  | bv_term_parser (SMTLIB.Sym "bvnot", [t1]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> t1)
  | bv_term_parser (SMTLIB.Sym "bvneg", [t]) =
      SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | bv_term_parser (SMTLIB.Sym "bvand", (t::ts)) =
      SOME (mk_lassoc' \<^const_name>\<open>semiring_bit_operations_class.and\<close> t ts)
  | bv_term_parser (SMTLIB.Sym "bv", [int, base]) = SOME (mk_bv_from_int_base int base)
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_",SMTLIB.Sym n, SMTLIB.Num base],[]) =
    (case try (unprefix "bv") n of
        NONE => NONE
      | SOME t =>
         (case Int.fromString t of
         NONE => NONE
         |SOME t' =>
         let
          val int = HOLogic.mk_number @{typ int} t'
         in
           SOME (mk_bv_from_int_base int (HOLogic.mk_number @{typ int} base))
         end)
     )
  | bv_term_parser (SMTLIB.Sym "_", [Free(n,_),base]) =
    (case try (unprefix "bv") n of
        NONE => NONE
      | SOME t =>
         (case Int.fromString t of
         NONE => NONE
         |SOME t' =>
         let
          val int = HOLogic.mk_number @{typ int} t'
         in
           SOME (mk_bv_from_int_base int base)
         end)
     )
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "int_to_bv", SMTLIB.Num i], [t]) =
      mk_word_of_int i t
  | bv_term_parser (SMTLIB.Sym "int_to_bv", [i,t]) =
      mk_word_of_int' i t
  | bv_term_parser (SMTLIB.Sym "ubv_to_int",[t1]) =
      let
        val T1 = fastype_of t1
      in
        SOME (Const (\<^const_name>\<open>unsigned\<close>, T1 --> @{typ int}) $ t1)
      end
  | bv_term_parser (SMTLIB.Sym "sbv_to_int",[t1]) =
      let
        val T1 = fastype_of t1
      in
        SOME (Const (\<^const_name>\<open>signed\<close>, T1 --> @{typ int}) $ t1)
      end
  | bv_term_parser (SMTLIB.Sym "bvult", [t1, t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvule", [t1, t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvadd", t) =
      let val (xs, a) = split_last t
      in
        SOME (fold (curry (HOLogic.mk_binop \<^const_name>\<open>Groups.plus\<close>)) xs a)
      end
  | bv_term_parser (SMTLIB.Sym "bvsub", t) =
      let val (xs, a) = split_last t
      in
        SOME (fold (curry (HOLogic.mk_binop \<^const_name>\<open>Groups.minus\<close>)) xs a)
      end
  | bv_term_parser (SMTLIB.Sym "bvmul", (t::ts)) =
      let
        val T = fastype_of t
      in
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>Groups.times\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end

  | bv_term_parser (SMTLIB.Sym "bvor", (t::ts)) =
      let
        val T = fastype_of t
      in
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>semiring_bit_operations_class.or\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvxor", (t::ts)) =
      let
        val T = fastype_of t
      in
        SOME (mk_lassoc (fn t1 => fn t2 => (Const ( \<^const_name>\<open>semiring_bit_operations_class.xor\<close>, T --> T --> T)) $ t1 $ t2) t ts)
      end
  | bv_term_parser (SMTLIB.Sym "bvxnor", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.xor\<close> (t1, t2)))

  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "zero_extend", SMTLIB.Num i], [t]) =
      mk_zero_extend i t
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "sign_extend", SMTLIB.Num i], [t]) =
      SOME (mk_scast i t)
  | bv_term_parser (SMTLIB.Sym "sign_extend", [t1, t2]) =
     SOME (Const (\<^const_name>\<open>Word.signed_cast\<close>, fastype_of t2 --> dummyT) $ t2)
  | bv_term_parser (SMTLIB.Sym "zero_extend", [t1, t2]) =
     SOME (Const (\<^const_name>\<open>Word.unsigned\<close>, fastype_of t2 --> dummyT) $ t2)
  | bv_term_parser (SMTLIB.Sym "concat", t1 :: t2 :: ts) =
  let
    fun cat_op I1 I2 O = (Const ( \<^const_name>\<open>word_cat\<close>, I1 --> I2 --> O))
    fun res_type I1 I2 = (dest_wordT I1 + dest_wordT I2) |> mk_wordT


    fun bitwidthConcat [x] = (x,(fastype_of x))
      | bitwidthConcat (x::xs) =
        let
          val (curr_t, currT) = bitwidthConcat xs
          val xT = fastype_of x
          val resT = res_type xT currT
        in
          (((cat_op xT currT resT) $ x $ curr_t),resT)
        end
    val (res,_) = bitwidthConcat (t1::t2::ts)
  in (SOME (res)) end

  | bv_term_parser xs = NONE

fun bv_type_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "BitVec", SMTLIB.Num x], []) =
    SOME (Word_Lib.mk_wordT x)
  | bv_type_parser _ = NONE

(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (30, smtlib_logic) #>
  setup_builtins))

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser bv_type_parser #>
  SMTLIB_Proof.add_term_parser bv_term_parser))

end
