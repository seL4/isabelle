(*  Title:      HOL/Word/Tools/smt_word.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for words.
*)

signature SMT_WORD =
sig
  val add_word_shift': term * string -> Context.generic -> Context.generic
end

structure SMT_Word : SMT_WORD =
struct

open Word_Lib


(* SMT-LIB logic *)

(* "QF_AUFBV" is too restrictive for Isabelle's problems, which contain aritmetic and quantifiers.
   Better set the logic to "" and make at least Z3 happy. *)
fun smtlib_logic ts =
  if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME "" else NONE


(* SMT-LIB builtins *)

local
  val smtlibC = SMTLIB_Interface.smtlibC

  val wordT = \<^typ>\<open>'a::len word\<close>

  fun index1 s i = "(_ " ^ s ^ " " ^ string_of_int i ^ ")"
  fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"

  fun word_typ (Type (\<^type_name>\<open>word\<close>, [T])) =
      Option.map (rpair [] o index1 "BitVec") (try dest_binT T)
    | word_typ _ = NONE

  fun word_num (Type (\<^type_name>\<open>word\<close>, [T])) k =
        Option.map (index1 ("bv" ^ string_of_int k)) (try dest_binT T)
    | word_num _ _ = NONE

  fun if_fixed pred m n T ts =
    let val (Us, U) = Term.strip_type T
    in
      if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
    end

  fun if_fixed_all m = if_fixed (forall (can dest_wordT) o (op ::)) m
  fun if_fixed_args m = if_fixed (forall (can dest_wordT) o snd) m

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end

  val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

  fun mk_shift' c [t, u] = Const c $ t $ mk_nat (snd (HOLogic.dest_number u))
    | mk_shift' c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift' m n T ts =
    let val U = Term.domain_type T
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd o tl) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd ts, HOLogic.mk_number U i], mk_shift' (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

  fun mk_shift c [u, t] = Const c $ mk_nat (snd (HOLogic.dest_number u)) $ t
    | mk_shift c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift m n T ts =
    let val U = Term.domain_type T
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd ts, HOLogic.mk_number U i], mk_shift (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

  fun mk_extract c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun extract m n T ts =
    let val U = Term.range_type (Term.range_type T)
    in
      (case (try (snd o HOLogic.dest_number o hd) ts, try dest_wordT U) of
        (SOME lb, SOME i) =>
          SOME (index2 n (i + lb - 1) lb, 1, tl ts, mk_extract (m, T) lb)
      | _ => NONE)
    end

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

  fun mk_rotate c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun rotate m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (snd o HOLogic.dest_number o hd) ts) of
        (true, SOME i) => SOME (index1 n i, 1, tl ts, mk_rotate (m, T) i)
      | _ => NONE)
    end
in

val setup_builtins =
  SMT_Builtin.add_builtin_typ smtlibC (wordT, word_typ, word_num) #>
  fold (add_word_fun if_fixed_all) [
    (\<^term>\<open>uminus :: 'a::len word \<Rightarrow> _\<close>, "bvneg"),
    (\<^term>\<open>plus :: 'a::len word \<Rightarrow> _\<close>, "bvadd"),
    (\<^term>\<open>minus :: 'a::len word \<Rightarrow> _\<close>, "bvsub"),
    (\<^term>\<open>times :: 'a::len word \<Rightarrow> _\<close>, "bvmul"),
    (\<^term>\<open>NOT :: 'a::len word \<Rightarrow> _\<close>, "bvnot"),
    (\<^term>\<open>(AND) :: 'a::len word \<Rightarrow> _\<close>, "bvand"),
    (\<^term>\<open>(OR) :: 'a::len word \<Rightarrow> _\<close>, "bvor"),
    (\<^term>\<open>(XOR) :: 'a::len word \<Rightarrow> _\<close>, "bvxor"),
    (\<^term>\<open>word_cat :: 'a::len word \<Rightarrow> _\<close>, "concat") ] #>
  fold (add_word_fun shift) [
    (\<^term>\<open>push_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _ \<close>, "bvshl"),
    (\<^term>\<open>drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvlshr"),
    (\<^term>\<open>signed_drop_bit :: nat \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "bvashr") ] #>
  add_word_fun extract
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
    (\<^term>\<open>word_sle\<close>, "bvsle") ]

val add_word_shift' = add_word_fun shift'

end


(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (20, smtlib_logic) #>
  setup_builtins))

end;
