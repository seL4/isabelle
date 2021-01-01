(*  Title:      HOL/Tools/numeral.ML
    Author:     Makarius

Logical and syntactic operations on numerals (see also HOL/Tools/hologic.ML).
*)

signature NUMERAL =
sig
  val mk_cnumber: ctyp -> int -> cterm
  val mk_number_syntax: int -> term
  val dest_num_syntax: term -> int
  val add_code: string -> (int -> int) -> (Code_Printer.literals -> int -> string) -> string -> theory -> theory
end;

structure Numeral: NUMERAL =
struct

(* numeral *)

fun dest_num_syntax (Const (\<^const_syntax>\<open>Num.Bit0\<close>, _) $ t) = 2 * dest_num_syntax t
  | dest_num_syntax (Const (\<^const_syntax>\<open>Num.Bit1\<close>, _) $ t) = 2 * dest_num_syntax t + 1
  | dest_num_syntax (Const (\<^const_syntax>\<open>Num.One\<close>, _)) = 1;

fun mk_num_syntax n =
  if n > 0 then
    (case Integer.quot_rem n 2 of
      (0, 1) => Syntax.const \<^const_syntax>\<open>One\<close>
    | (n, 0) => Syntax.const \<^const_syntax>\<open>Bit0\<close> $ mk_num_syntax n
    | (n, 1) => Syntax.const \<^const_syntax>\<open>Bit1\<close> $ mk_num_syntax n)
  else raise Match

fun mk_cbit 0 = \<^cterm>\<open>Num.Bit0\<close>
  | mk_cbit 1 = \<^cterm>\<open>Num.Bit1\<close>
  | mk_cbit _ = raise CTERM ("mk_cbit", []);

fun mk_cnumeral i =
  let
    fun mk 1 = \<^cterm>\<open>Num.One\<close>
      | mk i =
      let val (q, r) = Integer.div_mod i 2 in
        Thm.apply (mk_cbit r) (mk q)
      end
  in
    if i > 0 then mk i else raise CTERM ("mk_cnumeral: negative input", [])
  end


(* number *)

local

val cterm_of = Thm.cterm_of \<^context>;
fun tvar S = (("'a", 0), S);

val zero_tvar = tvar \<^sort>\<open>zero\<close>;
val zero = cterm_of (Const (\<^const_name>\<open>zero_class.zero\<close>, TVar zero_tvar));

val one_tvar = tvar \<^sort>\<open>one\<close>;
val one = cterm_of (Const (\<^const_name>\<open>one_class.one\<close>, TVar one_tvar));

val numeral_tvar = tvar \<^sort>\<open>numeral\<close>;
val numeral = cterm_of (Const (\<^const_name>\<open>numeral\<close>, \<^typ>\<open>num\<close> --> TVar numeral_tvar));

val uminus_tvar = tvar \<^sort>\<open>uminus\<close>;
val uminus = cterm_of (Const (\<^const_name>\<open>uminus\<close>, TVar uminus_tvar --> TVar uminus_tvar));

fun instT T v = Thm.instantiate_cterm ([(v, T)], []);

in

fun mk_cnumber T 0 = instT T zero_tvar zero
  | mk_cnumber T 1 = instT T one_tvar one
  | mk_cnumber T i =
      if i > 0 then
        Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral i)
      else
        Thm.apply (instT T uminus_tvar uminus)
          (Thm.apply (instT T numeral_tvar numeral) (mk_cnumeral (~ i)));

end;

fun mk_number_syntax n =
  if n = 0 then Syntax.const \<^const_syntax>\<open>Groups.zero\<close>
  else if n = 1 then Syntax.const \<^const_syntax>\<open>Groups.one\<close>
  else Syntax.const \<^const_syntax>\<open>numeral\<close> $ mk_num_syntax n;


(* code generator *)

local open Basic_Code_Thingol in

fun dest_num_code (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Num.One\<close>, ... }) = SOME 1
  | dest_num_code (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Num.Bit0\<close>, ... } `$ t) =
     (case dest_num_code t of
        SOME n => SOME (2 * n)
      | _ => NONE)
  | dest_num_code (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Num.Bit1\<close>, ... } `$ t) =
     (case dest_num_code t of
        SOME n => SOME (2 * n + 1)
      | _ => NONE)
  | dest_num_code _ = NONE;

fun add_code number_of preproc print target thy =
  let
    fun pretty literals _ thm _ _ [(t, _)] =
      case dest_num_code t of
        SOME n => (Code_Printer.str o print literals o preproc) n
      | NONE => Code_Printer.eqn_error thy thm "Illegal numeral expression: illegal term";
  in
    thy |> Code_Target.set_printings (Code_Symbol.Constant (number_of,
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty)))]))
  end;

end; (*local*)

end;
