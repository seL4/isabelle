(*  Title:      HOL/Tools/SMT/smt_real.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for reals.
*)

signature SMT_REAL =
sig
  val setup: theory -> theory
end

structure SMT_Real: SMT_REAL =
struct


(* SMT-LIB logic *)

fun smtlib_logic ts =
  if exists (Term.exists_type (Term.exists_subtype (equal @{typ real}))) ts
  then SOME "AUFLIRA"
  else NONE



(* SMT-LIB builtins *)

local
  fun smtlib_builtin_typ @{typ real} = SOME "Real"
    | smtlib_builtin_typ _ = NONE

  fun smtlib_builtin_num @{typ real} i = SOME (string_of_int i ^ ".0")
    | smtlib_builtin_num _ _ = NONE

  fun smtlib_builtin_func @{const_name uminus} ts = SOME ("~", ts)
    | smtlib_builtin_func @{const_name plus} ts = SOME ("+", ts)
    | smtlib_builtin_func @{const_name minus} ts = SOME ("-", ts)
    | smtlib_builtin_func @{const_name times} ts = SOME ("*", ts)
    | smtlib_builtin_func _ _ = NONE

  fun smtlib_builtin_pred @{const_name less} = SOME "<"
    | smtlib_builtin_pred @{const_name less_eq} = SOME "<="
    | smtlib_builtin_pred _ = NONE

  fun real_fun T y f x = 
    (case try Term.domain_type T of
      SOME @{typ real} => f x
    | _ => y)
in

val smtlib_builtins = {
  builtin_typ = smtlib_builtin_typ,
  builtin_num = smtlib_builtin_num,
  builtin_func = (fn (n, T) => real_fun T NONE (smtlib_builtin_func n)),
  builtin_pred = (fn (n, T) => fn ts =>
    real_fun T NONE smtlib_builtin_pred n |> Option.map (rpair ts)),
  is_builtin_pred = (fn n => fn T =>
    real_fun T false (is_some o smtlib_builtin_pred) n) }

end



(* Z3 builtins *)

local
  fun z3_builtin_fun @{term "op / :: real => _"} ts = SOME ("/", ts)
    | z3_builtin_fun _ _ = NONE
in

val z3_builtins = (fn c => fn ts => z3_builtin_fun (Const c) ts)

end



(* Z3 constructors *)

local
  structure I = Z3_Interface

  fun z3_mk_builtin_typ (I.Sym ("real", _)) = SOME @{typ real}
    | z3_mk_builtin_typ _ = NONE

  fun z3_mk_builtin_num _ i T =
    if T = @{typ real} then SOME (Numeral.mk_cnumber @{ctyp real} i)
    else NONE

  val mk_uminus = Thm.capply @{cterm "uminus :: real => _"}
  val mk_add = Thm.mk_binop @{cterm "op + :: real => _"}
  val mk_sub = Thm.mk_binop @{cterm "op - :: real => _"}
  val mk_mul = Thm.mk_binop @{cterm "op * :: real => _"}
  val mk_div = Thm.mk_binop @{cterm "op / :: real => _"}
  val mk_lt = Thm.mk_binop @{cterm "op < :: real => _"}
  val mk_le = Thm.mk_binop @{cterm "op <= :: real => _"}

  fun z3_mk_builtin_fun (I.Sym ("-", _)) [ct] = SOME (mk_uminus ct)
    | z3_mk_builtin_fun (I.Sym ("+", _)) [ct, cu] = SOME (mk_add ct cu)
    | z3_mk_builtin_fun (I.Sym ("-", _)) [ct, cu] = SOME (mk_sub ct cu)
    | z3_mk_builtin_fun (I.Sym ("*", _)) [ct, cu] = SOME (mk_mul ct cu)
    | z3_mk_builtin_fun (I.Sym ("/", _)) [ct, cu] = SOME (mk_div ct cu)
    | z3_mk_builtin_fun (I.Sym ("<", _)) [ct, cu] = SOME (mk_lt ct cu)
    | z3_mk_builtin_fun (I.Sym ("<=", _)) [ct, cu] = SOME (mk_le ct cu)
    | z3_mk_builtin_fun (I.Sym (">", _)) [ct, cu] = SOME (mk_lt cu ct)
    | z3_mk_builtin_fun (I.Sym (">=", _)) [ct, cu] = SOME (mk_le cu ct)
    | z3_mk_builtin_fun _ _ = NONE
in

val z3_mk_builtins = {
  mk_builtin_typ = z3_mk_builtin_typ,
  mk_builtin_num = z3_mk_builtin_num,
  mk_builtin_fun = (fn _ => fn sym => fn cts =>
    (case try (#T o Thm.rep_cterm o hd) cts of
      SOME @{typ real} => z3_mk_builtin_fun sym cts
    | _ => NONE)) }

end



(* Z3 proof reconstruction *)

val real_rules = @{lemma
  "0 + (x::real) = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto}

val real_linarith_proc = Simplifier.simproc @{theory} "fast_real_arith" [
  "(m::real) < n", "(m::real) <= n", "(m::real) = n"] (K Lin_Arith.simproc)



(* setup *)

val setup =
  Context.theory_map (
    SMTLIB_Interface.add_logic smtlib_logic #>
    SMTLIB_Interface.add_builtins smtlib_builtins #>
    Z3_Interface.add_builtin_funs z3_builtins #>
    Z3_Interface.add_mk_builtins z3_mk_builtins #>
    fold Z3_Proof_Reconstruction.add_z3_rule real_rules #>
    Z3_Proof_Tools.add_simproc real_linarith_proc)

end
