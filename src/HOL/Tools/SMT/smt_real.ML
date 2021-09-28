(*  Title:      HOL/Tools/SMT/smt_real.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for reals.
*)

structure SMT_Real: sig end =
struct


(* SMT-LIB logic *)

fun smtlib_logic ts =
  if exists (Term.exists_type (Term.exists_subtype (equal \<^typ>\<open>real\<close>))) ts
  then SOME "AUFLIRA"
  else NONE


(* SMT-LIB and Z3 built-ins *)

local
  fun real_num _ i = SOME (string_of_int i ^ ".0")

  fun is_linear [t] = SMT_Util.is_number t
    | is_linear [t, u] = SMT_Util.is_number t orelse SMT_Util.is_number u
    | is_linear _ = false

  fun mk_times ts = Term.list_comb (\<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, ts)

  fun times _ _ ts = if is_linear ts then SOME ("*", 2, ts, mk_times) else NONE
in

val setup_builtins =
  SMT_Builtin.add_builtin_typ SMTLIB_Interface.smtlibC
    (\<^typ>\<open>real\<close>, K (SOME ("Real", [])), real_num) #>
  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.smtlibC) [
    (\<^Const>\<open>less \<^Type>\<open>real\<close>\<close>, "<"),
    (\<^Const>\<open>less_eq \<^Type>\<open>real\<close>\<close>, "<="),
    (\<^Const>\<open>uminus \<^Type>\<open>real\<close>\<close>, "-"),
    (\<^Const>\<open>plus \<^Type>\<open>real\<close>\<close>, "+"),
    (\<^Const>\<open>minus \<^Type>\<open>real\<close>\<close>, "-") ] #>
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (Term.dest_Const \<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, times) #>
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (\<^Const>\<open>times \<^Type>\<open>real\<close>\<close>, "*") #>
  SMT_Builtin.add_builtin_fun' Z3_Interface.smtlib_z3C
    (\<^Const>\<open>divide \<^Type>\<open>real\<close>\<close>, "/")

end


(* Z3 constructors *)

local
  fun z3_mk_builtin_typ (Z3_Interface.Sym ("Real", _)) = SOME \<^typ>\<open>real\<close>
    | z3_mk_builtin_typ (Z3_Interface.Sym ("real", _)) = SOME \<^typ>\<open>real\<close>
        (*FIXME: delete*)
    | z3_mk_builtin_typ _ = NONE

  fun z3_mk_builtin_num _ i T =
    if T = \<^typ>\<open>real\<close> then SOME (Numeral.mk_cnumber \<^ctyp>\<open>real\<close> i)
    else NONE

  fun mk_nary _ cu [] = cu
    | mk_nary ct _ cts = uncurry (fold_rev (Thm.mk_binop ct)) (split_last cts)

  val mk_uminus = Thm.apply \<^cterm>\<open>uminus :: real \<Rightarrow> _\<close>
  val add = \<^cterm>\<open>(+) :: real \<Rightarrow> _\<close>
  val real0 = Numeral.mk_cnumber \<^ctyp>\<open>real\<close> 0
  val mk_sub = Thm.mk_binop \<^cterm>\<open>(-) :: real \<Rightarrow> _\<close>
  val mk_mul = Thm.mk_binop \<^cterm>\<open>(*) :: real \<Rightarrow> _\<close>
  val mk_div = Thm.mk_binop \<^cterm>\<open>(/) :: real \<Rightarrow> _\<close>
  val mk_lt = Thm.mk_binop \<^cterm>\<open>(<) :: real \<Rightarrow> _\<close>
  val mk_le = Thm.mk_binop \<^cterm>\<open>(\<le>) :: real \<Rightarrow> _\<close>

  fun z3_mk_builtin_fun (Z3_Interface.Sym ("-", _)) [ct] = SOME (mk_uminus ct)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("+", _)) cts = SOME (mk_nary add real0 cts)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("-", _)) [ct, cu] = SOME (mk_sub ct cu)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("*", _)) [ct, cu] = SOME (mk_mul ct cu)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("/", _)) [ct, cu] = SOME (mk_div ct cu)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("<", _)) [ct, cu] = SOME (mk_lt ct cu)
    | z3_mk_builtin_fun (Z3_Interface.Sym ("<=", _)) [ct, cu] = SOME (mk_le ct cu)
    | z3_mk_builtin_fun (Z3_Interface.Sym (">", _)) [ct, cu] = SOME (mk_lt cu ct)
    | z3_mk_builtin_fun (Z3_Interface.Sym (">=", _)) [ct, cu] = SOME (mk_le cu ct)
    | z3_mk_builtin_fun _ _ = NONE
in

val z3_mk_builtins = {
  mk_builtin_typ = z3_mk_builtin_typ,
  mk_builtin_num = z3_mk_builtin_num,
  mk_builtin_fun = (fn _ => fn sym => fn cts =>
    (case try (Thm.typ_of_cterm o hd) cts of
      SOME \<^typ>\<open>real\<close> => z3_mk_builtin_fun sym cts
    | _ => NONE)) }

end


(* Z3 proof replay *)

val real_linarith_proc =
  Simplifier.make_simproc \<^context> "fast_real_arith"
   {lhss = [\<^term>\<open>(m::real) < n\<close>, \<^term>\<open>(m::real) \<le> n\<close>, \<^term>\<open>(m::real) = n\<close>],
    proc = K Lin_Arith.simproc}


(* setup *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (10, smtlib_logic) #>
  setup_builtins #>
  Z3_Interface.add_mk_builtins z3_mk_builtins #>
  SMT_Replay.add_simproc real_linarith_proc))

end;
