theory Predicate_Compile
imports Complex_Main Lattice_Syntax Code_Eval
uses "predicate_compile.ML"
begin

text {* Package setup *}

setup {* Predicate_Compile.setup *}

text {* Experimental code *}

ML {*
structure Predicate_Compile =
struct

open Predicate_Compile;

fun eval thy t_compr =
  let
    val t = Predicate_Compile.analyze_compr thy t_compr;
    val Type (@{type_name Predicate.pred}, [T]) = fastype_of t;
    fun mk_predT T = Type (@{type_name Predicate.pred}, [T]);
    val T1 = T --> @{typ term};
    val T2 = T1 --> mk_predT T --> mk_predT @{typ term};
    val t' = Const (@{const_name Predicate.map}, T2) (*FIXME*)
      $ Const (@{const_name Code_Eval.term_of}, T1) $ t;
  in (T, Code_ML.eval NONE ("Predicate_Compile.eval_ref", eval_ref) Predicate.map thy t' []) end;

fun values ctxt k t_compr =
  let
    val thy = ProofContext.theory_of ctxt;
    val (T, t') = eval thy t_compr;
  in t' |> Predicate.yieldn k |> fst |> HOLogic.mk_list T end;

fun values_cmd modes k raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = values ctxt k t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

end;

local structure P = OuterParse in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ = OuterSyntax.improper_command "values" "enumerate and print comprehensions" OuterKeyword.diag
  (opt_modes -- Scan.optional P.nat ~1 -- P.term
    >> (fn ((modes, k), t) => Toplevel.no_timing o Toplevel.keep
        (Predicate_Compile.values_cmd modes k t)));

end;
*}

end