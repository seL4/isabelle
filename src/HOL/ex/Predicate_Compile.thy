theory Predicate_Compile
imports Complex_Main Lattice_Syntax Code_Eval
uses "predicate_compile.ML"
begin

text {* Package setup *}

setup {* Predicate_Compile.setup *}


text {* Experimental code *}

definition pred_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a Predicate.pred \<Rightarrow> 'b Predicate.pred" where
  "pred_map f P = Predicate.bind P (Predicate.single o f)"

ML {*
structure Predicate =
struct

open Predicate;

val pred_ref = ref (NONE : (unit -> term Predicate.pred) option);

fun eval_pred thy t =
  Code_ML.eval NONE ("Predicate.pred_ref", pred_ref) @{code pred_map} thy (HOLogic.mk_term_of (fastype_of t) t) [];

fun eval_pred_elems thy t T length =
  t |> eval_pred thy |> yieldn length |> fst |> HOLogic.mk_list T;

fun analyze_compr thy t =
  let
    val split = case t of (Const (@{const_name Collect}, _) $ t') => t'
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term_global thy t);
    val (body, Ts, fp) = HOLogic.strip_split split;
    val (t_pred, args) = strip_comb body;
    val pred = case t_pred of Const (pred, _) => pred
      | _ => error ("Not a constant: " ^ Syntax.string_of_term_global thy t_pred);
    val mode = map is_Bound args; (*FIXME what about higher-order modes?*)
    val args' = filter_out is_Bound args;
    val T = HOLogic.mk_tupleT fp Ts;
    val mk = HOLogic.mk_tuple' fp T;
  in (((pred, mode), args), (mk, T)) end;

end;
*}

end