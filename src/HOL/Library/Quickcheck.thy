(* Author: Florian Haftmann, TU Muenchen *)

header {* A simple counterexample generator *}

theory Quickcheck
imports Random Code_Eval Map
begin

subsection {* The @{text random} class *}

class random = typerep +
  fixes random :: "index \<Rightarrow> seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> seed"

text {* Type @{typ "'a itself"} *}

instantiation itself :: ("{type, typerep}") random
begin

definition
  "random _ = return (TYPE('a), \<lambda>u. Code_Eval.Const (STR ''TYPE'') TYPEREP('a))"

instance ..

end


subsection {* Quickcheck generator *}

ML {*
structure StateMonad =
struct

fun liftT T sT = sT --> HOLogic.mk_prodT (T, sT);
fun liftT' sT = sT --> sT;

fun return T sT x = Const (@{const_name Pair}, T --> liftT T sT) $ x;

fun scomp T1 T2 sT f g = Const (@{const_name scomp},
  liftT T1 sT --> (T1 --> liftT T2 sT) --> liftT T2 sT) $ f $ g;

end;

structure Quickcheck =
struct

open Quickcheck;

val eval_ref : (unit -> int -> int * int -> term list option * (int * int)) option ref = ref NONE;

fun mk_generator_expr thy prop tys =
  let
    val bound_max = length tys - 1;
    val bounds = map_index (fn (i, ty) =>
      (2 * (bound_max - i) + 1, 2 * (bound_max - i), 2 * i, ty)) tys;
    val result = list_comb (prop, map (fn (i, _, _, _) => Bound i) bounds);
    val terms = HOLogic.mk_list @{typ term} (map (fn (_, i, _, _) => Bound i $ @{term "()"}) bounds);
    val check = @{term "If \<Colon> bool \<Rightarrow> term list option \<Rightarrow> term list option \<Rightarrow> term list option"}
      $ result $ @{term "None \<Colon> term list option"} $ (@{term "Some \<Colon> term list \<Rightarrow> term list option "} $ terms);
    val return = @{term "Pair \<Colon> term list option \<Rightarrow> seed \<Rightarrow> term list option \<times> seed"};
    fun mk_termtyp ty = HOLogic.mk_prodT (ty, @{typ "unit \<Rightarrow> term"});
    fun mk_split ty = Sign.mk_const thy
      (@{const_name split}, [ty, @{typ "unit \<Rightarrow> term"}, StateMonad.liftT @{typ "term list option"} @{typ seed}]);
    fun mk_scomp_split ty t t' =
      StateMonad.scomp (mk_termtyp ty) @{typ "term list option"} @{typ seed} t (*FIXME*)
        (mk_split ty $ Abs ("", ty, Abs ("", @{typ "unit \<Rightarrow> term"}, t')));
    fun mk_bindclause (_, _, i, ty) = mk_scomp_split ty
      (Sign.mk_const thy (@{const_name random}, [ty]) $ Bound i)
    val t = fold_rev mk_bindclause bounds (return $ check);
  in Abs ("n", @{typ index}, t) end;

fun compile_generator_expr thy t =
  let
    val tys = (map snd o fst o strip_abs) t;
    val t' = mk_generator_expr thy t tys;
    val f = Code_ML.eval_term ("Quickcheck.eval_ref", eval_ref) thy t' [];
  in f #> Random_Engine.run #> (Option.map o map) (Code.postprocess_term thy) end;

end
*}

setup {*
  Quickcheck.add_generator ("code", Quickcheck.compile_generator_expr o ProofContext.theory_of)
*}

end
