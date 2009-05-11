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
  "random _ = Pair (TYPE('a), \<lambda>u. Code_Eval.Const (STR ''TYPE'') TYPEREP('a))"

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

val target = "Quickcheck";

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
    val f = Code_ML.eval (SOME target) ("Quickcheck.eval_ref", eval_ref)
      (fn proc => fn g => fn s => g s #>> (Option.map o map) proc) thy t' [];
  in f #> Random_Engine.run end;

end
*}

setup {*
  Code_Target.extend_target (Quickcheck.target, (Code_ML.target_Eval, K I))
  #> Quickcheck.add_generator ("code", Quickcheck.compile_generator_expr o ProofContext.theory_of)
*}


subsection {* Type @{typ "'a \<Rightarrow> 'b"} *}

ML {*
structure Random_Engine =
struct

open Random_Engine;

fun random_fun (T1 : typ) (T2 : typ) (eq : 'a -> 'a -> bool) (term_of : 'a -> term)
    (random : Random_Engine.seed -> ('b * (unit -> term)) * Random_Engine.seed)
    (random_split : Random_Engine.seed -> Random_Engine.seed * Random_Engine.seed)
    (seed : Random_Engine.seed) =
  let
    val (seed', seed'') = random_split seed;
    val state = ref (seed', [], Const (@{const_name undefined}, T1 --> T2));
    val fun_upd = Const (@{const_name fun_upd},
      (T1 --> T2) --> T1 --> T2 --> T1 --> T2);
    fun random_fun' x =
      let
        val (seed, fun_map, f_t) = ! state;
      in case AList.lookup (uncurry eq) fun_map x
       of SOME y => y
        | NONE => let
              val t1 = term_of x;
              val ((y, t2), seed') = random seed;
              val fun_map' = (x, y) :: fun_map;
              val f_t' = fun_upd $ f_t $ t1 $ t2 ();
              val _ = state := (seed', fun_map', f_t');
            in y end
      end;
    fun term_fun' () = #3 (! state);
  in ((random_fun', term_fun'), seed'') end;

end
*}

axiomatization
  random_fun_aux :: "typerep \<Rightarrow> typerep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
    \<Rightarrow> (seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> seed) \<Rightarrow> (seed \<Rightarrow> seed \<times> seed)
    \<Rightarrow> seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> seed"

code_const random_fun_aux (Quickcheck "Random'_Engine.random'_fun")
  -- {* With enough criminal energy this can be abused to derive @{prop False};
  for this reason we use a distinguished target @{text Quickcheck}
  not spoiling the regular trusted code generation *}

instantiation "fun" :: ("{eq, term_of}", "{type, random}") random
begin

definition random_fun :: "index \<Rightarrow> seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> seed" where
  "random n = random_fun_aux TYPEREP('a) TYPEREP('b) (op =) Code_Eval.term_of (random n) split_seed"

instance ..

end

code_reserved Quickcheck Random_Engine

end
