(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple counterexample generator *}

theory Quickcheck
imports Random Eval
begin

subsection {* The @{text random} class *}

class random = type +
  fixes random :: "index \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"

text {* Type @{typ "'a itself"} *}

instantiation itself :: (type) random
begin

definition
  "random _ = return TYPE('a)"

instance ..

end

text {* Datatypes *}

lemma random'_if:
  fixes random' :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
  assumes "random' 0 j = undefined"
    and "\<And>i. random' (Suc_index i) j = rhs2 i"
  shows "random' i j s = (if i = 0 then undefined else rhs2 (i - 1) s)"
  by (cases i rule: index.exhaust) (insert assms, simp_all add: undefined_fun)

setup {*
let
  exception REC of string;
  fun mk_collapse thy ty = Sign.mk_const thy
    (@{const_name collapse}, [@{typ seed}, ty]);
  fun mk_cons this_ty (c, args) =
    let
      val tys = map (fst o fst) args;
      val return = StateMonad.return this_ty @{typ seed}
        (list_comb (Const (c, tys ---> this_ty),
           map Bound (length tys - 1 downto 0)));
      val t = fold_rev (fn ((ty, _), random) => fn t =>
        StateMonad.mbind ty this_ty @{typ seed} random (Abs ("", ty, t)))
          args return;
      val is_rec = exists (snd o fst) args;
    in (is_rec, StateMonad.run this_ty @{typ seed} t) end;
  fun mk_conss thy ty [] = NONE
    | mk_conss thy ty [(_, t)] = SOME t
    | mk_conss thy ty ts = SOME (mk_collapse thy ty $
          (Sign.mk_const thy (@{const_name select}, [StateMonad.liftT ty @{typ seed}]) $
            HOLogic.mk_list (StateMonad.liftT ty @{typ seed}) (map snd ts)));
  fun mk_clauses thy ty (tyco, (ts_rec, ts_atom)) = 
    let
      val SOME t_atom = mk_conss thy ty ts_atom;
    in case mk_conss thy ty ts_rec
     of SOME t_rec => mk_collapse thy ty $
          (Sign.mk_const thy (@{const_name select_default}, [StateMonad.liftT ty @{typ seed}]) $
             @{term "i\<Colon>index"} $ t_rec $ t_atom)
      | NONE => t_atom
    end;
  fun mk_random_eqs thy tycos =
    let
      val (raw_vs, _) = DatatypePackage.the_datatype_spec thy (hd tycos);
      val vs = (map o apsnd)
        (curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort random}) raw_vs;
      val this_ty = Type (hd tycos, map TFree vs);
      val this_ty' = StateMonad.liftT this_ty @{typ seed};
      val random_name = NameSpace.base @{const_name random};
      val random'_name = random_name ^ "_" ^ Class.type_name (hd tycos) ^ "'";
      fun random ty = Sign.mk_const thy (@{const_name random}, [ty]);
      val random' = Free (random'_name,
        @{typ index} --> @{typ index} --> this_ty');
      fun atom ty = ((ty, false), random ty $ @{term "j\<Colon>index"});
      fun dtyp tyco = ((this_ty, true), random' $ @{term "i\<Colon>index"} $ @{term "j\<Colon>index"});
      fun rtyp tyco tys = raise REC
        ("Will not generate random elements for mutual recursive type " ^ quote (hd tycos));
      val rhss = DatatypePackage.construction_interpretation thy
            { atom = atom, dtyp = dtyp, rtyp = rtyp } vs tycos
        |> (map o apsnd o map) (mk_cons this_ty) 
        |> (map o apsnd) (List.partition fst)
        |> map (mk_clauses thy this_ty)
      val eqss = map ((apsnd o map) (HOLogic.mk_Trueprop o HOLogic.mk_eq) o (fn rhs => ((this_ty, random'), [
          (random' $ @{term "0\<Colon>index"} $ @{term "j\<Colon>index"}, Const (@{const_name undefined}, this_ty')),
          (random' $ @{term "Suc_index i"} $ @{term "j\<Colon>index"}, rhs)
        ]))) rhss;
    in eqss end;
  fun random_inst [tyco] thy =
        let
          val (raw_vs, _) = DatatypePackage.the_datatype_spec thy tyco;
          val vs = (map o apsnd)
            (curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort random}) raw_vs;
          val { descr, index, ... } = DatatypePackage.the_datatype thy tyco;
          val ((this_ty, random'), eqs') = singleton (mk_random_eqs thy) tyco;
          val eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
            (Sign.mk_const thy (@{const_name random}, [this_ty]) $ @{term "i\<Colon>index"},
               random' $ @{term "i\<Colon>index"} $ @{term "i\<Colon>index"})
          val del_func = Attrib.internal (fn _ => Thm.declaration_attribute
            (fn thm => Context.mapping (Code.del_func thm) I));
          fun add_code simps lthy =
            let
              val thy = ProofContext.theory_of lthy;
              val thm = @{thm random'_if}
                |> Drule.instantiate' [SOME (Thm.ctyp_of thy this_ty)] [SOME (Thm.cterm_of thy random')]
                |> (fn thm => thm OF simps)
                |> singleton (ProofContext.export lthy (ProofContext.init thy))
            in
              lthy
              |> LocalTheory.theory (PureThy.note Thm.internalK (fst (dest_Free random') ^ "_code", thm)
                   #-> Code.add_func)
            end;
        in
          thy
          |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
          |> PrimrecPackage.add_primrec
               [(fst (dest_Free random'), SOME (snd (dest_Free random')), NoSyn)]
                 (map (fn eq => (("", [del_func]), eq)) eqs')
          |-> add_code
          |> `(fn lthy => Syntax.check_term lthy eq)
          |-> (fn eq => Specification.definition (NONE, (("", []), eq)))
          |> snd
          |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
          |> LocalTheory.exit
          |> ProofContext.theory_of
        end
    | random_inst tycos thy = raise REC
        ("Will not generate random elements for mutual recursive type(s) " ^ commas (map quote tycos));
  fun add_random_inst tycos thy = random_inst tycos thy
     handle REC msg => (warning msg; thy);
in DatatypePackage.interpretation add_random_inst end
*}

text {* Type @{typ int} *}

instantiation int :: random
begin

definition
  "random n = (do
     (b, m) \<leftarrow> random n;
     return (if b then int m else - int m)
   done)"

instance ..

end

text {* Type @{typ "'a set"} *}

instantiation set :: (random) random
begin

primrec random_set' :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> 'a set \<times> seed" where
  "random_set' 0 j = undefined"
  | "random_set' (Suc_index i) j = collapse (select_default i
       (do x \<leftarrow> random i; xs \<leftarrow> random_set' i j; return (insert x xs) done)
       (return {}))"

lemma random_set'_code [code func]:
  "random_set' i j s = (if i = 0 then undefined else collapse (select_default (i - 1)
       (do x \<leftarrow> random (i - 1); xs \<leftarrow> random_set' (i - 1) j; return (insert x xs) done)
       (return {})) s)"
  by (rule random'_if random_set'.simps)+

definition
  "random i = random_set' i i"

instance ..

end

text {* Type @{typ "'a \<Rightarrow> 'b"} *}

ML {*
structure Random_Engine =
struct

open Random_Engine;

fun random_fun (eq : 'a -> 'a -> bool)
    (random : Random_Engine.seed -> 'b * Random_Engine.seed)
    (random_split : Random_Engine.seed -> Random_Engine.seed * Random_Engine.seed)
    (seed : Random_Engine.seed) =
  let
    val (seed', seed'') = random_split seed;
    val state = ref (seed', []);
    fun random_fun' x =
      let
        val (seed, fun_map) = ! state;
      in case AList.lookup (uncurry eq) fun_map x
       of SOME y => y
        | NONE => let
              val (y, seed') = random seed;
              val _ = state := (seed', (x, y) :: fun_map);
            in y end
      end;
  in (random_fun', seed'') end;

end
*}

axiomatization
  random_fun_aux :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (seed \<Rightarrow> 'b \<times> seed)
    \<Rightarrow> (seed \<Rightarrow> seed \<times> seed) \<Rightarrow> seed \<Rightarrow> ('a \<Rightarrow> 'b) \<times> seed"

code_const random_fun_aux (SML "Random'_Engine.random'_fun")

instantiation "fun" :: (term_of, term_of) term_of
begin

instance ..

end

code_const "Eval.term_of :: ('a\<Colon>term_of \<Rightarrow> 'b\<Colon>term_of) \<Rightarrow> _"
  (SML "(fn '_ => Const (\"arbitrary\", dummyT))")

instantiation "fun" :: (eq, "{type, random}") random
begin

definition
  "random n = random_fun_aux (op =) (random n) split_seed"

instance ..

end

code_reserved SML Random_Engine


subsection {* Quickcheck generator *}

ML {*
structure Quickcheck =
struct

val eval_ref : (unit -> int -> int * int -> term list option * (int * int)) option ref = ref NONE;

fun mk_generator_expr prop tys =
  let
    val bounds = map_index (fn (i, ty) => (i, ty)) tys;
    val result = list_comb (prop, map (fn (i, _) => Bound (length tys - i - 1)) bounds);
    val terms = map (fn (i, ty) => Const (@{const_name Eval.term_of}, ty --> @{typ term}) $ Bound (length tys - i - 1)) bounds;
    val check = @{term "If \<Colon> bool \<Rightarrow> term list option \<Rightarrow> term list option \<Rightarrow> term list option"}
      $ result $ @{term "None \<Colon> term list option"} $ (@{term "Some \<Colon> term list \<Rightarrow> term list option "} $ HOLogic.mk_list @{typ term} terms);
    val return = @{term "Pair \<Colon> term list option \<Rightarrow> seed \<Rightarrow> term list option \<times> seed"};
    fun mk_bindtyp ty = @{typ seed} --> HOLogic.mk_prodT (ty, @{typ seed});
    fun mk_bindclause (i, ty) t = Const (@{const_name mbind}, mk_bindtyp ty
      --> (ty --> mk_bindtyp @{typ "term list option"}) --> mk_bindtyp @{typ "term list option"})
      $ (Const (@{const_name random}, @{typ index} --> mk_bindtyp ty)
        $ Bound i) $ Abs ("a", ty, t);
    val t = fold_rev mk_bindclause bounds (return $ check);
  in Abs ("n", @{typ index}, t) end;

fun compile_generator_expr thy prop tys =
  let
    val f = CodePackage.eval_term ("Quickcheck.eval_ref", eval_ref) thy
      (mk_generator_expr prop tys) [];
  in f #> Random_Engine.run #> (Option.map o map) (Code.postprocess_term thy) end;

fun VALUE prop tys thy =
  let
    val t = mk_generator_expr prop tys;
    val eq = Logic.mk_equals (Free ("VALUE", fastype_of t), t)
  in
    thy
    |> TheoryTarget.init NONE
    |> Specification.definition (NONE, (("", []), eq))
    |> snd
    |> LocalTheory.exit
    |> ProofContext.theory_of
  end;

end
*}


subsection {* Examples *}

ML {* Quickcheck.mk_generator_expr
  @{term "\<lambda>(n::nat) (m::nat) (q::nat). n = m + q + 1"} [@{typ nat}, @{typ nat}, @{typ nat}]
|> Sign.string_of_term @{theory} *}

(*setup {* Quickcheck.VALUE @{term "\<lambda>(n::nat) (m::nat) (q::nat). n = m + q + 1"} [@{typ nat}, @{typ nat}, @{typ nat}] *}
export_code VALUE in SML module_name QuickcheckExample file "~~/../../gen_code/quickcheck.ML"
use "~~/../../gen_code/quickcheck.ML"
ML {* Random_Engine.run (QuickcheckExample.range 1) *}*)

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(n::nat) (m::nat) (q::nat). n = m + q + 1"} [@{typ nat}, @{typ nat}, @{typ nat}] *}

ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 25 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(n::int) (m::int) (q::int). n = m + q + 1"} [@{typ int}, @{typ int}, @{typ int}] *}

(*definition "FOO = (True, Suc 0)"

code_module (test) QuickcheckExample
  file "~~/../../gen_code/quickcheck'.ML"
  contains FOO*)

ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 25 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 3 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(xs\<Colon>int list) ys. rev (xs @ ys) = rev xs @ rev ys"}
  [@{typ "int list"}, @{typ "int list"}] *}

ML {* f 15 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 25 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 8 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 8 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 8 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 88 |> (Option.map o map) (Sign.string_of_term @{theory}) *}


ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>f k. int (f k) = k"} [@{typ "int \<Rightarrow> nat"}, @{typ int}] *}

ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 20 |> (Option.map o map) (Sign.string_of_term @{theory}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(A \<Colon> nat set) B. card (A \<union> B) = card A + card B"} [@{typ "nat set"}, @{typ "nat set"}] *}

ML {* f 1 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 2 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 3 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 5 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 6 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(s \<Colon> string). s \<noteq> rev s"} [@{typ string}] *}

ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 4 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 10 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 8 |> (Option.map o map) (Sign.string_of_term @{theory}) *}
ML {* f 8 |> (Option.map o map) (Sign.string_of_term @{theory}) *}

end
