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

print_classes

instantiation itself :: (type) random
begin

definition
  "random _ = return TYPE('a)"

instance ..

end

lemma random_aux_if:
  fixes random' :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
  assumes "random' 0 j = undefined"
    and "\<And>i. random' (Suc_index i) j = rhs2 i"
  shows "random' i j s = (if i = 0 then undefined else rhs2 (i - 1) s)"
  by (cases i rule: index.exhaust) (insert assms, simp_all add: undefined_fun)

setup {*
let
  exception REC;
  fun random_inst tyco thy =
    let
      val { descr, index, ... } = DatatypePackage.the_datatype thy tyco;
      val _ = if length descr > 1 then raise REC else ();
      val (raw_vs, _) = DatatypePackage.the_datatype_spec thy tyco;
      val vs = (map o apsnd)
        (curry (Sorts.inter_sort (Sign.classes_of thy)) @{sort random}) raw_vs;
      val ty = Type (tyco, map TFree vs);
      val typ_of = DatatypeAux.typ_of_dtyp descr vs;
      val SOME (_, _, constrs) = AList.lookup (op =) descr index;
      val randomN = NameSpace.base @{const_name random};
      val random_aux_name = randomN ^ "_" ^ Class.type_name tyco ^ "'";
      fun lift_ty ty = StateMonad.liftT ty @{typ seed};
      val ty_aux = @{typ index} --> @{typ index} --> lift_ty ty;
      fun random ty =
        Const (@{const_name random}, @{typ index} --> lift_ty ty);
      val random_aux = Free (random_aux_name, ty_aux);
      fun add_cons_arg dty (is_rec, t) =
        let
          val ty' = typ_of dty;
          val rec_call = case try DatatypeAux.dest_DtRec dty
           of SOME index' => index = index'
            | NONE => false
          val random' = if rec_call
            then random_aux $ @{term "i\<Colon>index"} $ @{term "j\<Colon>index"}
            else random ty' $ @{term "j\<Colon>index"}
          val is_rec' = is_rec orelse DatatypeAux.is_rec_type dty;
          val t' = StateMonad.mbind ty' ty @{typ seed} random' (Abs ("", ty', t))
        in (is_rec', t') end;
      fun mk_cons_t (c, dtys) =
        let
          val ty' = map typ_of dtys ---> ty;
          val t = StateMonad.return ty @{typ seed} (list_comb (Const (c, ty'),
            map Bound (length dtys - 1 downto 0)));
          val (is_rec, t') = fold_rev add_cons_arg dtys (false, t);
        in (is_rec, StateMonad.run ty @{typ seed} t') end;
      fun check_empty [] = NONE
        | check_empty xs = SOME xs;
      fun bundle_cons_ts cons_ts =
        let
          val ts = map snd cons_ts;
          val t = HOLogic.mk_list (lift_ty ty) ts;
          val t' = Const (@{const_name select}, HOLogic.listT (lift_ty ty) --> lift_ty (lift_ty ty)) $ t;
          val t'' = Const (@{const_name collapse}, lift_ty (lift_ty ty) --> lift_ty ty) $ t';
        in t'' end;
      fun bundle_conss (some_rec_t, nonrec_t) =
        let
          val t = case some_rec_t
           of SOME rec_t => Const (@{const_name collapse}, lift_ty (lift_ty ty) --> lift_ty ty)
               $ (Const (@{const_name select_default},
                   @{typ index} --> lift_ty ty --> lift_ty ty --> lift_ty (lift_ty ty))
                  $ @{term "i\<Colon>index"} $ rec_t $ nonrec_t)
            | NONE => nonrec_t
        in t end;
      val random_rhs = constrs
        |> map mk_cons_t 
        |> List.partition fst
        |> apfst (Option.map bundle_cons_ts o check_empty)
        |> apsnd bundle_cons_ts
        |> bundle_conss;
      val random_aux_undef = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
        (random_aux $ @{term "0\<Colon>index"} $ @{term "j\<Colon>index"}, Const (@{const_name undefined}, lift_ty ty))
      val random_aux_eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
        (random_aux $ @{term "Suc_index i"} $ @{term "j\<Colon>index"}, random_rhs);
      val random_eq = (HOLogic.mk_Trueprop o HOLogic.mk_eq) (Const (@{const_name random},
        @{typ index} --> lift_ty ty) $ @{term "i\<Colon>index"},
          random_aux $ @{term "i\<Colon>index"} $ @{term "i\<Colon>index"});
      val del_func = Attrib.internal (fn _ => Thm.declaration_attribute
        (fn thm => Context.mapping (Code.del_func thm) I));
      fun add_code simps lthy =
        let
          val thy = ProofContext.theory_of lthy;
          val thm = @{thm random_aux_if}
            |> Drule.instantiate' [SOME (Thm.ctyp_of thy ty)] [SOME (Thm.cterm_of thy random_aux)]
            |> (fn thm => thm OF simps)
            |> singleton (ProofContext.export lthy (ProofContext.init thy))
        in
          lthy
          |> LocalTheory.theory (PureThy.note Thm.internalK (random_aux_name ^ "_code", thm)
               #-> Code.add_func)
        end;
    in
      thy
      |> TheoryTarget.instantiation ([tyco], vs, @{sort random})
      |> PrimrecPackage.add_primrec [(random_aux_name, SOME ty_aux, NoSyn)]
           [(("", [del_func]), random_aux_undef), (("", [del_func]), random_aux_eq)]
      |-> add_code
      |> `(fn lthy => Syntax.check_term lthy random_eq)
      |-> (fn eq => Specification.definition (NONE, (("", []), eq)))
      |> snd
      |> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
      |> LocalTheory.exit
      |> ProofContext.theory_of
    end;
  fun add_random_inst [tyco] = (fn thy => random_inst tyco thy handle REC =>
        (warning ("Will not generated random elements for mutual recursive type " ^ quote tyco); thy))
    | add_random_inst tycos = tap (fn _ => warning
        ("Will not generated random elements for mutual recursive type(s) " ^ commas (map quote tycos)));
in DatatypePackage.interpretation add_random_inst end
*}

instantiation int :: random
begin

definition
  "random n = (do
     (b, m) \<leftarrow> random n;
     return (if b then int m else - int m)
   done)"

instance ..

end

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
  by (rule random_aux_if random_set'.simps)+

definition
  "random i = random_set' i i"

instance ..

end

code_reserved SML Quickcheck


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

subsection {* Incremental function generator *}

ML {*
structure Quickcheck =
struct

open Quickcheck;

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

code_const random_fun_aux (SML "Quickcheck.random'_fun")

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
