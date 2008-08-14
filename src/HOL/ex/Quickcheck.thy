(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple counterexample generator *}

theory Quickcheck
imports Random Eval
begin

subsection {* The @{text random} class *}

class random = rtype +
  fixes random :: "index \<Rightarrow> seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> seed"

text {* Type @{typ "'a itself"} *}

instantiation itself :: ("{type, rtype}") random
begin

definition
  "random _ = return (TYPE('a), \<lambda>u. Eval.Const (STR ''TYPE'') RTYPE('a))"

instance ..

end

text {* Datatypes *}

lemma random'_if:
  fixes random' :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> seed"
  assumes "random' 0 j = undefined"
    and "\<And>i. random' (Suc_index i) j = rhs2 i"
  shows "random' i j s = (if i = 0 then undefined else rhs2 (i - 1) s)"
  by (cases i rule: index.exhaust) (insert assms, simp_all add: undefined_fun)

setup {*
let
  exception REC of string;
  fun mk_collapse thy ty = Sign.mk_const thy
    (@{const_name collapse}, [@{typ seed}, ty]);
  fun term_ty ty = HOLogic.mk_prodT (ty, @{typ "unit \<Rightarrow> term"});
  fun mk_split thy ty ty' = Sign.mk_const thy
    (@{const_name split}, [ty, @{typ "unit \<Rightarrow> term"}, StateMonad.liftT (term_ty ty') @{typ seed}]);
  fun mk_scomp_split thy ty ty' t t' =
    StateMonad.scomp (term_ty ty) (term_ty ty') @{typ seed} t
      (mk_split thy ty ty' $ Abs ("", ty, Abs ("", @{typ "unit \<Rightarrow> term"}, t')))
  fun mk_cons thy this_ty (c, args) =
    let
      val tys = map (fst o fst) args;
      val c_ty = tys ---> this_ty;
      val c = Const (c, tys ---> this_ty);
      val t_indices = map (curry ( op * ) 2) (length tys - 1 downto 0);
      val c_indices = map (curry ( op + ) 1) t_indices;
      val c_t = list_comb (c, map Bound c_indices);
      val t_t = Abs ("", @{typ unit}, Eval.mk_term Free RType.rtype
        (list_comb (c, map (fn k => Bound (k + 1)) t_indices))
        |> map_aterms (fn t as Bound _ => t $ @{term "()"} | t => t));
      val return = StateMonad.return (term_ty this_ty) @{typ seed}
        (HOLogic.mk_prod (c_t, t_t));
      val t = fold_rev (fn ((ty, _), random) =>
        mk_scomp_split thy ty this_ty random)
          args return;
      val is_rec = exists (snd o fst) args;
    in (is_rec, StateMonad.run (term_ty this_ty) @{typ seed} t) end;
  fun mk_conss thy ty [] = NONE
    | mk_conss thy ty [(_, t)] = SOME t
    | mk_conss thy ty ts = SOME (mk_collapse thy (term_ty ty) $
          (Sign.mk_const thy (@{const_name select}, [StateMonad.liftT (term_ty ty) @{typ seed}]) $
            HOLogic.mk_list (StateMonad.liftT (term_ty ty) @{typ seed}) (map snd ts)));
  fun mk_clauses thy ty (tyco, (ts_rec, ts_atom)) = 
    let
      val SOME t_atom = mk_conss thy ty ts_atom;
    in case mk_conss thy ty ts_rec
     of SOME t_rec => mk_collapse thy (term_ty ty) $
          (Sign.mk_const thy (@{const_name select_default}, [StateMonad.liftT (term_ty ty) @{typ seed}]) $
             @{term "i\<Colon>index"} $ t_rec $ t_atom)
      | NONE => t_atom
    end;
  fun mk_random_eqs thy vs tycos =
    let
      val this_ty = Type (hd tycos, map TFree vs);
      val this_ty' = StateMonad.liftT (term_ty this_ty) @{typ seed};
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
        |> (map o apsnd o map) (mk_cons thy this_ty) 
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
          val ((this_ty, random'), eqs') = singleton (mk_random_eqs thy vs) tyco;
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
              |> LocalTheory.theory (PureThy.add_thm ((fst (dest_Free random') ^ "_code", thm), [Thm.kind_internal])
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
     (b, _) \<leftarrow> random n;
     (m, t) \<leftarrow> random n;
     return (if b then (int m, \<lambda>u. Eval.App (Eval.Const (STR ''Int.int'') RTYPE(nat \<Rightarrow> int)) (t ()))
       else (- int m, \<lambda>u. Eval.App (Eval.Const (STR ''HOL.uminus_class.uminus'') RTYPE(int \<Rightarrow> int))
         (Eval.App (Eval.Const (STR ''Int.int'') RTYPE(nat \<Rightarrow> int)) (t ()))))
   done)"

instance ..

end

text {* Type @{typ "'a \<Rightarrow> 'b"} *}

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
    val state = ref (seed', [], Const (@{const_name arbitrary}, T1 --> T2));
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
  random_fun_aux :: "rtype \<Rightarrow> rtype \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
    \<Rightarrow> (seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> seed) \<Rightarrow> (seed \<Rightarrow> seed \<times> seed)
    \<Rightarrow> seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> seed"

code_const random_fun_aux (SML "Random'_Engine.random'_fun")

instantiation "fun" :: ("{eq, term_of}", "{type, random}") random
begin

definition random_fun :: "index \<Rightarrow> seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> seed" where
  "random n = random_fun_aux RTYPE('a) RTYPE('b) (op =) Eval.term_of (random n) split_seed"

instance ..

end

code_reserved SML Random_Engine


subsection {* Quickcheck generator *}

ML {*
structure Quickcheck =
struct

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

fun compile_generator_expr thy prop tys =
  let
    val f = CodeTarget.eval_term ("Quickcheck.eval_ref", eval_ref) thy
      (mk_generator_expr thy prop tys) [];
  in f #> Random_Engine.run #> (Option.map o map) (Code.postprocess_term thy) end;

fun VALUE prop tys thy =
  let
    val t = mk_generator_expr thy prop tys;
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

(*export_code "random :: index \<Rightarrow> seed \<Rightarrow> ((_ \<Rightarrow> _) \<times> (unit \<Rightarrow> term)) \<times> seed"
  in SML file -*)

(*setup {* Quickcheck.VALUE
  @{term "\<lambda>f k. int (f k) = k"} [@{typ "int \<Rightarrow> nat"}, @{typ int}] *}

export_code VALUE in SML module_name QuickcheckExample file "~~/../../gen_code/quickcheck.ML"
use "~~/../../gen_code/quickcheck.ML"
ML {* Random_Engine.run (QuickcheckExample.range 1) *}*)

(*definition "FOO = (True, Suc 0)"

code_module (test) QuickcheckExample
  file "~~/../../gen_code/quickcheck'.ML"
  contains FOO*)

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(n::nat) (m::nat) (q::nat). n = m + q + 1"} [@{typ nat}, @{typ nat}, @{typ nat}] *}

ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 25 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(n::int) (m::int) (q::int). n = m + q + 1"} [@{typ int}, @{typ int}, @{typ int}] *}

ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 25 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 3 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(xs\<Colon>int list) ys. rev (xs @ ys) = rev xs @ rev ys"}
  [@{typ "int list"}, @{typ "int list"}] *}

ML {* f 15 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 25 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 8 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 8 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 8 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 88 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

ML {* f 1 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 2 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 3 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 5 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 6 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>(s \<Colon> string). s \<noteq> rev s"} [@{typ string}] *}

ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 4 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 10 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 8 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 8 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

ML {* val f = Quickcheck.compile_generator_expr @{theory}
  @{term "\<lambda>f k. int (f k) = k"} [@{typ "int \<Rightarrow> nat"}, @{typ int}] *}

ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}
ML {* f 20 |> (Option.map o map) (Syntax.string_of_term @{context}) *}

end
