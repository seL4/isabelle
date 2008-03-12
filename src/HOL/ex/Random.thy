(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* A simple term generator *}

theory Random
imports State_Monad Code_Index List Eval
begin

subsection {* The random engine *}

types seed = "index \<times> index"

definition
  "next" :: "seed \<Rightarrow> index \<times> seed"
where
  "next s = (let
     (v, w) = s;
     k = v div 53668;
     v' = 40014 * (v - k * 53668) - k * 12211;
     v'' = (if v' < 0 then v' + 2147483563 else v');
     l = w div 52774;
     w' = 40692 * (w - l * 52774) - l * 3791;
     w'' = (if w' < 0 then w' + 2147483399 else w');
     z = v'' - w'';
     z' = (if z < 1 then z + 2147483562 else z)
   in (z',  (v'', w'')))"

definition
  split_seed :: "seed \<Rightarrow> seed \<times> seed"
where
  "split_seed s = (let
     (v, w) = s;
     (v', w') = snd (next s);
     v'' = (if v = 2147483562 then 1 else v + 1);
     s'' = (v'', w');
     w'' = (if w = 2147483398 then 1 else w + 1);
     s''' = (v', w'')
   in (s'', s'''))"

text {* Base selectors *}

primrec
  pick :: "(index \<times> 'a) list \<Rightarrow> index \<Rightarrow> 'a"
where
  "pick (x#xs) n = (if n < fst x then snd x else pick xs (n - fst x))"

function
  iLogBase :: "index \<Rightarrow> index \<Rightarrow> index"
where
  "iLogBase b i = (if b \<le> 1 \<or> i < b then 1 else 1 + iLogBase b (i div b))"
by pat_completeness auto
termination
  by (relation "measure (nat_of_index o snd)")
    (auto simp add: index)

function
  range_aux :: "index \<Rightarrow> index \<Rightarrow> seed \<Rightarrow> index \<times> seed"
where
  "range_aux k l s = (if k = 0 then (l, s) else
    let (v, s') = next s
  in range_aux (k - 1) (v + l * 2147483561) s')"
by pat_completeness auto
termination
  by (relation "measure (nat_of_index o fst)")
    (auto simp add: index)

definition
  range :: "index \<Rightarrow> seed \<Rightarrow> index \<times> seed"
where
  "range k s = (let
    b = 2147483561;
    n = iLogBase b k;
    (v, s') = range_aux n 1 s
  in (v mod k, s'))"

definition
  select :: "'a list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
where
  [simp]: "select xs s = (let
    (k, s') = range (index_of_nat (length xs)) s
  in (nth xs (nat_of_index k), s'))"

definition
  select_weight :: "(index \<times> 'a) list \<Rightarrow> seed \<Rightarrow> 'a \<times> seed"
where
  [simp]: "select_weight xs s = (let
    (k, s') = range (foldr (op + \<circ> fst) xs 0) s
  in (pick xs k, s'))"

(*lemma
  "select (x#xs) s = select_weight (map (Pair 1) (x#xs)) s"
proof (induct xs)
  case Nil show ?case apply (auto simp add: Let_def split_def) 
next
  have map_fst_Pair: "!!xs y. map fst (map (Pair y) xs) = replicate (length xs) y"
  proof -
    fix xs
    fix y
    show "map fst (map (Pair y) xs) = replicate (length xs) y"
      by (induct xs) simp_all
  qed
  have pick_nth: "!!xs n. n < length xs \<Longrightarrow> pick (map (Pair 1) xs) n = nth xs n"
  proof -
    fix xs
    fix n
    assume "n < length xs"
    then show "pick (map (Pair 1) xs) n = nth xs n"
    proof (induct xs arbitrary: n)
      case Nil then show ?case by simp
    next
      case (Cons x xs) show ?case
      proof (cases n)
        case 0 then show ?thesis by simp
      next
        case (Suc _)
    from Cons have "n < length (x # xs)" by auto
        then have "n < Suc (length xs)" by simp
        with Suc have "n - 1 < Suc (length xs) - 1" by auto
        with Cons have "pick (map (Pair (1\<Colon>nat)) xs) (n - 1) = xs ! (n - 1)" by auto
        with Suc show ?thesis by auto
      qed
    qed
  qed
  have sum_length: "!!xs. foldl (op +) 0 (map fst (map (Pair 1) xs)) = length xs"
  proof -
    have replicate_append:
      "!!x xs y. replicate (length (x # xs)) y = replicate (length xs) y @ [y]"
      by (simp add: replicate_app_Cons_same)
    fix xs
    show "foldl (op +) 0 (map fst (map (Pair 1) xs)) = length xs"
    unfolding map_fst_Pair proof (induct xs)
      case Nil show ?case by simp
    next
      case (Cons x xs) then show ?case unfolding replicate_append by simp
    qed
  qed
  have pick_nth_random:
    "!!x xs s. pick (map (Pair 1) (x#xs)) (fst (random (length (x#xs)) s)) = nth (x#xs) (fst (random (length (x#xs)) s))"
  proof -
    fix s
    fix x
    fix xs
    have bound: "fst (random (length (x#xs)) s) < length (x#xs)" by (rule random_bound) simp
    from pick_nth [OF bound] show
      "pick (map (Pair 1) (x#xs)) (fst (random (length (x#xs)) s)) = nth (x#xs) (fst (random (length (x#xs)) s))" .
  qed
  have pick_nth_random_do:
    "!!x xs s. (do n \<leftarrow> random (length (x#xs)); return (pick (map (Pair 1) (x#xs)) n) done) s =
      (do n \<leftarrow> random (length (x#xs)); return (nth (x#xs) n) done) s"
  unfolding monad_collapse split_def unfolding pick_nth_random ..
  case (Cons x xs) then show ?case
    unfolding select_weight_def sum_length pick_nth_random_do
    by simp
qed*)

text {* The @{text ML} interface *}

ML {*
structure Quickcheck =
struct

type seed = int * int;

local

val seed = ref (0, 0);

fun init () =
  let
    val now = Time.toNanoseconds (Time.now ());
    val (q, s1) = IntInf.divMod (now, 2147483562);
    val s2 = q mod 2147483398;
  in seed := (s1 + 1, s2 + 1) end;
  
in

val seed = seed; (* FIXME *)

fun run f =
  let
    val (x, seed') = f (!seed);
    val _ = seed := seed'
    val _ = if fst (! seed) = 0 orelse snd (! seed) = 0 then
      (warning "broken random seed"; init ())
      else ()
  in x end;

end;

end;
*}


subsection {* The @{text random} class *}

class random =
  fixes random :: "index \<Rightarrow> seed \<Rightarrow> 'a\<Colon>{} \<times> seed"

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
  fun random_inst tyco thy =
    let
      val { descr, index, ... } = DatatypePackage.the_datatype thy tyco;
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
          val random' = if can DatatypeAux.dest_DtRec dty
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
          val rec' = case some_rec_t
           of SOME rec_t => SOME (HOLogic.mk_prod (@{term "i\<Colon>index"}, rec_t))
            | NONE => NONE;
          val nonrec' = HOLogic.mk_prod (@{term "1\<Colon>index"}, nonrec_t);
          val i_ty = HOLogic.mk_prodT (@{typ index}, lift_ty ty);
          val t = HOLogic.mk_list i_ty (the_list rec' @ single nonrec');
          val t' = Const (@{const_name select_weight}, HOLogic.listT i_ty --> lift_ty (lift_ty ty)) $ t;
          val t'' = Const (@{const_name collapse}, lift_ty (lift_ty ty) --> lift_ty ty) $ t';
        in t'' end;
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
  fun add_random_inst [tyco] = (fn thy => case try (random_inst tyco) thy
       of SOME thy => thy
        | NONE => (warning ("Failed to generate random elements for type" ^ tyco); thy))
    | add_random_inst tycos = tap (fn _ => warning
        ("Will not generated random elements for mutual recursive types " ^ commas (map quote tycos)));
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

code_reserved SML Quickcheck


subsection {* Quickcheck generator *}

ML {*
structure Quickcheck =
struct

open Quickcheck;

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
  in f #> run #> (Option.map o map) (Code.postprocess_term thy) end;

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

(*setup {* Quickcheck.VALUE @{term "\<lambda>(n::int) (m::int) (q::int). n = m + q + 1"} [@{typ int}, @{typ int}, @{typ int}] *}

export_code VALUE in SML module_name QuickcheckExample file "~~/../../gen_code/quickcheck.ML"

definition "FOO = (True, Suc 0)"

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
  @{term "\<lambda>(xs\<Colon>nat list) ys. rev (xs @ ys) = rev xs @ rev ys"}
  [@{typ "nat list"}, @{typ "nat list"}] *}

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
    (random : seed -> 'b * seed)
    (random_split : seed -> seed * seed)
    (seed : seed) =
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

end
