(*  Title:      HOL/Quickcheck_Exhaustive.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>A simple counterexample generator performing exhaustive testing\<close>

theory Quickcheck_Exhaustive
imports Quickcheck_Random
keywords "quickcheck_generator" :: thy_decl
begin

subsection \<open>Basic operations for exhaustive generators\<close>

definition orelse :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"  (infixr "orelse" 55)
  where [code_unfold]: "x orelse y = (case x of Some x' \<Rightarrow> Some x' | None \<Rightarrow> y)"


subsection \<open>Exhaustive generator type classes\<close>

class exhaustive = term_of +
  fixes exhaustive :: "('a \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"

class full_exhaustive = term_of +
  fixes full_exhaustive ::
    "('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"

instantiation natural :: full_exhaustive
begin

function full_exhaustive_natural' ::
    "(natural \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
      natural \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_natural' f d i =
    (if d < i then None
     else (f (i, \<lambda>_. Code_Evaluation.term_of i)) orelse (full_exhaustive_natural' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat_of_natural (d + 1 - i))") (auto simp add: less_natural_def)

definition "full_exhaustive f d = full_exhaustive_natural' f d 0"

instance ..

end

instantiation natural :: exhaustive
begin

function exhaustive_natural' ::
    "(natural \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "exhaustive_natural' f d i =
    (if d < i then None
     else (f i orelse exhaustive_natural' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat_of_natural (d + 1 - i))") (auto simp add: less_natural_def)

definition "exhaustive f d = exhaustive_natural' f d 0"

instance ..

end

instantiation integer :: exhaustive
begin

function exhaustive_integer' ::
    "(integer \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> (bool \<times> term list) option"
  where "exhaustive_integer' f d i =
    (if d < i then None else (f i orelse exhaustive_integer' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat_of_integer (d + 1 - i))")
    (auto simp add: less_integer_def nat_of_integer_def)

definition "exhaustive f d = exhaustive_integer' f (integer_of_natural d) (- (integer_of_natural d))"

instance ..

end

instantiation integer :: full_exhaustive
begin

function full_exhaustive_integer' ::
    "(integer \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
      integer \<Rightarrow> integer \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_integer' f d i =
    (if d < i then None
     else
      (case f (i, \<lambda>_. Code_Evaluation.term_of i) of
        Some t \<Rightarrow> Some t
      | None \<Rightarrow> full_exhaustive_integer' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat_of_integer (d + 1 - i))")
    (auto simp add: less_integer_def nat_of_integer_def)

definition "full_exhaustive f d =
  full_exhaustive_integer' f (integer_of_natural d) (- (integer_of_natural d))"

instance ..

end

instantiation nat :: exhaustive
begin

definition "exhaustive f d = exhaustive (\<lambda>x. f (nat_of_natural x)) d"

instance ..

end

instantiation nat :: full_exhaustive
begin

definition "full_exhaustive f d =
  full_exhaustive (\<lambda>(x, xt). f (nat_of_natural x, \<lambda>_. Code_Evaluation.term_of (nat_of_natural x))) d"

instance ..

end

instantiation int :: exhaustive
begin

function exhaustive_int' ::
    "(int \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (bool \<times> term list) option"
  where "exhaustive_int' f d i =
    (if d < i then None else (f i orelse exhaustive_int' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat (d + 1 - i))") auto

definition "exhaustive f d =
  exhaustive_int' f (int_of_integer (integer_of_natural d))
    (- (int_of_integer (integer_of_natural d)))"

instance ..

end

instantiation int :: full_exhaustive
begin

function full_exhaustive_int' ::
    "(int \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_int' f d i =
    (if d < i then None
     else
      (case f (i, \<lambda>_. Code_Evaluation.term_of i) of
        Some t \<Rightarrow> Some t
       | None \<Rightarrow> full_exhaustive_int' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, d, i). nat (d + 1 - i))") auto

definition "full_exhaustive f d =
  full_exhaustive_int' f (int_of_integer (integer_of_natural d))
    (- (int_of_integer (integer_of_natural d)))"

instance ..

end

instantiation prod :: (exhaustive, exhaustive) exhaustive
begin

definition "exhaustive f d = exhaustive (\<lambda>x. exhaustive (\<lambda>y. f ((x, y))) d) d"

instance ..

end

context
  includes term_syntax
begin

definition
  [code_unfold]: "valtermify_pair x y =
    Code_Evaluation.valtermify (Pair :: 'a::typerep \<Rightarrow> 'b::typerep \<Rightarrow> 'a \<times> 'b) {\<cdot>} x {\<cdot>} y"

end

instantiation prod :: (full_exhaustive, full_exhaustive) full_exhaustive
begin

definition "full_exhaustive f d =
  full_exhaustive (\<lambda>x. full_exhaustive (\<lambda>y. f (valtermify_pair x y)) d) d"

instance ..

end

instantiation set :: (exhaustive) exhaustive
begin

fun exhaustive_set
where
  "exhaustive_set f i =
    (if i = 0 then None
     else
      f {} orelse
      exhaustive_set
        (\<lambda>A. f A orelse exhaustive (\<lambda>x. if x \<in> A then None else f (insert x A)) (i - 1)) (i - 1))"

instance ..

end

instantiation set :: (full_exhaustive) full_exhaustive
begin

fun full_exhaustive_set
where
  "full_exhaustive_set f i =
    (if i = 0 then None
     else
      f valterm_emptyset orelse
      full_exhaustive_set
        (\<lambda>A. f A orelse Quickcheck_Exhaustive.full_exhaustive
          (\<lambda>x. if fst x \<in> fst A then None else f (valtermify_insert x A)) (i - 1)) (i - 1))"

instance ..

end

instantiation "fun" :: ("{equal,exhaustive}", exhaustive) exhaustive
begin

fun exhaustive_fun' ::
  "(('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "exhaustive_fun' f i d =
    (exhaustive (\<lambda>b. f (\<lambda>_. b)) d) orelse
      (if i > 1 then
        exhaustive_fun'
          (\<lambda>g. exhaustive (\<lambda>a. exhaustive (\<lambda>b. f (g(a := b))) d) d) (i - 1) d else None)"

definition exhaustive_fun ::
  "(('a \<Rightarrow> 'b) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "exhaustive_fun f d = exhaustive_fun' f d d"

instance ..

end

definition [code_unfold]:
  "valtermify_absdummy =
    (\<lambda>(v, t).
      (\<lambda>_::'a. v,
        \<lambda>u::unit. Code_Evaluation.Abs (STR ''x'') (Typerep.typerep TYPE('a::typerep)) (t ())))"

context
  includes term_syntax
begin

definition
  [code_unfold]: "valtermify_fun_upd g a b =
    Code_Evaluation.valtermify
      (fun_upd :: ('a::typerep \<Rightarrow> 'b::typerep) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b) {\<cdot>} g {\<cdot>} a {\<cdot>} b"

end

instantiation "fun" :: ("{equal,full_exhaustive}", full_exhaustive) full_exhaustive
begin

fun full_exhaustive_fun' ::
  "(('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
    natural \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "full_exhaustive_fun' f i d =
    full_exhaustive (\<lambda>v. f (valtermify_absdummy v)) d orelse
    (if i > 1 then
      full_exhaustive_fun'
        (\<lambda>g. full_exhaustive
          (\<lambda>a. full_exhaustive (\<lambda>b. f (valtermify_fun_upd g a b)) d) d) (i - 1) d
     else None)"

definition full_exhaustive_fun ::
  "(('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
    natural \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_fun f d = full_exhaustive_fun' f d d"

instance ..

end

subsubsection \<open>A smarter enumeration scheme for functions over finite datatypes\<close>

class check_all = enum + term_of +
  fixes check_all :: "('a \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> (bool * term list) option"
  fixes enum_term_of :: "'a itself \<Rightarrow> unit \<Rightarrow> term list"

fun check_all_n_lists :: "('a::check_all list \<times> (unit \<Rightarrow> term list) \<Rightarrow>
  (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool * term list) option"
where
  "check_all_n_lists f n =
    (if n = 0 then f ([], (\<lambda>_. []))
     else check_all (\<lambda>(x, xt).
      check_all_n_lists (\<lambda>(xs, xst). f ((x # xs), (\<lambda>_. (xt () # xst ())))) (n - 1)))"

context
  includes term_syntax
begin

definition
  [code_unfold]: "termify_fun_upd g a b =
    (Code_Evaluation.termify
      (fun_upd :: ('a::typerep \<Rightarrow> 'b::typerep) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b) <\<cdot>> g <\<cdot>> a <\<cdot>> b)"

end

definition mk_map_term ::
  "(unit \<Rightarrow> typerep) \<Rightarrow> (unit \<Rightarrow> typerep) \<Rightarrow>
    (unit \<Rightarrow> term list) \<Rightarrow> (unit \<Rightarrow> term list) \<Rightarrow> unit \<Rightarrow> term"
  where "mk_map_term T1 T2 domm rng =
    (\<lambda>_.
      let
        T1 = T1 ();
        T2 = T2 ();
        update_term =
          (\<lambda>g (a, b).
            Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.App
             (Code_Evaluation.Const (STR ''Fun.fun_upd'')
               (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''fun'') [T1, T2],
                  Typerep.Typerep (STR ''fun'') [T1,
                    Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''fun'') [T1, T2]]]]))
                    g) a) b)
      in
        List.foldl update_term
          (Code_Evaluation.Abs (STR ''x'') T1
            (Code_Evaluation.Const (STR ''HOL.undefined'') T2)) (zip (domm ()) (rng ())))"

instantiation "fun" :: ("{equal,check_all}", check_all) check_all
begin

definition
  "check_all f =
    (let
      mk_term =
        mk_map_term
          (\<lambda>_. Typerep.typerep (TYPE('a)))
          (\<lambda>_. Typerep.typerep (TYPE('b)))
          (enum_term_of (TYPE('a)));
      enum = (Enum.enum :: 'a list)
    in
      check_all_n_lists
        (\<lambda>(ys, yst). f (the \<circ> map_of (zip enum ys), mk_term yst))
        (natural_of_nat (length enum)))"

definition enum_term_of_fun :: "('a \<Rightarrow> 'b) itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_fun =
    (\<lambda>_ _.
      let
        enum_term_of_a = enum_term_of (TYPE('a));
        mk_term =
          mk_map_term
            (\<lambda>_. Typerep.typerep (TYPE('a)))
            (\<lambda>_. Typerep.typerep (TYPE('b)))
            enum_term_of_a
      in
        map (\<lambda>ys. mk_term (\<lambda>_. ys) ())
          (List.n_lists (length (enum_term_of_a ())) (enum_term_of (TYPE('b)) ())))"

instance ..

end

context
  includes term_syntax
begin

fun check_all_subsets ::
  "(('a::typerep) set \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow>
    ('a \<times> (unit \<Rightarrow> term)) list \<Rightarrow> (bool \<times> term list) option"
where
  "check_all_subsets f [] = f valterm_emptyset"
| "check_all_subsets f (x # xs) =
    check_all_subsets (\<lambda>s. case f s of Some ts \<Rightarrow> Some ts | None \<Rightarrow> f (valtermify_insert x s)) xs"

definition
  [code_unfold]: "term_emptyset = Code_Evaluation.termify ({} :: ('a::typerep) set)"

definition
  [code_unfold]: "termify_insert x s =
    Code_Evaluation.termify (insert :: ('a::typerep) \<Rightarrow> 'a set \<Rightarrow> 'a set)  <\<cdot>> x <\<cdot>> s"

definition setify :: "('a::typerep) itself \<Rightarrow> term list \<Rightarrow> term"
where
  "setify T ts = foldr (termify_insert T) ts (term_emptyset T)"

end

instantiation set :: (check_all) check_all
begin

definition
  "check_all_set f =
     check_all_subsets f
      (zip (Enum.enum :: 'a list)
        (map (\<lambda>a. \<lambda>u :: unit. a) (Quickcheck_Exhaustive.enum_term_of (TYPE ('a)) ())))"

definition enum_term_of_set :: "'a set itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_set _ _ =
    map (setify (TYPE('a))) (subseqs (Quickcheck_Exhaustive.enum_term_of (TYPE('a)) ()))"

instance ..

end

instantiation unit :: check_all
begin

definition "check_all f = f (Code_Evaluation.valtermify ())"

definition enum_term_of_unit :: "unit itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_unit = (\<lambda>_ _. [Code_Evaluation.term_of ()])"

instance ..

end


instantiation bool :: check_all
begin

definition
  "check_all f =
    (case f (Code_Evaluation.valtermify False) of
      Some x' \<Rightarrow> Some x'
    | None \<Rightarrow> f (Code_Evaluation.valtermify True))"

definition enum_term_of_bool :: "bool itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_bool = (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: bool list))"

instance ..

end

context
  includes term_syntax
begin

definition [code_unfold]:
  "termify_pair x y =
    Code_Evaluation.termify (Pair :: 'a::typerep \<Rightarrow> 'b :: typerep \<Rightarrow> 'a * 'b) <\<cdot>> x <\<cdot>> y"

end

instantiation prod :: (check_all, check_all) check_all
begin

definition "check_all f = check_all (\<lambda>x. check_all (\<lambda>y. f (valtermify_pair x y)))"

definition enum_term_of_prod :: "('a * 'b) itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_prod =
    (\<lambda>_ _.
      map (\<lambda>(x, y). termify_pair TYPE('a) TYPE('b) x y)
        (List.product (enum_term_of (TYPE('a)) ()) (enum_term_of (TYPE('b)) ())))"

instance ..

end

context
  includes term_syntax
begin

definition
  [code_unfold]: "valtermify_Inl x =
    Code_Evaluation.valtermify (Inl :: 'a::typerep \<Rightarrow> 'a + 'b :: typerep) {\<cdot>} x"

definition
  [code_unfold]: "valtermify_Inr x =
    Code_Evaluation.valtermify (Inr :: 'b::typerep \<Rightarrow> 'a::typerep + 'b) {\<cdot>} x"

end

instantiation sum :: (check_all, check_all) check_all
begin

definition
  "check_all f = check_all (\<lambda>a. f (valtermify_Inl a)) orelse check_all (\<lambda>b. f (valtermify_Inr b))"

definition enum_term_of_sum :: "('a + 'b) itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_sum =
    (\<lambda>_ _.
      let
        T1 = Typerep.typerep (TYPE('a));
        T2 = Typerep.typerep (TYPE('b))
      in
        map
          (Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inl'')
            (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])))
          (enum_term_of (TYPE('a)) ()) @
        map
          (Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inr'')
            (Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])))
          (enum_term_of (TYPE('b)) ()))"

instance ..

end

instantiation char :: check_all
begin

primrec check_all_char' ::
  "(char \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> char list \<Rightarrow> (bool \<times> term list) option"
  where "check_all_char' f [] = None"
  | "check_all_char' f (c # cs) = f (c, \<lambda>_. Code_Evaluation.term_of c)
      orelse check_all_char' f cs"

definition check_all_char ::
  "(char \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> (bool \<times> term list) option"
  where "check_all f = check_all_char' f Enum.enum"

definition enum_term_of_char :: "char itself \<Rightarrow> unit \<Rightarrow> term list"
where
  "enum_term_of_char = (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: char list))"

instance ..

end

instantiation option :: (check_all) check_all
begin

definition
  "check_all f =
    f (Code_Evaluation.valtermify (None :: 'a option)) orelse
    check_all
      (\<lambda>(x, t).
        f
          (Some x,
            \<lambda>_. Code_Evaluation.App
              (Code_Evaluation.Const (STR ''Option.option.Some'')
                (Typerep.Typerep (STR ''fun'')
                [Typerep.typerep TYPE('a),
                 Typerep.Typerep (STR ''Option.option'') [Typerep.typerep TYPE('a)]])) (t ())))"

definition enum_term_of_option :: "'a option itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_option =
    (\<lambda> _ _.
      Code_Evaluation.term_of (None :: 'a option) #
      (map
        (Code_Evaluation.App
          (Code_Evaluation.Const (STR ''Option.option.Some'')
            (Typerep.Typerep (STR ''fun'')
              [Typerep.typerep TYPE('a),
               Typerep.Typerep (STR ''Option.option'') [Typerep.typerep TYPE('a)]])))
        (enum_term_of (TYPE('a)) ())))"

instance ..

end


instantiation Enum.finite_1 :: check_all
begin

definition "check_all f = f (Code_Evaluation.valtermify Enum.finite_1.a\<^sub>1)"

definition enum_term_of_finite_1 :: "Enum.finite_1 itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_finite_1 = (\<lambda>_ _. [Code_Evaluation.term_of Enum.finite_1.a\<^sub>1])"

instance ..

end

instantiation Enum.finite_2 :: check_all
begin

definition
  "check_all f =
    (f (Code_Evaluation.valtermify Enum.finite_2.a\<^sub>1) orelse
     f (Code_Evaluation.valtermify Enum.finite_2.a\<^sub>2))"

definition enum_term_of_finite_2 :: "Enum.finite_2 itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_finite_2 =
    (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: Enum.finite_2 list))"

instance ..

end

instantiation Enum.finite_3 :: check_all
begin

definition
  "check_all f =
    (f (Code_Evaluation.valtermify Enum.finite_3.a\<^sub>1) orelse
     f (Code_Evaluation.valtermify Enum.finite_3.a\<^sub>2) orelse
     f (Code_Evaluation.valtermify Enum.finite_3.a\<^sub>3))"

definition enum_term_of_finite_3 :: "Enum.finite_3 itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_finite_3 =
    (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: Enum.finite_3 list))"

instance ..

end

instantiation Enum.finite_4 :: check_all
begin

definition
  "check_all f =
    f (Code_Evaluation.valtermify Enum.finite_4.a\<^sub>1) orelse
    f (Code_Evaluation.valtermify Enum.finite_4.a\<^sub>2) orelse
    f (Code_Evaluation.valtermify Enum.finite_4.a\<^sub>3) orelse
    f (Code_Evaluation.valtermify Enum.finite_4.a\<^sub>4)"

definition enum_term_of_finite_4 :: "Enum.finite_4 itself \<Rightarrow> unit \<Rightarrow> term list"
  where "enum_term_of_finite_4 =
    (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: Enum.finite_4 list))"

instance ..

end

subsection \<open>Bounded universal quantifiers\<close>

class bounded_forall =
  fixes bounded_forall :: "('a \<Rightarrow> bool) \<Rightarrow> natural \<Rightarrow> bool"


subsection \<open>Fast exhaustive combinators\<close>

class fast_exhaustive = term_of +
  fixes fast_exhaustive :: "('a \<Rightarrow> unit) \<Rightarrow> natural \<Rightarrow> unit"

axiomatization throw_Counterexample :: "term list \<Rightarrow> unit"
axiomatization catch_Counterexample :: "unit \<Rightarrow> term list option"

code_printing
  constant throw_Counterexample \<rightharpoonup>
    (Quickcheck) "raise (Exhaustive'_Generators.Counterexample _)"
| constant catch_Counterexample \<rightharpoonup>
    (Quickcheck) "(((_); NONE) handle Exhaustive'_Generators.Counterexample ts \<Rightarrow> SOME ts)"


subsection \<open>Continuation passing style functions as plus monad\<close>

type_synonym 'a cps = "('a \<Rightarrow> term list option) \<Rightarrow> term list option"

definition cps_empty :: "'a cps"
  where "cps_empty = (\<lambda>cont. None)"

definition cps_single :: "'a \<Rightarrow> 'a cps"
  where "cps_single v = (\<lambda>cont. cont v)"

definition cps_bind :: "'a cps \<Rightarrow> ('a \<Rightarrow> 'b cps) \<Rightarrow> 'b cps"
  where "cps_bind m f = (\<lambda>cont. m (\<lambda>a. (f a) cont))"

definition cps_plus :: "'a cps \<Rightarrow> 'a cps \<Rightarrow> 'a cps"
  where "cps_plus a b = (\<lambda>c. case a c of None \<Rightarrow> b c | Some x \<Rightarrow> Some x)"

definition cps_if :: "bool \<Rightarrow> unit cps"
  where "cps_if b = (if b then cps_single () else cps_empty)"

definition cps_not :: "unit cps \<Rightarrow> unit cps"
  where "cps_not n = (\<lambda>c. case n (\<lambda>u. Some []) of None \<Rightarrow> c () | Some _ \<Rightarrow> None)"

type_synonym 'a pos_bound_cps =
  "('a \<Rightarrow> (bool * term list) option) \<Rightarrow> natural \<Rightarrow> (bool * term list) option"

definition pos_bound_cps_empty :: "'a pos_bound_cps"
  where "pos_bound_cps_empty = (\<lambda>cont i. None)"

definition pos_bound_cps_single :: "'a \<Rightarrow> 'a pos_bound_cps"
  where "pos_bound_cps_single v = (\<lambda>cont i. cont v)"

definition pos_bound_cps_bind :: "'a pos_bound_cps \<Rightarrow> ('a \<Rightarrow> 'b pos_bound_cps) \<Rightarrow> 'b pos_bound_cps"
  where "pos_bound_cps_bind m f = (\<lambda>cont i. if i = 0 then None else (m (\<lambda>a. (f a) cont i) (i - 1)))"

definition pos_bound_cps_plus :: "'a pos_bound_cps \<Rightarrow> 'a pos_bound_cps \<Rightarrow> 'a pos_bound_cps"
  where "pos_bound_cps_plus a b = (\<lambda>c i. case a c i of None \<Rightarrow> b c i | Some x \<Rightarrow> Some x)"

definition pos_bound_cps_if :: "bool \<Rightarrow> unit pos_bound_cps"
  where "pos_bound_cps_if b = (if b then pos_bound_cps_single () else pos_bound_cps_empty)"

datatype (plugins only: code extraction) (dead 'a) unknown =
  Unknown | Known 'a

datatype (plugins only: code extraction) (dead 'a) three_valued =
  Unknown_value | Value 'a | No_value

type_synonym 'a neg_bound_cps =
  "('a unknown \<Rightarrow> term list three_valued) \<Rightarrow> natural \<Rightarrow> term list three_valued"

definition neg_bound_cps_empty :: "'a neg_bound_cps"
  where "neg_bound_cps_empty = (\<lambda>cont i. No_value)"

definition neg_bound_cps_single :: "'a \<Rightarrow> 'a neg_bound_cps"
  where "neg_bound_cps_single v = (\<lambda>cont i. cont (Known v))"

definition neg_bound_cps_bind :: "'a neg_bound_cps \<Rightarrow> ('a \<Rightarrow> 'b neg_bound_cps) \<Rightarrow> 'b neg_bound_cps"
  where "neg_bound_cps_bind m f =
    (\<lambda>cont i.
      if i = 0 then cont Unknown
      else m (\<lambda>a. case a of Unknown \<Rightarrow> cont Unknown | Known a' \<Rightarrow> f a' cont i) (i - 1))"

definition neg_bound_cps_plus :: "'a neg_bound_cps \<Rightarrow> 'a neg_bound_cps \<Rightarrow> 'a neg_bound_cps"
  where "neg_bound_cps_plus a b =
    (\<lambda>c i.
      case a c i of
        No_value \<Rightarrow> b c i
      | Value x \<Rightarrow> Value x
      | Unknown_value \<Rightarrow>
          (case b c i of
            No_value \<Rightarrow> Unknown_value
          | Value x \<Rightarrow> Value x
          | Unknown_value \<Rightarrow> Unknown_value))"

definition neg_bound_cps_if :: "bool \<Rightarrow> unit neg_bound_cps"
  where "neg_bound_cps_if b = (if b then neg_bound_cps_single () else neg_bound_cps_empty)"

definition neg_bound_cps_not :: "unit pos_bound_cps \<Rightarrow> unit neg_bound_cps"
  where "neg_bound_cps_not n =
    (\<lambda>c i. case n (\<lambda>u. Some (True, [])) i of None \<Rightarrow> c (Known ()) | Some _ \<Rightarrow> No_value)"

definition pos_bound_cps_not :: "unit neg_bound_cps \<Rightarrow> unit pos_bound_cps"
  where "pos_bound_cps_not n =
    (\<lambda>c i. case n (\<lambda>u. Value []) i of No_value \<Rightarrow> c () | Value _ \<Rightarrow> None | Unknown_value \<Rightarrow> None)"


subsection \<open>Defining generators for any first-order data type\<close>

axiomatization unknown :: 'a

notation (output) unknown  ("?")

ML_file \<open>Tools/Quickcheck/exhaustive_generators.ML\<close>

declare [[quickcheck_batch_tester = exhaustive]]


subsection \<open>Defining generators for abstract types\<close>

ML_file \<open>Tools/Quickcheck/abstract_generators.ML\<close>

hide_fact (open) orelse_def
no_notation orelse  (infixr "orelse" 55)

hide_const valtermify_absdummy valtermify_fun_upd
  valterm_emptyset valtermify_insert
  valtermify_pair valtermify_Inl valtermify_Inr
  termify_fun_upd term_emptyset termify_insert termify_pair setify

hide_const (open)
  exhaustive full_exhaustive
  exhaustive_int' full_exhaustive_int'
  exhaustive_integer' full_exhaustive_integer'
  exhaustive_natural' full_exhaustive_natural'
  throw_Counterexample catch_Counterexample
  check_all enum_term_of
  orelse unknown mk_map_term check_all_n_lists check_all_subsets

hide_type (open) cps pos_bound_cps neg_bound_cps unknown three_valued

hide_const (open) cps_empty cps_single cps_bind cps_plus cps_if cps_not
  pos_bound_cps_empty pos_bound_cps_single pos_bound_cps_bind
  pos_bound_cps_plus pos_bound_cps_if pos_bound_cps_not
  neg_bound_cps_empty neg_bound_cps_single neg_bound_cps_bind
  neg_bound_cps_plus neg_bound_cps_if neg_bound_cps_not
  Unknown Known Unknown_value Value No_value

end
