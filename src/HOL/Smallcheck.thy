(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Another simple counterexample generator *}

theory Smallcheck
imports Quickcheck
uses ("Tools/smallvalue_generators.ML")
begin

subsection {* basic operations for generators *}

definition orelse :: "'a option => 'a option => 'a option" (infixr "orelse" 55)
where
  [code_unfold]: "x orelse y = (case x of Some x' => Some x' | None => y)"

subsection {* small value generator type classes *}

class small = term_of +
fixes small :: "('a \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"

instantiation unit :: small
begin

definition "small f d = f ()"

instance ..

end

instantiation int :: small
begin

function small' :: "(int => term list option) => int => int => term list option"
where "small' f d i = (if d < i then None else (case f i of Some t => Some t | None => small' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "small f d = small' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (small, small) small
begin

definition
  "small f d = small (%x. small (%y. f (x, y)) d) d"

instance ..

end

subsection {* full small value generator type classes *}

class full_small = term_of +
fixes full_small :: "('a * (unit => term) \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"

instantiation unit :: full_small
begin

definition "full_small f d = f (Code_Evaluation.valtermify ())"

instance ..

end

instantiation int :: full_small
begin

function full_small' :: "(int * (unit => term) => term list option) => int => int => term list option"
  where "full_small' f d i = (if d < i then None else (case f (i, %_. Code_Evaluation.term_of i) of Some t => Some t | None => full_small' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "full_small f d = full_small' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (full_small, full_small) full_small
begin

definition
  "full_small f d = full_small (%(x, t1). full_small (%(y, t2). f ((x, y),
    %u. Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.term_of (Pair :: 'a => 'b => ('a * 'b))) (t1 ())) (t2 ()))) d) d"

instance ..

end

instantiation "fun" :: ("{equal, full_small}", full_small) full_small
begin

fun full_small_fun' :: "(('a => 'b) * (unit => term) => term list option) => code_numeral => code_numeral => term list option"
where
  "full_small_fun' f i d = (if i > 1 then
    full_small (%(a, at). full_small (%(b, bt).
      full_small_fun' (%(g, gt). f (g(a := b),
        (%_. let T1 = (Typerep.typerep (TYPE('a)));
                 T2 = (Typerep.typerep (TYPE('b)))
             in
               Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.App
                 (Code_Evaluation.Const (STR ''Fun.fun_upd'')
                    (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''fun'') [T1, T2],
                       Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''fun'') [T1, T2]]]]))
               (gt ())) (at ())) (bt ())))) (i - 1) d) d) d
  else (if i > 0 then
    full_small (%(b, t). f (%_. b, %_. Code_Evaluation.Abs (STR ''x'') (Typerep.typerep TYPE('a)) (t ()))) d else None))"

definition full_small_fun :: "(('a => 'b) * (unit => term) => term list option) => code_numeral => term list option"
where
  "full_small_fun f d = full_small_fun' f d d" 

instance ..

end

subsubsection {* A smarter enumeration scheme for functions over finite datatypes *}


class check_all = enum + term_of +
  fixes check_all :: "('a * (unit \<Rightarrow> term) \<Rightarrow> term list option) \<Rightarrow> term list option"
  fixes enum_term_of :: "'a itself \<Rightarrow> unit \<Rightarrow> term list"
  
fun check_all_n_lists :: "(('a :: check_all) list * (unit \<Rightarrow> term list) \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"
where
  "check_all_n_lists f n =
     (if n = 0 then f ([], (%_. [])) else check_all (%(x, xt). check_all_n_lists (%(xs, xst). f ((x # xs), (%_. (xt () # xst ())))) (n - 1)))"

definition mk_map_term :: " (unit \<Rightarrow> typerep) \<Rightarrow> (unit \<Rightarrow> typerep) \<Rightarrow> (unit \<Rightarrow> term list) \<Rightarrow> (unit \<Rightarrow> term list) \<Rightarrow> unit \<Rightarrow> term"
where
  "mk_map_term T1 T2 domm rng =
     (%_. let T1 = T1 ();
              T2 = T2 ();
              update_term = (%g (a, b).
                Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.App
                 (Code_Evaluation.Const (STR ''Fun.fun_upd'')
                   (Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''fun'') [T1, T2],
                      Typerep.Typerep (STR ''fun'') [T1,
                        Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''fun'') [T1, T2]]]]))
                        g) a) b)
          in
             List.foldl update_term (Code_Evaluation.Abs (STR ''x'') T1 (Code_Evaluation.Const (STR ''HOL.undefined'') T2)) (zip (domm ()) (rng ())))"

instantiation "fun" :: ("{equal, check_all}", check_all) check_all
begin

definition
  "check_all f =
    (let
      mk_term = mk_map_term (%_. Typerep.typerep (TYPE('a))) (%_. Typerep.typerep (TYPE('b))) (enum_term_of (TYPE('a)));
      enum = (Enum.enum :: 'a list)
    in check_all_n_lists (\<lambda>(ys, yst). f (the o map_of (zip enum ys), mk_term yst)) (Code_Numeral.of_nat (length enum)))"

definition enum_term_of_fun :: "('a => 'b) itself => unit => term list"
where
  "enum_term_of_fun = (%_ _. let
    enum_term_of_a = enum_term_of (TYPE('a));
    mk_term = mk_map_term (%_. Typerep.typerep (TYPE('a))) (%_. Typerep.typerep (TYPE('b))) enum_term_of_a
  in map (%ys. mk_term (%_. ys) ()) (Enum.n_lists (length (enum_term_of_a ())) (enum_term_of (TYPE('b)) ())))"
 
instance ..

end


instantiation unit :: check_all
begin

definition
  "check_all f = f (Code_Evaluation.valtermify ())"

definition enum_term_of_unit :: "unit itself => unit => term list"
where
  "enum_term_of_unit = (%_ _. [Code_Evaluation.term_of ()])"

instance ..

end


instantiation bool :: check_all
begin

definition
  "check_all f = (case f (Code_Evaluation.valtermify False) of Some x' \<Rightarrow> Some x' | None \<Rightarrow> f (Code_Evaluation.valtermify True))"

definition enum_term_of_bool :: "bool itself => unit => term list"
where
  "enum_term_of_bool = (%_ _. map Code_Evaluation.term_of (Enum.enum :: bool list))"

instance ..

end


instantiation prod :: (check_all, check_all) check_all
begin

definition
  "check_all f = check_all (%(x, t1). check_all (%(y, t2). f ((x, y), %_. Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.term_of (Pair :: 'a => 'b => ('a * 'b))) (t1 ())) (t2 ()))))"

definition enum_term_of_prod :: "('a * 'b) itself => unit => term list"
where
  "enum_term_of_prod = (%_ _. map (%(x, y). Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.term_of (Pair :: 'a => 'b => ('a * 'b))) x) y) (Enum.product (enum_term_of (TYPE('a)) ()) (enum_term_of (TYPE('b)) ())))"

instance ..

end


instantiation sum :: (check_all, check_all) check_all
begin

definition
  "check_all f = (case check_all (%(a, t). f (Inl a, %_. Code_Evaluation.App (Code_Evaluation.term_of (Inl :: 'a => 'a + 'b)) (t ()))) of Some x' => Some x'
             | None => check_all (%(b, t). f (Inr b, %_. Code_Evaluation.App (Code_Evaluation.term_of (Inr :: 'b => 'a + 'b)) (t ()))))"

definition enum_term_of_sum :: "('a + 'b) itself => unit => term list"
where
  "enum_term_of_sum = (%_ _. map (Code_Evaluation.App (Code_Evaluation.term_of (Inl :: 'a => ('a + 'b)))) (enum_term_of (TYPE('a)) ()) @
     map (Code_Evaluation.App (Code_Evaluation.term_of (Inr :: 'b => ('a + 'b)))) (enum_term_of (TYPE('b)) ()))"

instance ..

end

instantiation nibble :: check_all
begin

definition
  "check_all f =
    f (Code_Evaluation.valtermify Nibble0) orelse
    f (Code_Evaluation.valtermify Nibble1) orelse
    f (Code_Evaluation.valtermify Nibble2) orelse
    f (Code_Evaluation.valtermify Nibble3) orelse
    f (Code_Evaluation.valtermify Nibble4) orelse
    f (Code_Evaluation.valtermify Nibble5) orelse
    f (Code_Evaluation.valtermify Nibble6) orelse
    f (Code_Evaluation.valtermify Nibble7) orelse
    f (Code_Evaluation.valtermify Nibble8) orelse
    f (Code_Evaluation.valtermify Nibble9) orelse
    f (Code_Evaluation.valtermify NibbleA) orelse
    f (Code_Evaluation.valtermify NibbleB) orelse
    f (Code_Evaluation.valtermify NibbleC) orelse
    f (Code_Evaluation.valtermify NibbleD) orelse
    f (Code_Evaluation.valtermify NibbleE) orelse
    f (Code_Evaluation.valtermify NibbleF)"

definition enum_term_of_nibble :: "nibble itself => unit => term list"
where
  "enum_term_of_nibble = (%_ _. map Code_Evaluation.term_of (Enum.enum :: nibble list))"

instance ..

end


instantiation char :: check_all
begin

definition
  "check_all f = check_all (%(x, t1). check_all (%(y, t2). f (Char x y, %_. Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.term_of Char) (t1 ())) (t2 ()))))"

definition enum_term_of_char :: "char itself => unit => term list"
where
  "enum_term_of_char = (%_ _. map Code_Evaluation.term_of (Enum.enum :: char list))"

instance ..

end


instantiation option :: (check_all) check_all
begin

definition
  "check_all f = f (Code_Evaluation.valtermify (None :: 'a option)) orelse check_all (%(x, t). f (Some x, %_. Code_Evaluation.App
    (Code_Evaluation.Const (STR ''Option.option.Some'')
      (Typerep.Typerep (STR ''fun'') [Typerep.typerep TYPE('a),  Typerep.Typerep (STR ''Option.option'') [Typerep.typerep TYPE('a)]])) (t ())))"

definition enum_term_of_option :: "'a option itself => unit => term list"
where
  "enum_term_of_option = (% _ _. (Code_Evaluation.term_of (None :: 'a option)) # (map (Code_Evaluation.App (Code_Evaluation.term_of (Some :: 'a => 'a option))) (enum_term_of (TYPE('a)) ())))"

instance ..

end


instantiation Enum.finite_1 :: check_all
begin

definition
  "check_all f = f (Code_Evaluation.valtermify Enum.finite_1.a\<^isub>1)"

definition enum_term_of_finite_1 :: "Enum.finite_1 itself => unit => term list"
where
  "enum_term_of_finite_1 = (%_ _. [Code_Evaluation.term_of Enum.finite_1.a\<^isub>1])"

instance ..

end

instantiation Enum.finite_2 :: check_all
begin

definition
  "check_all f = (case f (Code_Evaluation.valtermify Enum.finite_2.a\<^isub>1) of Some x' \<Rightarrow> Some x' | None \<Rightarrow> f (Code_Evaluation.valtermify Enum.finite_2.a\<^isub>2))"

definition enum_term_of_finite_2 :: "Enum.finite_2 itself => unit => term list"
where
  "enum_term_of_finite_2 = (%_ _. map Code_Evaluation.term_of (Enum.enum :: Enum.finite_2 list))"

instance ..

end

instantiation Enum.finite_3 :: check_all
begin

definition
  "check_all f = (case f (Code_Evaluation.valtermify Enum.finite_3.a\<^isub>1) of Some x' \<Rightarrow> Some x' | None \<Rightarrow> (case f (Code_Evaluation.valtermify Enum.finite_3.a\<^isub>2) of Some x' \<Rightarrow> Some x' | None \<Rightarrow> f (Code_Evaluation.valtermify Enum.finite_3.a\<^isub>3)))"

definition enum_term_of_finite_3 :: "Enum.finite_3 itself => unit => term list"
where
  "enum_term_of_finite_3 = (%_ _. map Code_Evaluation.term_of (Enum.enum :: Enum.finite_3 list))"

instance ..

end



subsection {* Defining combinators for any first-order data type *}

definition catch_match :: "term list option => term list option => term list option"
where
  [code del]: "catch_match t1 t2 = (SOME t. t = t1 \<or> t = t2)"

code_const catch_match 
  (SML "(_) handle Match => _")

use "Tools/smallvalue_generators.ML"

setup {* Smallvalue_Generators.setup *}

declare [[quickcheck_tester = exhaustive]]

hide_fact orelse_def catch_match_def
no_notation orelse (infixr "orelse" 55)
hide_const (open) orelse catch_match mk_map_term check_all_n_lists

end