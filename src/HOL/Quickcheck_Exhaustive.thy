(* Author: Lukas Bulwahn, TU Muenchen *)

header {* A simple counterexample generator performing exhaustive testing *}

theory Quickcheck_Exhaustive
imports Quickcheck
uses ("Tools/Quickcheck/exhaustive_generators.ML")
begin

subsection {* basic operations for exhaustive generators *}

definition orelse :: "'a option => 'a option => 'a option" (infixr "orelse" 55)
where
  [code_unfold]: "x orelse y = (case x of Some x' => Some x' | None => y)"

subsection {* exhaustive generator type classes *}

class exhaustive = term_of +
  fixes exhaustive :: "('a \<Rightarrow> (bool * term list) option) \<Rightarrow> code_numeral \<Rightarrow> (bool * term list) option"
  
class full_exhaustive = term_of +
  fixes full_exhaustive :: "('a * (unit => term) \<Rightarrow> (bool * term list) option) \<Rightarrow> code_numeral \<Rightarrow> (bool * term list) option"

instantiation code_numeral :: full_exhaustive
begin

function full_exhaustive_code_numeral' :: "(code_numeral * (unit => term) => (bool * term list) option) => code_numeral => code_numeral => (bool * term list) option"
  where "full_exhaustive_code_numeral' f d i =
    (if d < i then None
    else (f (i, %_. Code_Evaluation.term_of i)) orelse (full_exhaustive_code_numeral' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (%(_, d, i). Code_Numeral.nat_of (d + 1 - i))") auto

definition "full_exhaustive f d = full_exhaustive_code_numeral' f d 0"

instance ..

end

instantiation code_numeral :: exhaustive
begin

function exhaustive_code_numeral' :: "(code_numeral => (bool * term list) option) => code_numeral => code_numeral => (bool * term list) option"
  where "exhaustive_code_numeral' f d i =
    (if d < i then None
    else (f i orelse exhaustive_code_numeral' f d (i + 1)))"
by pat_completeness auto

termination
  by (relation "measure (%(_, d, i). Code_Numeral.nat_of (d + 1 - i))") auto

definition "exhaustive f d = exhaustive_code_numeral' f d 0"

instance ..

end

instantiation nat :: exhaustive
begin

definition "exhaustive f d = exhaustive (%x. f (Code_Numeral.nat_of x)) d"

instance ..

end

instantiation nat :: full_exhaustive
begin

definition "full_exhaustive f d = full_exhaustive (%(x, xt). f (Code_Numeral.nat_of x, %_. Code_Evaluation.term_of (Code_Numeral.nat_of x))) d"

instance ..

end

instantiation int :: exhaustive
begin

function exhaustive' :: "(int => (bool * term list) option) => int => int => (bool * term list) option"
  where "exhaustive' f d i = (if d < i then None else (f i orelse exhaustive' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "exhaustive f d = exhaustive' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation int :: full_exhaustive
begin

function full_exhaustive' :: "(int * (unit => term) => (bool * term list) option) => int => int => (bool * term list) option"
  where "full_exhaustive' f d i = (if d < i then None else (case f (i, %_. Code_Evaluation.term_of i) of Some t => Some t | None => full_exhaustive' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "full_exhaustive f d = full_exhaustive' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (exhaustive, exhaustive) exhaustive
begin

definition
  "exhaustive f d = exhaustive (%x. exhaustive (%y. f ((x, y))) d) d"

instance ..

end

instantiation prod :: (full_exhaustive, full_exhaustive) full_exhaustive
begin

definition
  "full_exhaustive f d = full_exhaustive (%(x, t1). full_exhaustive (%(y, t2). f ((x, y),
    %u. let T1 = (Typerep.typerep (TYPE('a)));
            T2 = (Typerep.typerep (TYPE('b)))
    in Code_Evaluation.App (Code_Evaluation.App (
      Code_Evaluation.Const (STR ''Product_Type.Pair'') 
      (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Product_Type.prod'') [T1, T2]]]))
      (t1 ())) (t2 ()))) d) d"

instance ..

end

instantiation "fun" :: ("{equal, exhaustive}", exhaustive) exhaustive
begin

fun exhaustive_fun' :: "(('a => 'b) => (bool * term list) option) => code_numeral => code_numeral => (bool * term list) option"
where
  "exhaustive_fun' f i d = (exhaustive (%b. f (%_. b)) d)
   orelse (if i > 1 then
     exhaustive_fun' (%g. exhaustive (%a. exhaustive (%b.
       f (g(a := b))) d) d) (i - 1) d else None)"

definition exhaustive_fun :: "(('a => 'b) => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "exhaustive_fun f d = exhaustive_fun' f d d" 

instance ..

end

instantiation "fun" :: ("{equal, full_exhaustive}", full_exhaustive) full_exhaustive
begin

fun full_exhaustive_fun' :: "(('a => 'b) * (unit => term) => (bool * term list) option) => code_numeral => code_numeral => (bool * term list) option"
where
  "full_exhaustive_fun' f i d = (full_exhaustive (%(b, t). f (%_. b, %_. Code_Evaluation.Abs (STR ''x'') (Typerep.typerep TYPE('a)) (t ()))) d)
   orelse (if i > 1 then
     full_exhaustive_fun' (%(g, gt). full_exhaustive (%(a, at). full_exhaustive (%(b, bt).
       f (g(a := b),
         (%_. let A = (Typerep.typerep (TYPE('a)));
                  B = (Typerep.typerep (TYPE('b)));
                  fun = (%T U. Typerep.Typerep (STR ''fun'') [T, U])
              in
                Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.App
                  (Code_Evaluation.Const (STR ''Fun.fun_upd'') (fun (fun A B) (fun A (fun B (fun A B)))))
                (gt ())) (at ())) (bt ())))) d) d) (i - 1) d else None)"

definition full_exhaustive_fun :: "(('a => 'b) * (unit => term) => (bool * term list) option) => code_numeral => (bool * term list) option"
where
  "full_exhaustive_fun f d = full_exhaustive_fun' f d d" 

instance ..

end

subsubsection {* A smarter enumeration scheme for functions over finite datatypes *}

class check_all = enum + term_of +
  fixes check_all :: "('a * (unit \<Rightarrow> term) \<Rightarrow> (bool * term list) option) \<Rightarrow> (bool * term list) option"
  fixes enum_term_of :: "'a itself \<Rightarrow> unit \<Rightarrow> term list"
  
fun check_all_n_lists :: "(('a :: check_all) list * (unit \<Rightarrow> term list) \<Rightarrow> (bool * term list) option) \<Rightarrow> code_numeral \<Rightarrow> (bool * term list) option"
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
  "check_all f = check_all (%(x, t1). check_all (%(y, t2). f ((x, y),
    %u. let T1 = (Typerep.typerep (TYPE('a)));
            T2 = (Typerep.typerep (TYPE('b)))
    in Code_Evaluation.App (Code_Evaluation.App (
      Code_Evaluation.Const (STR ''Product_Type.Pair'') 
      (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Product_Type.prod'') [T1, T2]]]))
      (t1 ())) (t2 ()))))"

definition enum_term_of_prod :: "('a * 'b) itself => unit => term list"
where
  "enum_term_of_prod = (%_ _. map (%(x, y).
       let T1 = (Typerep.typerep (TYPE('a)));
           T2 = (Typerep.typerep (TYPE('b)))
       in Code_Evaluation.App (Code_Evaluation.App (
         Code_Evaluation.Const (STR ''Product_Type.Pair'') 
           (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Product_Type.prod'') [T1, T2]]])) x) y)
     (Enum.product (enum_term_of (TYPE('a)) ()) (enum_term_of (TYPE('b)) ())))  "

instance ..

end


instantiation sum :: (check_all, check_all) check_all
begin

definition
  "check_all f = (case check_all (%(a, t). f (Inl a, %_. 
     let T1 = (Typerep.typerep (TYPE('a)));
         T2 = (Typerep.typerep (TYPE('b)))
       in Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inl'') 
           (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])) (t ()))) of Some x' => Some x'
             | None => check_all (%(b, t). f (Inr b, %_. let
                 T1 = (Typerep.typerep (TYPE('a)));
                 T2 = (Typerep.typerep (TYPE('b)))
               in Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inr'') 
                 (Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])) (t ()))))"

definition enum_term_of_sum :: "('a + 'b) itself => unit => term list"
where
  "enum_term_of_sum = (%_ _.
     let
       T1 = (Typerep.typerep (TYPE('a)));
       T2 = (Typerep.typerep (TYPE('b)))
     in
       map (Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inl'') 
             (Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])))
             (enum_term_of (TYPE('a)) ()) @
       map (Code_Evaluation.App (Code_Evaluation.Const (STR ''Sum_Type.Inr'') 
             (Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''Sum_Type.sum'') [T1, T2]])))
             (enum_term_of (TYPE('b)) ()))"

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
  "enum_term_of_option = (% _ _. (Code_Evaluation.term_of (None :: 'a option)) # (map (Code_Evaluation.App (Code_Evaluation.Const (STR ''Option.option.Some'')
      (Typerep.Typerep (STR ''fun'') [Typerep.typerep TYPE('a),  Typerep.Typerep (STR ''Option.option'') [Typerep.typerep TYPE('a)]]))) (enum_term_of (TYPE('a)) ())))"

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

subsection {* Bounded universal quantifiers *}

class bounded_forall =
  fixes bounded_forall :: "('a \<Rightarrow> bool) \<Rightarrow> code_numeral \<Rightarrow> bool"

subsection {* Fast exhaustive combinators *}

class fast_exhaustive = term_of +
  fixes fast_exhaustive :: "('a \<Rightarrow> unit) \<Rightarrow> code_numeral \<Rightarrow> unit"

axiomatization throw_Counterexample :: "term list => unit"
axiomatization catch_Counterexample :: "unit => term list option"

code_const throw_Counterexample
  (Quickcheck "raise (Exhaustive'_Generators.Counterexample _)")
code_const catch_Counterexample
  (Quickcheck "(((_); NONE) handle Exhaustive'_Generators.Counterexample ts => SOME ts)")

subsection {* Continuation passing style functions as plus monad *}
  
type_synonym 'a cps = "('a => term list option) => term list option"

definition cps_empty :: "'a cps"
where
  "cps_empty = (%cont. None)"

definition cps_single :: "'a => 'a cps"
where
  "cps_single v = (%cont. cont v)"

definition cps_bind :: "'a cps => ('a => 'b cps) => 'b cps" 
where
  "cps_bind m f = (%cont. m (%a. (f a) cont))"

definition cps_plus :: "'a cps => 'a cps => 'a cps"
where
  "cps_plus a b = (%c. case a c of None => b c | Some x => Some x)"

definition cps_if :: "bool => unit cps"
where
  "cps_if b = (if b then cps_single () else cps_empty)"

definition cps_not :: "unit cps => unit cps"
where
  "cps_not n = (%c. case n (%u. Some []) of None => c () | Some _ => None)"

type_synonym 'a pos_bound_cps = "('a => (bool * term list) option) => code_numeral => (bool * term list) option"

definition pos_bound_cps_empty :: "'a pos_bound_cps"
where
  "pos_bound_cps_empty = (%cont i. None)"

definition pos_bound_cps_single :: "'a => 'a pos_bound_cps"
where
  "pos_bound_cps_single v = (%cont i. cont v)"

definition pos_bound_cps_bind :: "'a pos_bound_cps => ('a => 'b pos_bound_cps) => 'b pos_bound_cps" 
where
  "pos_bound_cps_bind m f = (%cont i. if i = 0 then None else (m (%a. (f a) cont i) (i - 1)))"

definition pos_bound_cps_plus :: "'a pos_bound_cps => 'a pos_bound_cps => 'a pos_bound_cps"
where
  "pos_bound_cps_plus a b = (%c i. case a c i of None => b c i | Some x => Some x)"

definition pos_bound_cps_if :: "bool => unit pos_bound_cps"
where
  "pos_bound_cps_if b = (if b then pos_bound_cps_single () else pos_bound_cps_empty)"

datatype 'a unknown = Unknown | Known 'a
datatype 'a three_valued = Unknown_value | Value 'a | No_value

type_synonym 'a neg_bound_cps = "('a unknown => term list three_valued) => code_numeral => term list three_valued"

definition neg_bound_cps_empty :: "'a neg_bound_cps"
where
  "neg_bound_cps_empty = (%cont i. No_value)"

definition neg_bound_cps_single :: "'a => 'a neg_bound_cps"
where
  "neg_bound_cps_single v = (%cont i. cont (Known v))"

definition neg_bound_cps_bind :: "'a neg_bound_cps => ('a => 'b neg_bound_cps) => 'b neg_bound_cps" 
where
  "neg_bound_cps_bind m f = (%cont i. if i = 0 then cont Unknown else m (%a. case a of Unknown => cont Unknown | Known a' => f a' cont i) (i - 1))"

definition neg_bound_cps_plus :: "'a neg_bound_cps => 'a neg_bound_cps => 'a neg_bound_cps"
where
  "neg_bound_cps_plus a b = (%c i. case a c i of No_value => b c i | Value x => Value x | Unknown_value => (case b c i of No_value => Unknown_value | Value x => Value x | Unknown_value => Unknown_value))"

definition neg_bound_cps_if :: "bool => unit neg_bound_cps"
where
  "neg_bound_cps_if b = (if b then neg_bound_cps_single () else neg_bound_cps_empty)"

definition neg_bound_cps_not :: "unit pos_bound_cps => unit neg_bound_cps"
where
  "neg_bound_cps_not n = (%c i. case n (%u. Some (True, [])) i of None => c (Known ()) | Some _ => No_value)"

definition pos_bound_cps_not :: "unit neg_bound_cps => unit pos_bound_cps"
where
  "pos_bound_cps_not n = (%c i. case n (%u. Value []) i of No_value => c () | Value _ => None | Unknown_value => None)"

subsection {* Defining combinators for any first-order data type *}

axiomatization unknown :: 'a

notation (output) unknown  ("?")
 
use "Tools/Quickcheck/exhaustive_generators.ML"

setup {* Exhaustive_Generators.setup *}

declare [[quickcheck_batch_tester = exhaustive]]

hide_fact orelse_def
no_notation orelse (infixr "orelse" 55)

hide_fact
  exhaustive'_def
  exhaustive_code_numeral'_def

hide_const (open)
  exhaustive full_exhaustive exhaustive' exhaustive_code_numeral' full_exhaustive_code_numeral'
  throw_Counterexample catch_Counterexample
  check_all enum_term_of
  orelse unknown mk_map_term check_all_n_lists

hide_type (open) cps pos_bound_cps neg_bound_cps unknown three_valued
hide_const (open) cps_empty cps_single cps_bind cps_plus cps_if cps_not
  pos_bound_cps_empty pos_bound_cps_single pos_bound_cps_bind pos_bound_cps_plus pos_bound_cps_if pos_bound_cps_not
  neg_bound_cps_empty neg_bound_cps_single neg_bound_cps_bind neg_bound_cps_plus neg_bound_cps_if neg_bound_cps_not
  Unknown Known Unknown_value Value No_value

end
