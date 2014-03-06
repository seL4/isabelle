(*  Title:      HOL/ex/Coercion_Examples.thy
    Author:     Dmitriy Traytel, TU Muenchen

Examples for coercive subtyping via subtype constraints.
*)

theory Coercion_Examples
imports Main
begin

declare[[coercion_enabled]]

(* Error messages test *)

consts func :: "(nat \<Rightarrow> int) \<Rightarrow> nat"
consts arg :: "int \<Rightarrow> nat"
(* Invariant arguments
term "func arg"
*)
(* No subtype relation - constraint
term "(1::nat)::int"
*)
consts func' :: "int \<Rightarrow> int"
consts arg' :: "nat"
(* No subtype relation - function application
term "func' arg'"
*)
(* Uncomparable types in bound
term "arg' = True"
*)
(* Unfullfilled type class requirement
term "1 = True"
*)
(* Different constructors
term "[1::int] = func"
*)

(* Coercion/type maps definitions *)

abbreviation nat_of_bool :: "bool \<Rightarrow> nat"
where
  "nat_of_bool \<equiv> of_bool"

declare [[coercion nat_of_bool]]

declare [[coercion int]]

declare [[coercion_map map]]

definition map_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'd)" where
 "map_fun f g h = g o h o f"

declare [[coercion_map "\<lambda> f g h . g o h o f"]]

primrec map_prod :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a * 'b) \<Rightarrow> ('c * 'd)" where
 "map_prod f g (x,y) = (f x, g y)"

declare [[coercion_map map_prod]]

(* Examples taken from the haskell draft implementation *)

term "(1::nat) = True"

term "True = (1::nat)"

term "(1::nat) = (True = (1::nat))"

term "op = (True = (1::nat))"

term "[1::nat,True]"

term "[True,1::nat]"

term "[1::nat] = [True]"

term "[True] = [1::nat]"

term "[[True]] = [[1::nat]]"

term "[[[[[[[[[[True]]]]]]]]]] = [[[[[[[[[[1::nat]]]]]]]]]]"

term "[[True],[42::nat]] = rev [[True]]"

term "rev [10000::nat] = [False, 420000::nat, True]"

term "\<lambda> x . x = (3::nat)"

term "(\<lambda> x . x = (3::nat)) True"

term "map (\<lambda> x . x = (3::nat))"

term "map (\<lambda> x . x = (3::nat)) [True,1::nat]"

consts bnn :: "(bool \<Rightarrow> nat) \<Rightarrow> nat"
consts nb :: "nat \<Rightarrow> bool"
consts ab :: "'a \<Rightarrow> bool"

term "bnn nb"

term "bnn ab"

term "\<lambda> x . x = (3::int)"

term "map (\<lambda> x . x = (3::int)) [True]"

term "map (\<lambda> x . x = (3::int)) [True,1::nat]"

term "map (\<lambda> x . x = (3::int)) [True,1::nat,1::int]"

term "[1::nat,True,1::int,False]"

term "map (map (\<lambda> x . x = (3::int))) [[True],[1::nat],[True,1::int]]"

consts cbool :: "'a \<Rightarrow> bool"
consts cnat :: "'a \<Rightarrow> nat"
consts cint :: "'a \<Rightarrow> int"

term "[id, cbool, cnat, cint]"

consts funfun :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
consts flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"

term "flip funfun"

term "map funfun [id,cnat,cint,cbool]"

term "map (flip funfun True)"

term "map (flip funfun True) [id,cnat,cint,cbool]"

consts ii :: "int \<Rightarrow> int"
consts aaa :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
consts nlist :: "nat list"
consts ilil :: "int list \<Rightarrow> int list"

term "ii (aaa (1::nat) True)"

term "map ii nlist"

term "ilil nlist"

(***************************************************)

(* Other examples *)

definition xs :: "bool list" where "xs = [True]"

term "(xs::nat list)"

term "(1::nat) = True"

term "True = (1::nat)"

term "int (1::nat)"

term "((True::nat)::int)"

term "1::nat"

term "nat 1"

definition C :: nat
where "C = 123"

consts g :: "int \<Rightarrow> int"
consts h :: "nat \<Rightarrow> nat"

term "(g (1::nat)) + (h 2)"

term "g 1"

term "1+(1::nat)"

term "((1::int) + (1::nat),(1::int))"

definition ys :: "bool list list list list list" where "ys=[[[[[True]]]]]"

term "ys=[[[[[1::nat]]]]]"

typedecl ('a, 'b, 'c) F
consts Fmap :: "('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'c) F \<Rightarrow> ('d, 'b, 'c) F"
consts z :: "(bool, nat, bool) F"
declare [[coercion_map "Fmap :: ('a \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'c) F \<Rightarrow> ('d, 'b, 'c) F"]]
term "z :: (nat, nat, bool) F"

consts
  case_nil :: "'a \<Rightarrow> 'b"
  case_cons :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  case_abs :: "('c \<Rightarrow> 'b) \<Rightarrow> 'b"
  case_elem :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"

declare [[coercion_args case_cons - -]]
declare [[coercion_args case_abs -]]
declare [[coercion_args case_elem - +]]

term "case_cons (case_abs (\<lambda>n. case_abs (\<lambda>is. case_elem (((n::nat),(is::int list))) (n#is)))) case_nil"

consts n :: nat m :: nat
term "- (n + m)"
declare [[coercion_args uminus -]]
declare [[coercion_args plus + +]]
term "- (n + m)"

end
