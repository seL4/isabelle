(*  Title:      HOL/BNF_Examples/Compat.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Tests for compatibility with the old datatype package.
*)

header {* Tests for Compatibility with the Old Datatype Package *}

theory Compat
imports Main
begin

datatype_new 'a lst = Nl | Cns 'a "'a lst"
datatype_compat lst

datatype_new 'b w = W | W' "'b w \<times> 'b list"
(* no support for sums of products
datatype_compat w
*)

datatype_new ('c, 'b) s = L 'c | R 'b
datatype_new 'd x = X | X' "('d x lst, 'd list) s"
datatype_compat s
datatype_compat x

datatype_new 'a tttre = TTTre 'a "'a tttre lst lst lst"
datatype_compat tttre

datatype_new 'a ftre = FEmp | FTre "'a \<Rightarrow> 'a ftre lst"
datatype_compat ftre

datatype_new 'a btre = BTre 'a "'a btre lst" "'a btre lst"
datatype_compat btre

datatype_new 'a foo = Foo | Foo' 'a "'a bar" and 'a bar = Bar | Bar' 'a "'a foo"
datatype_compat foo bar

datatype_new 'a tre = Tre 'a "'a tre lst"
datatype_compat tre

fun f_tre and f_tres where
  "f_tre (Tre a ts) = {a} \<union> f_tres ts"
| "f_tres Nl = {}"
| "f_tres (Cns t ts) = f_tres ts"

datatype_new 'a f = F 'a and 'a g = G 'a
datatype_new h = H "h f" | H'
datatype_compat f g
datatype_compat h

datatype_new myunit = MyUnity
datatype_compat myunit

datatype_new mylist = MyNil | MyCons nat mylist
datatype_compat mylist

fun f_mylist where
  "f_mylist MyNil = 0"
| "f_mylist (MyCons _ xs) = Suc (f_mylist xs)"

datatype_new foo' = FooNil | FooCons bar' foo' and bar' = Bar
datatype_compat bar' foo'

fun f_foo and f_bar where
  "f_foo FooNil = 0"
| "f_foo (FooCons bar foo) = Suc (f_foo foo) + f_bar bar"
| "f_bar Bar = Suc 0"

locale opt begin

datatype_new 'a opt = Non | Som 'a
datatype_compat opt

end

datatype funky = Funky "funky tre" | Funky'
datatype fnky = Fnky "nat tre"

datatype_new tree = Tree "tree foo"
datatype_compat tree

ML {* Datatype_Data.get_info @{theory} @{type_name tree} *}

end
