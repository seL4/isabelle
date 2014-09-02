(*  Title:      HOL/BNF_Examples/Compat.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Tests for compatibility with the old datatype package.
*)

header \<open> Tests for Compatibility with the Old Datatype Package \<close>

theory Compat
imports Main
begin

subsection \<open> Viewing and Registering New-Style Datatypes as Old-Style Ones \<close>

ML \<open>
fun check_len n xs label =
  length xs = n orelse error ("Expected length " ^ string_of_int (length xs) ^ " for " ^ label);

fun check_lens (n1, n2, n3) (xs1, xs2, xs3) =
  check_len n1 xs1 "old" andalso check_len n2 xs2 "unfold" andalso check_len n3 xs3 "keep";

fun get_descrs thy lens T_name =
  (these (Option.map #descr (Old_Datatype_Data.get_info thy T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy BNF_LFP_Compat.Unfold_Nesting T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy BNF_LFP_Compat.Keep_Nesting T_name)))
  |> tap (check_lens lens);
\<close>

datatype 'a old_lst = Old_Nl | Old_Cns 'a "'a old_lst"

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name old_lst}; \<close>

datatype_new 'a lst = Nl | Cns 'a "'a lst"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name lst}; \<close>

datatype_compat lst

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name lst}; \<close>

datatype_new 'b w = W | W' "'b w \<times> 'b list"

(* no support for sums of products:
datatype_compat w
*)

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name w}; \<close>

datatype_new ('c, 'b) s = L 'c | R 'b

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name s}; \<close>

datatype_new 'd x = X | X' "('d x lst, 'd list) s"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name x}; \<close>

datatype_compat s

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name s}; \<close>
ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name x}; \<close>

datatype_compat x

ML \<open> get_descrs @{theory} (3, 3, 1) @{type_name x}; \<close>

datatype_new 'a tttre = TTTre 'a "'a tttre lst lst lst"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name tttre}; \<close>

datatype_compat tttre

ML \<open> get_descrs @{theory} (4, 4, 1) @{type_name tttre}; \<close>

datatype_new 'a ftre = FEmp | FTre "'a \<Rightarrow> 'a ftre lst"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name ftre}; \<close>

datatype_compat ftre

ML \<open> get_descrs @{theory} (2, 2, 1) @{type_name ftre}; \<close>

datatype_new 'a btre = BTre 'a "'a btre lst" "'a btre lst"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name btre}; \<close>

datatype_compat btre

ML \<open> get_descrs @{theory} (3, 3, 1) @{type_name btre}; \<close>

datatype_new 'a foo = Foo | Foo' 'a "'a bar" and 'a bar = Bar | Bar' 'a "'a foo"

ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name foo}; \<close>
ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name bar}; \<close>

datatype_compat foo bar

ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name foo}; \<close>
ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name bar}; \<close>

datatype_new 'a tre = Tre 'a "'a tre lst"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name tre}; \<close>

datatype_compat tre

ML \<open> get_descrs @{theory} (2, 2, 1) @{type_name tre}; \<close>

fun f_tre and f_tres where
  "f_tre (Tre a ts) = {a} \<union> f_tres ts"
| "f_tres Nl = {}"
| "f_tres (Cns t ts) = f_tres ts"

datatype_new 'a f = F 'a and 'a g = G 'a

ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name f}; \<close>
ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name g}; \<close>

datatype_new h = H "h f" | H'

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name h}; \<close>

datatype_compat f g

ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name f}; \<close>
ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name g}; \<close>
ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name h}; \<close>

datatype_compat h

ML \<open> get_descrs @{theory} (3, 3, 1) @{type_name h}; \<close>

datatype_new myunit = MyUnity

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name myunit}; \<close>

datatype_compat myunit

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name myunit}; \<close>

datatype_new mylist = MyNil | MyCons nat mylist

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name mylist}; \<close>

datatype_compat mylist

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name mylist}; \<close>

fun f_mylist where
  "f_mylist MyNil = 0"
| "f_mylist (MyCons _ xs) = Suc (f_mylist xs)"

datatype_new foo' = FooNil | FooCons bar' foo' and bar' = Bar

ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name foo'}; \<close>
ML \<open> get_descrs @{theory} (0, 2, 2) @{type_name bar'}; \<close>

datatype_compat bar' foo'

ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name foo'}; \<close>
ML \<open> get_descrs @{theory} (2, 2, 2) @{type_name bar'}; \<close>

fun f_foo and f_bar where
  "f_foo FooNil = 0"
| "f_foo (FooCons bar foo) = Suc (f_foo foo) + f_bar bar"
| "f_bar Bar = Suc 0"

locale opt begin

datatype_new 'a opt = Non | Som 'a

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name opt}; \<close>

datatype_compat opt

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name opt}; \<close>

end

datatype funky = Funky "funky tre" | Funky'

ML \<open> get_descrs @{theory} (3, 3, 3) @{type_name funky}; \<close>

datatype fnky = Fnky "nat tre"

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name fnky}; \<close>

datatype_new tree = Tree "tree foo"

ML \<open> get_descrs @{theory} (0, 1, 1) @{type_name tree}; \<close>

datatype_compat tree

ML \<open> get_descrs @{theory} (3, 3, 1) @{type_name tree}; \<close>


subsection \<open> Creating a New-Style Datatype Using an Old-Style Interface \<close>

ML \<open>
val l_specs =
  [((@{binding l}, [("'a", @{sort type})], NoSyn),
   [(@{binding N}, [], NoSyn),
    (@{binding C}, [@{typ 'a}, Type (Sign.full_name @{theory} @{binding l}, [@{typ 'a}])], NoSyn)])];
\<close>

setup \<open> snd o BNF_LFP_Compat.add_datatype BNF_LFP_Compat.Unfold_Nesting l_specs \<close>

ML \<open> get_descrs @{theory} (1, 1, 1) @{type_name l}; \<close>

thm l.exhaust l.map l.induct l.rec l.size

ML \<open>
val t_specs =
  [((@{binding t}, [("'b", @{sort type})], NoSyn),
   [(@{binding T}, [@{typ 'b}, Type (@{type_name l},
       [Type (Sign.full_name @{theory} @{binding t}, [@{typ 'b}])])], NoSyn)])];
\<close>

setup \<open> snd o BNF_LFP_Compat.add_datatype BNF_LFP_Compat.Unfold_Nesting t_specs \<close>

ML \<open> get_descrs @{theory} (2, 2, 1) @{type_name t}; \<close>

thm t.exhaust t.map t.induct t.rec t.size

end
