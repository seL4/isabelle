(*  Title:      HOL/Datatype_Examples/Compat.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Tests for compatibility with the old datatype package.
*)

header {* Tests for Compatibility with the Old Datatype Package *}

theory Compat
imports "~~/src/HOL/Library/Old_Datatype"
begin

subsection {* Viewing and Registering New-Style Datatypes as Old-Style Ones *}

ML {*
fun check_len n xs label =
  length xs = n orelse error ("Expected length " ^ string_of_int (length xs) ^ " for " ^ label);

fun check_lens (n1, n2, n3) (xs1, xs2, xs3) =
  check_len n1 xs1 "old" andalso check_len n2 xs2 "unfold" andalso check_len n3 xs3 "keep";

fun get_descrs thy lens T_name =
  (these (Option.map #descr (Old_Datatype_Data.get_info thy T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy [] T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy [BNF_LFP_Compat.Keep_Nesting] T_name)))
  |> tap (check_lens lens);
*}

old_datatype 'a old_lst = Old_Nl | Old_Cns 'a "'a old_lst"

text {*
A few tests to make sure that @{text old_datatype} works as expected:
*}

primrec old_len :: "'a old_lst \<Rightarrow> nat" where
  "old_len Old_Nl = 0"
| "old_len (Old_Cns _ xs) = Suc (old_len xs)"

export_code old_len checking SML OCaml? Haskell? Scala

lemma "Old_Nl = Old_Cns x xs"
  nitpick (* [expect = genuine] *)
  quickcheck [exhaustive, expect = counterexample]
  quickcheck [random, expect = counterexample]
  quickcheck [narrowing (* , expect = counterexample *)]
  oops

lemma "old_len xs = size xs"
  by (induct xs) auto

ML {* get_descrs @{theory} (1, 1, 1) @{type_name old_lst} *}

datatype 'a lst = Nl | Cns 'a "'a lst"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name lst} *}

datatype_compat lst

ML {* get_descrs @{theory} (1, 1, 1) @{type_name lst} *}

datatype 'b w = W | W' "'b w \<times> 'b list"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name w} *}

datatype_compat w

ML {* get_descrs @{theory} (2, 2, 1) @{type_name w} *}

datatype ('c, 'b) s = L 'c | R 'b

ML {* get_descrs @{theory} (0, 1, 1) @{type_name s} *}

datatype 'd x = X | X' "('d x lst, 'd list) s"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name x} *}

datatype_compat s

ML {* get_descrs @{theory} (1, 1, 1) @{type_name s} *}
ML {* get_descrs @{theory} (0, 1, 1) @{type_name x} *}

datatype_compat x

ML {* get_descrs @{theory} (3, 3, 1) @{type_name x} *}

thm x.induct x.rec
thm compat_x.induct compat_x.rec

datatype 'a tttre = TTTre 'a "'a tttre lst lst lst"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name tttre} *}

datatype_compat tttre

ML {* get_descrs @{theory} (4, 4, 1) @{type_name tttre} *}

thm tttre.induct tttre.rec
thm compat_tttre.induct compat_tttre.rec

datatype 'a ftre = FEmp | FTre "'a \<Rightarrow> 'a ftre lst"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name ftre} *}

datatype_compat ftre

ML {* get_descrs @{theory} (2, 2, 1) @{type_name ftre} *}

thm ftre.induct ftre.rec
thm compat_ftre.induct compat_ftre.rec

datatype 'a btre = BTre 'a "'a btre lst" "'a btre lst"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name btre} *}

datatype_compat btre

ML {* get_descrs @{theory} (3, 3, 1) @{type_name btre} *}

thm btre.induct btre.rec
thm compat_btre.induct compat_btre.rec

datatype 'a foo = Foo | Foo' 'a "'a bar" and 'a bar = Bar | Bar' 'a "'a foo"

ML {* get_descrs @{theory} (0, 2, 2) @{type_name foo} *}
ML {* get_descrs @{theory} (0, 2, 2) @{type_name bar} *}

datatype_compat foo bar

ML {* get_descrs @{theory} (2, 2, 2) @{type_name foo} *}
ML {* get_descrs @{theory} (2, 2, 2) @{type_name bar} *}

datatype 'a tre = Tre 'a "'a tre lst"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name tre} *}

datatype_compat tre

ML {* get_descrs @{theory} (2, 2, 1) @{type_name tre} *}

thm tre.induct tre.rec
thm compat_tre.induct compat_tre.rec

datatype 'a f = F 'a and 'a g = G 'a

ML {* get_descrs @{theory} (0, 2, 2) @{type_name f} *}
ML {* get_descrs @{theory} (0, 2, 2) @{type_name g} *}

datatype h = H "h f" | H'

ML {* get_descrs @{theory} (0, 1, 1) @{type_name h} *}

datatype_compat f g

ML {* get_descrs @{theory} (2, 2, 2) @{type_name f} *}
ML {* get_descrs @{theory} (2, 2, 2) @{type_name g} *}
ML {* get_descrs @{theory} (0, 1, 1) @{type_name h} *}

datatype_compat h

ML {* get_descrs @{theory} (3, 3, 1) @{type_name h} *}

thm h.induct h.rec
thm compat_h.induct compat_h.rec

datatype myunit = MyUnity

ML {* get_descrs @{theory} (0, 1, 1) @{type_name myunit} *}

datatype_compat myunit

ML {* get_descrs @{theory} (1, 1, 1) @{type_name myunit} *}

datatype mylist = MyNil | MyCons nat mylist

ML {* get_descrs @{theory} (0, 1, 1) @{type_name mylist} *}

datatype_compat mylist

ML {* get_descrs @{theory} (1, 1, 1) @{type_name mylist} *}

datatype foo' = FooNil | FooCons bar' foo' and bar' = Bar

ML {* get_descrs @{theory} (0, 2, 2) @{type_name foo'} *}
ML {* get_descrs @{theory} (0, 2, 2) @{type_name bar'} *}

datatype_compat bar' foo'

ML {* get_descrs @{theory} (2, 2, 2) @{type_name foo'} *}
ML {* get_descrs @{theory} (2, 2, 2) @{type_name bar'} *}

old_datatype funky = Funky "funky tre" | Funky'

ML {* get_descrs @{theory} (3, 3, 3) @{type_name funky} *}

old_datatype fnky = Fnky "nat tre"

ML {* get_descrs @{theory} (1, 1, 1) @{type_name fnky} *}

datatype tree = Tree "tree foo"

ML {* get_descrs @{theory} (0, 1, 1) @{type_name tree} *}

datatype_compat tree

ML {* get_descrs @{theory} (3, 3, 1) @{type_name tree} *}

thm tree.induct tree.rec
thm compat_tree.induct compat_tree.rec


subsection {* Creating New-Style Datatypes Using Old-Style Interfaces *}

ML {*
val l_specs =
  [((@{binding l}, [("'a", @{sort type})], NoSyn),
   [(@{binding N}, [], NoSyn),
    (@{binding C}, [@{typ 'a}, Type (Sign.full_name @{theory} @{binding l}, [@{typ 'a}])],
     NoSyn)])];
*}

setup {* snd o BNF_LFP_Compat.add_datatype [] l_specs *}

ML {* get_descrs @{theory} (1, 1, 1) @{type_name l} *}

thm l.exhaust l.map l.induct l.rec l.size

ML {*
val t_specs =
  [((@{binding t}, [("'b", @{sort type})], NoSyn),
   [(@{binding T}, [@{typ 'b},
       Type (@{type_name l}, [Type (Sign.full_name @{theory} @{binding t}, [@{typ 'b}])])],
     NoSyn)])];
*}

setup {* snd o BNF_LFP_Compat.add_datatype [] t_specs *}

ML {* get_descrs @{theory} (2, 2, 1) @{type_name t} *}

thm t.exhaust t.map t.induct t.rec t.size
thm compat_t.induct compat_t.rec

ML {*
val ft_specs =
  [((@{binding ft}, [("'a", @{sort type})], NoSyn),
   [(@{binding FT0}, [], NoSyn),
    (@{binding FT}, [@{typ 'a} --> Type (Sign.full_name @{theory} @{binding ft}, [@{typ 'a}])],
     NoSyn)])];
*}

setup {* snd o BNF_LFP_Compat.add_datatype [] ft_specs *}

ML {* get_descrs @{theory} (1, 1, 1) @{type_name ft} *}

thm ft.exhaust ft.induct ft.rec ft.size
thm compat_ft.induct compat_ft.rec

end
