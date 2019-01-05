(*  Title:      HOL/Datatype_Examples/Compat.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Tests for compatibility with the old datatype package.
*)

section \<open>Tests for Compatibility with the Old Datatype Package\<close>

theory Compat
imports Main
begin

subsection \<open>Viewing and Registering New-Style Datatypes as Old-Style Ones\<close>

ML \<open>
fun check_len n xs label =
  length xs = n orelse error ("Expected length " ^ string_of_int (length xs) ^ " for " ^ label);

fun check_lens (n1, n2, n3) (xs1, xs2, xs3) =
  check_len n1 xs1 "old" andalso check_len n2 xs2 "unfold" andalso check_len n3 xs3 "keep";

fun get_descrs thy lens T_name =
  (these (Option.map #descr (Old_Datatype_Data.get_info thy T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy [] T_name)),
   these (Option.map #descr (BNF_LFP_Compat.get_info thy [BNF_LFP_Compat.Keep_Nesting] T_name)))
  |> tap (check_lens lens);
\<close>

datatype 'b w = W | W' "'b w \<times> 'b list"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>w\<close>\<close>

datatype_compat w

ML \<open>get_descrs \<^theory> (2, 2, 1) \<^type_name>\<open>w\<close>\<close>

datatype ('c, 'b) s = L 'c | R 'b

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>s\<close>\<close>

datatype 'd x = X | X' "('d x list, 'd list) s"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>x\<close>\<close>

datatype_compat s

ML \<open>get_descrs \<^theory> (1, 1, 1) \<^type_name>\<open>s\<close>\<close>
ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>x\<close>\<close>

datatype_compat x

ML \<open>get_descrs \<^theory> (3, 3, 1) \<^type_name>\<open>x\<close>\<close>

thm x.induct x.rec
thm compat_x.induct compat_x.rec

datatype 'a tttre = TTTre 'a "'a tttre list list list"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>tttre\<close>\<close>

datatype_compat tttre

ML \<open>get_descrs \<^theory> (4, 4, 1) \<^type_name>\<open>tttre\<close>\<close>

thm tttre.induct tttre.rec
thm compat_tttre.induct compat_tttre.rec

datatype 'a ftre = FEmp | FTre "'a \<Rightarrow> 'a ftre list"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>ftre\<close>\<close>

datatype_compat ftre

ML \<open>get_descrs \<^theory> (2, 2, 1) \<^type_name>\<open>ftre\<close>\<close>

thm ftre.induct ftre.rec
thm compat_ftre.induct compat_ftre.rec

datatype 'a btre = BTre 'a "'a btre list" "'a btre list"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>btre\<close>\<close>

datatype_compat btre

ML \<open>get_descrs \<^theory> (3, 3, 1) \<^type_name>\<open>btre\<close>\<close>

thm btre.induct btre.rec
thm compat_btre.induct compat_btre.rec

datatype 'a foo = Foo | Foo' 'a "'a bar" and 'a bar = Bar | Bar' 'a "'a foo"

ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>foo\<close>\<close>
ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>bar\<close>\<close>

datatype_compat foo bar

ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>foo\<close>\<close>
ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>bar\<close>\<close>

datatype 'a tre = Tre 'a "'a tre list"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>tre\<close>\<close>

datatype_compat tre

ML \<open>get_descrs \<^theory> (2, 2, 1) \<^type_name>\<open>tre\<close>\<close>

thm tre.induct tre.rec
thm compat_tre.induct compat_tre.rec

datatype 'a f = F 'a and 'a g = G 'a

ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>f\<close>\<close>
ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>g\<close>\<close>

datatype h = H "h f" | H'

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>h\<close>\<close>

datatype_compat f g

ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>f\<close>\<close>
ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>g\<close>\<close>
ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>h\<close>\<close>

datatype_compat h

ML \<open>get_descrs \<^theory> (3, 3, 1) \<^type_name>\<open>h\<close>\<close>

thm h.induct h.rec
thm compat_h.induct compat_h.rec

datatype myunit = MyUnity

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>myunit\<close>\<close>

datatype_compat myunit

ML \<open>get_descrs \<^theory> (1, 1, 1) \<^type_name>\<open>myunit\<close>\<close>

datatype mylist = MyNil | MyCons nat mylist

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>mylist\<close>\<close>

datatype_compat mylist

ML \<open>get_descrs \<^theory> (1, 1, 1) \<^type_name>\<open>mylist\<close>\<close>

datatype foo' = FooNil | FooCons bar' foo' and bar' = Bar

ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>foo'\<close>\<close>
ML \<open>get_descrs \<^theory> (0, 2, 2) \<^type_name>\<open>bar'\<close>\<close>

datatype_compat bar' foo'

ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>foo'\<close>\<close>
ML \<open>get_descrs \<^theory> (2, 2, 2) \<^type_name>\<open>bar'\<close>\<close>

datatype tree = Tree "tree foo"

ML \<open>get_descrs \<^theory> (0, 1, 1) \<^type_name>\<open>tree\<close>\<close>

datatype_compat tree

ML \<open>get_descrs \<^theory> (3, 3, 1) \<^type_name>\<open>tree\<close>\<close>

thm tree.induct tree.rec
thm compat_tree.induct compat_tree.rec


subsection \<open>Creating New-Style Datatypes Using Old-Style Interfaces\<close>

ML \<open>
val l_specs =
  [((\<^binding>\<open>l\<close>, [("'a", \<^sort>\<open>type\<close>)], NoSyn),
   [(\<^binding>\<open>N\<close>, [], NoSyn),
    (\<^binding>\<open>C\<close>, [\<^typ>\<open>'a\<close>, Type (Sign.full_name \<^theory> \<^binding>\<open>l\<close>, [\<^typ>\<open>'a\<close>])],
     NoSyn)])];

Theory.setup (snd o BNF_LFP_Compat.add_datatype [] l_specs);
\<close>

ML \<open>get_descrs \<^theory> (1, 1, 1) \<^type_name>\<open>l\<close>\<close>

thm l.exhaust l.map l.induct l.rec l.size

ML \<open>
val t_specs =
  [((\<^binding>\<open>t\<close>, [("'b", \<^sort>\<open>type\<close>)], NoSyn),
   [(\<^binding>\<open>T\<close>, [\<^typ>\<open>'b\<close>,
       Type (\<^type_name>\<open>l\<close>, [Type (Sign.full_name \<^theory> \<^binding>\<open>t\<close>, [\<^typ>\<open>'b\<close>])])],
     NoSyn)])];

Theory.setup (snd o BNF_LFP_Compat.add_datatype [] t_specs);
\<close>

ML \<open>get_descrs \<^theory> (2, 2, 1) \<^type_name>\<open>t\<close>\<close>

thm t.exhaust t.map t.induct t.rec t.size
thm compat_t.induct compat_t.rec

ML \<open>
val ft_specs =
  [((\<^binding>\<open>ft\<close>, [("'a", \<^sort>\<open>type\<close>)], NoSyn),
   [(\<^binding>\<open>FT0\<close>, [], NoSyn),
    (\<^binding>\<open>FT\<close>, [\<^typ>\<open>'a\<close> --> Type (Sign.full_name \<^theory> \<^binding>\<open>ft\<close>, [\<^typ>\<open>'a\<close>])],
     NoSyn)])];

Theory.setup (snd o BNF_LFP_Compat.add_datatype [] ft_specs);
\<close>

ML \<open>get_descrs \<^theory> (1, 1, 1) \<^type_name>\<open>ft\<close>\<close>

thm ft.exhaust ft.induct ft.rec ft.size
thm compat_ft.induct compat_ft.rec

end
