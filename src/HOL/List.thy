(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* The datatype of finite lists *}

theory List = PreList:

datatype 'a list =
    Nil    ("[]")
  | Cons 'a  "'a list"    (infixr "#" 65)

consts
  "@" :: "'a list => 'a list => 'a list"    (infixr 65)
  filter:: "('a => bool) => 'a list => 'a list"
  concat:: "'a list list => 'a list"
  foldl :: "('b => 'a => 'b) => 'b => 'a list => 'b"
  foldr :: "('a => 'b => 'b) => 'a list => 'b => 'b"
  hd:: "'a list => 'a"
  tl:: "'a list => 'a list"
  last:: "'a list => 'a"
  butlast :: "'a list => 'a list"
  set :: "'a list => 'a set"
  list_all:: "('a => bool) => ('a list => bool)"
  list_all2 :: "('a => 'b => bool) => 'a list => 'b list => bool"
  map :: "('a=>'b) => ('a list => 'b list)"
  mem :: "'a => 'a list => bool"    (infixl 55)
  nth :: "'a list => nat => 'a"    (infixl "!" 100)
  list_update :: "'a list => nat => 'a => 'a list"
  take:: "nat => 'a list => 'a list"
  drop:: "nat => 'a list => 'a list"
  takeWhile :: "('a => bool) => 'a list => 'a list"
  dropWhile :: "('a => bool) => 'a list => 'a list"
  rev :: "'a list => 'a list"
  zip :: "'a list => 'b list => ('a * 'b) list"
  upt :: "nat => nat => nat list" ("(1[_../_'(])")
  remdups :: "'a list => 'a list"
  null:: "'a list => bool"
  "distinct":: "'a list => bool"
  replicate :: "nat => 'a => 'a list"

nonterminals lupdbinds lupdbind

syntax
  -- {* list Enumeration *}
  "@list" :: "args => 'a list"    ("[(_)]")

  -- {* Special syntax for filter *}
  "@filter" :: "[pttrn, 'a list, bool] => 'a list"    ("(1[_:_./ _])")

  -- {* list update *}
  "_lupdbind":: "['a, 'a] => lupdbind"    ("(2_ :=/ _)")
  "" :: "lupdbind => lupdbinds"    ("_")
  "_lupdbinds" :: "[lupdbind, lupdbinds] => lupdbinds"    ("_,/ _")
  "_LUpdate" :: "['a, lupdbinds] => 'a"    ("_/[(_)]" [900,0] 900)

  upto:: "nat => nat => nat list"    ("(1[_../_])")

translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
  "[x:xs . P]"== "filter (%x. P) xs"

  "_LUpdate xs (_lupdbinds b bs)"== "_LUpdate (_LUpdate xs b) bs"
  "xs[i:=x]" == "list_update xs i x"

  "[i..j]" == "[i..(Suc j)(]"


syntax (xsymbols)
  "@filter" :: "[pttrn, 'a list, bool] => 'a list"("(1[_\<in>_ ./ _])")


text {*
  Function @{text size} is overloaded for all datatypes.Users may
  refer to the list version as @{text length}. *}

syntax length :: "'a list => nat"
translations "length" => "size :: _ list => nat"

typed_print_translation {*
  let
    fun size_tr' _ (Type ("fun", (Type ("list", _) :: _))) [t] =
          Syntax.const "length" $ t
      | size_tr' _ _ _ = raise Match;
  in [("size", size_tr')] end
*}

primrec
"hd(x#xs) = x"
primrec
"tl([]) = []"
"tl(x#xs) = xs"
primrec
"null([]) = True"
"null(x#xs) = False"
primrec
"last(x#xs) = (if xs=[] then x else last xs)"
primrec
"butlast []= []"
"butlast(x#xs) = (if xs=[] then [] else x#butlast xs)"
primrec
"x mem [] = False"
"x mem (y#ys) = (if y=x then True else x mem ys)"
primrec
"set [] = {}"
"set (x#xs) = insert x (set xs)"
primrec
list_all_Nil:"list_all P [] = True"
list_all_Cons: "list_all P (x#xs) = (P(x) \<and> list_all P xs)"
primrec
"map f [] = []"
"map f (x#xs) = f(x)#map f xs"
primrec
append_Nil:"[]@ys = ys"
append_Cons: "(x#xs)@ys = x#(xs@ys)"
primrec
"rev([]) = []"
"rev(x#xs) = rev(xs) @ [x]"
primrec
"filter P [] = []"
"filter P (x#xs) = (if P x then x#filter P xs else filter P xs)"
primrec
foldl_Nil:"foldl f a [] = a"
foldl_Cons: "foldl f a (x#xs) = foldl f (f a x) xs"
primrec
"foldr f [] a = a"
"foldr f (x#xs) a = f x (foldr f xs a)"
primrec
"concat([]) = []"
"concat(x#xs) = x @ concat(xs)"
primrec
drop_Nil:"drop n [] = []"
drop_Cons: "drop n (x#xs) = (case n of 0 => x#xs | Suc(m) => drop m xs)"
-- {* Warning: simpset does not contain this definition *}
-- {* but separate theorems for @{text "n = 0"} and @{text "n = Suc k"} *}
primrec
take_Nil:"take n [] = []"
take_Cons: "take n (x#xs) = (case n of 0 => [] | Suc(m) => x # take m xs)"
-- {* Warning: simpset does not contain this definition *}
-- {* but separate theorems for @{text "n = 0"} and @{text "n = Suc k"} *}
primrec
nth_Cons:"(x#xs)!n = (case n of 0 => x | (Suc k) => xs!k)"
-- {* Warning: simpset does not contain this definition *}
-- {* but separate theorems for @{text "n = 0"} and @{text "n = Suc k"} *}
primrec
"[][i:=v] = []"
"(x#xs)[i:=v] =
(case i of 0 => v # xs
| Suc j => x # xs[j:=v])"
primrec
"takeWhile P [] = []"
"takeWhile P (x#xs) = (if P x then x#takeWhile P xs else [])"
primrec
"dropWhile P [] = []"
"dropWhile P (x#xs) = (if P x then dropWhile P xs else x#xs)"
primrec
"zip xs [] = []"
zip_Cons: "zip xs (y#ys) = (case xs of [] => [] | z#zs => (z,y)#zip zs ys)"
-- {* Warning: simpset does not contain this definition *}
-- {* but separate theorems for @{text "xs = []"} and @{text "xs = z # zs"} *}
primrec
upt_0: "[i..0(] = []"
upt_Suc: "[i..(Suc j)(] = (if i <= j then [i..j(] @ [j] else [])"
primrec
"distinct [] = True"
"distinct (x#xs) = (x ~: set xs \<and> distinct xs)"
primrec
"remdups [] = []"
"remdups (x#xs) = (if x : set xs then remdups xs else x # remdups xs)"
primrec
replicate_0: "replicate 0 x = []"
replicate_Suc: "replicate (Suc n) x = x # replicate n x"
defs
 list_all2_def:
 "list_all2 P xs ys == length xs = length ys \<and> (\<forall>(x, y) \<in> set (zip xs ys). P x y)"


subsection {* Lexicographic orderings on lists *}

consts
lexn :: "('a * 'a)set => nat => ('a list * 'a list)set"
primrec
"lexn r 0 = {}"
"lexn r (Suc n) =
(prod_fun (%(x,xs). x#xs) (%(x,xs). x#xs) ` (r <*lex*> lexn r n)) Int
{(xs,ys). length xs = Suc n \<and> length ys = Suc n}"

constdefs
lex :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
"lex r == \<Union>n. lexn r n"

lexico :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
"lexico r == inv_image (less_than <*lex*> lex r) (%xs. (length xs, xs))"

sublist :: "'a list => nat set => 'a list"
"sublist xs A == map fst (filter (%p. snd p : A) (zip xs [0..size xs(]))"


lemma not_Cons_self [simp]: "xs \<noteq> x # xs"
by (induct xs) auto

lemmas not_Cons_self2 [simp] = not_Cons_self [symmetric]

lemma neq_Nil_conv: "(xs \<noteq> []) = (\<exists>y ys. xs = y # ys)"
by (induct xs) auto

lemma length_induct:
"(!!xs. \<forall>ys. length ys < length xs --> P ys ==> P xs) ==> P xs"
by (rule measure_induct [of length]) rules


subsection {* @{text lists}: the list-forming operator over sets *}

consts lists :: "'a set => 'a list set"
inductive "lists A"
intros
Nil [intro!]: "[]: lists A"
Cons [intro!]: "[| a: A;l: lists A|] ==> a#l : lists A"

inductive_cases listsE [elim!]: "x#l : lists A"

lemma lists_mono [mono]: "A \<subseteq> B ==> lists A \<subseteq> lists B"
by (unfold lists.defs) (blast intro!: lfp_mono)

lemma lists_IntI [rule_format]:
"l: lists A ==> l: lists B --> l: lists (A Int B)"
apply (erule lists.induct)
apply blast+
done

lemma lists_Int_eq [simp]: "lists (A \<inter> B) = lists A \<inter> lists B"
apply (rule mono_Int [THEN equalityI])
apply (simp add: mono_def lists_mono)
apply (blast intro!: lists_IntI)
done

lemma append_in_lists_conv [iff]:
"(xs @ ys : lists A) = (xs : lists A \<and> ys : lists A)"
by (induct xs) auto


subsection {* @{text length} *}

text {*
Needs to come before @{text "@"} because of theorem @{text
append_eq_append_conv}.
*}

lemma length_append [simp]: "length (xs @ ys) = length xs + length ys"
by (induct xs) auto

lemma length_map [simp]: "length (map f xs) = length xs"
by (induct xs) auto

lemma length_rev [simp]: "length (rev xs) = length xs"
by (induct xs) auto

lemma length_tl [simp]: "length (tl xs) = length xs - 1"
by (cases xs) auto

lemma length_0_conv [iff]: "(length xs = 0) = (xs = [])"
by (induct xs) auto

lemma length_greater_0_conv [iff]: "(0 < length xs) = (xs \<noteq> [])"
by (induct xs) auto

lemma length_Suc_conv:
"(length xs = Suc n) = (\<exists>y ys. xs = y # ys \<and> length ys = n)"
by (induct xs) auto


subsection {* @{text "@"} -- append *}

lemma append_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
by (induct xs) auto

lemma append_Nil2 [simp]: "xs @ [] = xs"
by (induct xs) auto

lemma append_is_Nil_conv [iff]: "(xs @ ys = []) = (xs = [] \<and> ys = [])"
by (induct xs) auto

lemma Nil_is_append_conv [iff]: "([] = xs @ ys) = (xs = [] \<and> ys = [])"
by (induct xs) auto

lemma append_self_conv [iff]: "(xs @ ys = xs) = (ys = [])"
by (induct xs) auto

lemma self_append_conv [iff]: "(xs = xs @ ys) = (ys = [])"
by (induct xs) auto

lemma append_eq_append_conv [rule_format, simp]:
 "\<forall>ys. length xs = length ys \<or> length us = length vs
 --> (xs@us = ys@vs) = (xs=ys \<and> us=vs)"
apply (induct_tac xs)
 apply(rule allI)
 apply (case_tac ys)
apply simp
 apply force
apply (rule allI)
apply (case_tac ys)
 apply force
apply simp
done

lemma same_append_eq [iff]: "(xs @ ys = xs @ zs) = (ys = zs)"
by simp

lemma append1_eq_conv [iff]: "(xs @ [x] = ys @ [y]) = (xs = ys \<and> x = y)"
by simp

lemma append_same_eq [iff]: "(ys @ xs = zs @ xs) = (ys = zs)"
by simp

lemma append_self_conv2 [iff]: "(xs @ ys = ys) = (xs = [])"
using append_same_eq [of _ _ "[]"] by auto

lemma self_append_conv2 [iff]: "(ys = xs @ ys) = (xs = [])"
using append_same_eq [of "[]"] by auto

lemma hd_Cons_tl [simp]: "xs \<noteq> [] ==> hd xs # tl xs = xs"
by (induct xs) auto

lemma hd_append: "hd (xs @ ys) = (if xs = [] then hd ys else hd xs)"
by (induct xs) auto

lemma hd_append2 [simp]: "xs \<noteq> [] ==> hd (xs @ ys) = hd xs"
by (simp add: hd_append split: list.split)

lemma tl_append: "tl (xs @ ys) = (case xs of [] => tl ys | z#zs => zs @ ys)"
by (simp split: list.split)

lemma tl_append2 [simp]: "xs \<noteq> [] ==> tl (xs @ ys) = tl xs @ ys"
by (simp add: tl_append split: list.split)


text {* Trivial rules for solving @{text "@"}-equations automatically. *}

lemma eq_Nil_appendI: "xs = ys ==> xs = [] @ ys"
by simp

lemma Cons_eq_appendI:
"[| x # xs1 = ys; xs = xs1 @ zs |] ==> x # xs = ys @ zs"
by (drule sym) simp

lemma append_eq_appendI:
"[| xs @ xs1 = zs; ys = xs1 @ us |] ==> xs @ ys = zs @ us"
by (drule sym) simp


text {*
Simplification procedure for all list equalities.
Currently only tries to rearrange @{text "@"} to see if
- both lists end in a singleton list,
- or both lists end in the same list.
*}

ML_setup {*
local

val append_assoc = thm "append_assoc";
val append_Nil = thm "append_Nil";
val append_Cons = thm "append_Cons";
val append1_eq_conv = thm "append1_eq_conv";
val append_same_eq = thm "append_same_eq";

fun last (cons as Const("List.list.Cons",_) $ _ $ xs) =
  (case xs of Const("List.list.Nil",_) => cons | _ => last xs)
  | last (Const("List.op @",_) $ _ $ ys) = last ys
  | last t = t;

fun list1 (Const("List.list.Cons",_) $ _ $ Const("List.list.Nil",_)) = true
  | list1 _ = false;

fun butlast ((cons as Const("List.list.Cons",_) $ x) $ xs) =
  (case xs of Const("List.list.Nil",_) => xs | _ => cons $ butlast xs)
  | butlast ((app as Const("List.op @",_) $ xs) $ ys) = app $ butlast ys
  | butlast xs = Const("List.list.Nil",fastype_of xs);

val rearr_tac =
  simp_tac (HOL_basic_ss addsimps [append_assoc, append_Nil, append_Cons]);

fun list_eq sg _ (F as (eq as Const(_,eqT)) $ lhs $ rhs) =
  let
    val lastl = last lhs and lastr = last rhs;
    fun rearr conv =
      let
        val lhs1 = butlast lhs and rhs1 = butlast rhs;
        val Type(_,listT::_) = eqT
        val appT = [listT,listT] ---> listT
        val app = Const("List.op @",appT)
        val F2 = eq $ (app$lhs1$lastl) $ (app$rhs1$lastr)
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (F,F2));
        val thm = Tactic.prove sg [] [] eq (K (rearr_tac 1));
      in Some ((conv RS (thm RS trans)) RS eq_reflection) end;

  in
    if list1 lastl andalso list1 lastr then rearr append1_eq_conv
    else if lastl aconv lastr then rearr append_same_eq
    else None
  end;

in

val list_eq_simproc =
  Simplifier.simproc (Theory.sign_of (the_context ())) "list_eq" ["(xs::'a list) = ys"] list_eq;

end;

Addsimprocs [list_eq_simproc];
*}


subsection {* @{text map} *}

lemma map_ext: "(!!x. x : set xs --> f x = g x) ==> map f xs = map g xs"
by (induct xs) simp_all

lemma map_ident [simp]: "map (\<lambda>x. x) = (\<lambda>xs. xs)"
by (rule ext, induct_tac xs) auto

lemma map_append [simp]: "map f (xs @ ys) = map f xs @ map f ys"
by (induct xs) auto

lemma map_compose: "map (f o g) xs = map f (map g xs)"
by (induct xs) (auto simp add: o_def)

lemma rev_map: "rev (map f xs) = map f (rev xs)"
by (induct xs) auto

lemma map_cong [recdef_cong]:
"xs = ys ==> (!!x. x : set ys ==> f x = g x) ==> map f xs = map g ys"
-- {* a congruence rule for @{text map} *}
by (clarify, induct ys) auto

lemma map_is_Nil_conv [iff]: "(map f xs = []) = (xs = [])"
by (cases xs) auto

lemma Nil_is_map_conv [iff]: "([] = map f xs) = (xs = [])"
by (cases xs) auto

lemma map_eq_Cons:
"(map f xs = y # ys) = (\<exists>x xs'. xs = x # xs' \<and> f x = y \<and> map f xs' = ys)"
by (cases xs) auto

lemma map_injective:
"!!xs. map f xs = map f ys ==> (\<forall>x y. f x = f y --> x = y) ==> xs = ys"
by (induct ys) (auto simp add: map_eq_Cons)

lemma inj_mapI: "inj f ==> inj (map f)"
by (rules dest: map_injective injD intro: inj_onI)

lemma inj_mapD: "inj (map f) ==> inj f"
apply (unfold inj_on_def)
apply clarify
apply (erule_tac x = "[x]" in ballE)
 apply (erule_tac x = "[y]" in ballE)
apply simp
 apply blast
apply blast
done

lemma inj_map: "inj (map f) = inj f"
by (blast dest: inj_mapD intro: inj_mapI)


subsection {* @{text rev} *}

lemma rev_append [simp]: "rev (xs @ ys) = rev ys @ rev xs"
by (induct xs) auto

lemma rev_rev_ident [simp]: "rev (rev xs) = xs"
by (induct xs) auto

lemma rev_is_Nil_conv [iff]: "(rev xs = []) = (xs = [])"
by (induct xs) auto

lemma Nil_is_rev_conv [iff]: "([] = rev xs) = (xs = [])"
by (induct xs) auto

lemma rev_is_rev_conv [iff]: "!!ys. (rev xs = rev ys) = (xs = ys)"
apply (induct xs)
 apply force
apply (case_tac ys)
 apply simp
apply force
done

lemma rev_induct [case_names Nil snoc]:
  "[| P []; !!x xs. P xs ==> P (xs @ [x]) |] ==> P xs"
apply(subst rev_rev_ident[symmetric])
apply(rule_tac list = "rev xs" in list.induct, simp_all)
done

ML {* val rev_induct_tac = induct_thm_tac (thm "rev_induct") *}-- "compatibility"

lemma rev_exhaust [case_names Nil snoc]:
  "(xs = [] ==> P) ==>(!!ys y. xs = ys @ [y] ==> P) ==> P"
by (induct xs rule: rev_induct) auto

lemmas rev_cases = rev_exhaust


subsection {* @{text set} *}

lemma finite_set [iff]: "finite (set xs)"
by (induct xs) auto

lemma set_append [simp]: "set (xs @ ys) = (set xs \<union> set ys)"
by (induct xs) auto

lemma set_subset_Cons: "set xs \<subseteq> set (x # xs)"
by auto

lemma set_empty [iff]: "(set xs = {}) = (xs = [])"
by (induct xs) auto

lemma set_rev [simp]: "set (rev xs) = set xs"
by (induct xs) auto

lemma set_map [simp]: "set (map f xs) = f`(set xs)"
by (induct xs) auto

lemma set_filter [simp]: "set (filter P xs) = {x. x : set xs \<and> P x}"
by (induct xs) auto

lemma set_upt [simp]: "set[i..j(] = {k. i \<le> k \<and> k < j}"
apply (induct j)
 apply simp_all
apply(erule ssubst)
apply auto
done

lemma in_set_conv_decomp: "(x : set xs) = (\<exists>ys zs. xs = ys @ x # zs)"
apply (induct xs)
 apply simp
apply simp
apply (rule iffI)
 apply (blast intro: eq_Nil_appendI Cons_eq_appendI)
apply (erule exE)+
apply (case_tac ys)
apply auto
done

lemma in_lists_conv_set: "(xs : lists A) = (\<forall>x \<in> set xs. x : A)"
-- {* eliminate @{text lists} in favour of @{text set} *}
by (induct xs) auto

lemma in_listsD [dest!]: "xs \<in> lists A ==> \<forall>x\<in>set xs. x \<in> A"
by (rule in_lists_conv_set [THEN iffD1])

lemma in_listsI [intro!]: "\<forall>x\<in>set xs. x \<in> A ==> xs \<in> lists A"
by (rule in_lists_conv_set [THEN iffD2])

lemma finite_list: "finite A ==> EX l. set l = A"
apply (erule finite_induct, auto)
apply (rule_tac x="x#l" in exI, auto)
done


subsection {* @{text mem} *}

lemma set_mem_eq: "(x mem xs) = (x : set xs)"
by (induct xs) auto


subsection {* @{text list_all} *}

lemma list_all_conv: "list_all P xs = (\<forall>x \<in> set xs. P x)"
by (induct xs) auto

lemma list_all_append [simp]:
"list_all P (xs @ ys) = (list_all P xs \<and> list_all P ys)"
by (induct xs) auto


subsection {* @{text filter} *}

lemma filter_append [simp]: "filter P (xs @ ys) = filter P xs @ filter P ys"
by (induct xs) auto

lemma filter_filter [simp]: "filter P (filter Q xs) = filter (\<lambda>x. Q x \<and> P x) xs"
by (induct xs) auto

lemma filter_True [simp]: "\<forall>x \<in> set xs. P x ==> filter P xs = xs"
by (induct xs) auto

lemma filter_False [simp]: "\<forall>x \<in> set xs. \<not> P x ==> filter P xs = []"
by (induct xs) auto

lemma length_filter [simp]: "length (filter P xs) \<le> length xs"
by (induct xs) (auto simp add: le_SucI)

lemma filter_is_subset [simp]: "set (filter P xs) \<le> set xs"
by auto


subsection {* @{text concat} *}

lemma concat_append [simp]: "concat (xs @ ys) = concat xs @ concat ys"
by (induct xs) auto

lemma concat_eq_Nil_conv [iff]: "(concat xss = []) = (\<forall>xs \<in> set xss. xs = [])"
by (induct xss) auto

lemma Nil_eq_concat_conv [iff]: "([] = concat xss) = (\<forall>xs \<in> set xss. xs = [])"
by (induct xss) auto

lemma set_concat [simp]: "set (concat xs) = \<Union>(set ` set xs)"
by (induct xs) auto

lemma map_concat: "map f (concat xs) = concat (map (map f) xs)"
by (induct xs) auto

lemma filter_concat: "filter p (concat xs) = concat (map (filter p) xs)"
by (induct xs) auto

lemma rev_concat: "rev (concat xs) = concat (map rev (rev xs))"
by (induct xs) auto


subsection {* @{text nth} *}

lemma nth_Cons_0 [simp]: "(x # xs)!0 = x"
by auto

lemma nth_Cons_Suc [simp]: "(x # xs)!(Suc n) = xs!n"
by auto

declare nth.simps [simp del]

lemma nth_append:
"!!n. (xs @ ys)!n = (if n < length xs then xs!n else ys!(n - length xs))"
apply(induct "xs")
 apply simp
apply (case_tac n)
 apply auto
done

lemma nth_map [simp]: "!!n. n < length xs ==> (map f xs)!n = f(xs!n)"
apply(induct xs)
 apply simp
apply (case_tac n)
 apply auto
done

lemma set_conv_nth: "set xs = {xs!i | i. i < length xs}"
apply (induct_tac xs)
 apply simp
apply simp
apply safe
apply (rule_tac x = 0 in exI)
apply simp
 apply (rule_tac x = "Suc i" in exI)
 apply simp
apply (case_tac i)
 apply simp
apply (rename_tac j)
apply (rule_tac x = j in exI)
apply simp
done

lemma list_ball_nth: "[| n < length xs; !x : set xs. P x|] ==> P(xs!n)"
by (auto simp add: set_conv_nth)

lemma nth_mem [simp]: "n < length xs ==> xs!n : set xs"
by (auto simp add: set_conv_nth)

lemma all_nth_imp_all_set:
"[| !i < length xs. P(xs!i); x : set xs|] ==> P x"
by (auto simp add: set_conv_nth)

lemma all_set_conv_all_nth:
"(\<forall>x \<in> set xs. P x) = (\<forall>i. i < length xs --> P (xs ! i))"
by (auto simp add: set_conv_nth)


subsection {* @{text list_update} *}

lemma length_list_update [simp]: "!!i. length(xs[i:=x]) = length xs"
by (induct xs) (auto split: nat.split)

lemma nth_list_update:
"!!i j. i < length xs==> (xs[i:=x])!j = (if i = j then x else xs!j)"
by (induct xs) (auto simp add: nth_Cons split: nat.split)

lemma nth_list_update_eq [simp]: "i < length xs ==> (xs[i:=x])!i = x"
by (simp add: nth_list_update)

lemma nth_list_update_neq [simp]: "!!i j. i \<noteq> j ==> xs[i:=x]!j = xs!j"
by (induct xs) (auto simp add: nth_Cons split: nat.split)

lemma list_update_overwrite [simp]:
"!!i. i < size xs ==> xs[i:=x, i:=y] = xs[i:=y]"
by (induct xs) (auto split: nat.split)

lemma list_update_same_conv:
"!!i. i < length xs ==> (xs[i := x] = xs) = (xs!i = x)"
by (induct xs) (auto split: nat.split)

lemma update_zip:
"!!i xy xs. length xs = length ys ==>
(zip xs ys)[i:=xy] = zip (xs[i:=fst xy]) (ys[i:=snd xy])"
by (induct ys) (auto, case_tac xs, auto split: nat.split)

lemma set_update_subset_insert: "!!i. set(xs[i:=x]) <= insert x (set xs)"
by (induct xs) (auto split: nat.split)

lemma set_update_subsetI: "[| set xs <= A; x:A |] ==> set(xs[i := x]) <= A"
by (blast dest!: set_update_subset_insert [THEN subsetD])


subsection {* @{text last} and @{text butlast} *}

lemma last_snoc [simp]: "last (xs @ [x]) = x"
by (induct xs) auto

lemma butlast_snoc [simp]: "butlast (xs @ [x]) = xs"
by (induct xs) auto

lemma length_butlast [simp]: "length (butlast xs) = length xs - 1"
by (induct xs rule: rev_induct) auto

lemma butlast_append:
"!!ys. butlast (xs @ ys) = (if ys = [] then butlast xs else xs @ butlast ys)"
by (induct xs) auto

lemma append_butlast_last_id [simp]:
"xs \<noteq> [] ==> butlast xs @ [last xs] = xs"
by (induct xs) auto

lemma in_set_butlastD: "x : set (butlast xs) ==> x : set xs"
by (induct xs) (auto split: split_if_asm)

lemma in_set_butlast_appendI:
"x : set (butlast xs) | x : set (butlast ys) ==> x : set (butlast (xs @ ys))"
by (auto dest: in_set_butlastD simp add: butlast_append)


subsection {* @{text take} and @{text drop} *}

lemma take_0 [simp]: "take 0 xs = []"
by (induct xs) auto

lemma drop_0 [simp]: "drop 0 xs = xs"
by (induct xs) auto

lemma take_Suc_Cons [simp]: "take (Suc n) (x # xs) = x # take n xs"
by simp

lemma drop_Suc_Cons [simp]: "drop (Suc n) (x # xs) = drop n xs"
by simp

declare take_Cons [simp del] and drop_Cons [simp del]

lemma length_take [simp]: "!!xs. length (take n xs) = min (length xs) n"
by (induct n) (auto, case_tac xs, auto)

lemma length_drop [simp]: "!!xs. length (drop n xs) = (length xs - n)"
by (induct n) (auto, case_tac xs, auto)

lemma take_all [simp]: "!!xs. length xs <= n ==> take n xs = xs"
by (induct n) (auto, case_tac xs, auto)

lemma drop_all [simp]: "!!xs. length xs <= n ==> drop n xs = []"
by (induct n) (auto, case_tac xs, auto)

lemma take_append [simp]:
"!!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)"
by (induct n) (auto, case_tac xs, auto)

lemma drop_append [simp]:
"!!xs. drop n (xs @ ys) = drop n xs @ drop (n - length xs) ys"
by (induct n) (auto, case_tac xs, auto)

lemma take_take [simp]: "!!xs n. take n (take m xs) = take (min n m) xs"
apply (induct m)
 apply auto
apply (case_tac xs)
 apply auto
apply (case_tac na)
 apply auto
done

lemma drop_drop [simp]: "!!xs. drop n (drop m xs) = drop (n + m) xs"
apply (induct m)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma take_drop: "!!xs n. take n (drop m xs) = drop m (take (n + m) xs)"
apply (induct m)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma append_take_drop_id [simp]: "!!xs. take n xs @ drop n xs = xs"
apply (induct n)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma take_map: "!!xs. take n (map f xs) = map f (take n xs)"
apply (induct n)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma drop_map: "!!xs. drop n (map f xs) = map f (drop n xs)"
apply (induct n)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma rev_take: "!!i. rev (take i xs) = drop (length xs - i) (rev xs)"
apply (induct xs)
 apply auto
apply (case_tac i)
 apply auto
done

lemma rev_drop: "!!i. rev (drop i xs) = take (length xs - i) (rev xs)"
apply (induct xs)
 apply auto
apply (case_tac i)
 apply auto
done

lemma nth_take [simp]: "!!n i. i < n ==> (take n xs)!i = xs!i"
apply (induct xs)
 apply auto
apply (case_tac n)
 apply(blast )
apply (case_tac i)
 apply auto
done

lemma nth_drop [simp]:
"!!xs i. n + i <= length xs ==> (drop n xs)!i = xs!(n + i)"
apply (induct n)
 apply auto
apply (case_tac xs)
 apply auto
done

lemma append_eq_conv_conj:
"!!zs. (xs @ ys = zs) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
apply(induct xs)
 apply simp
apply clarsimp
apply (case_tac zs)
apply auto
done


subsection {* @{text takeWhile} and @{text dropWhile} *}

lemma takeWhile_dropWhile_id [simp]: "takeWhile P xs @ dropWhile P xs = xs"
by (induct xs) auto

lemma takeWhile_append1 [simp]:
"[| x:set xs; ~P(x)|] ==> takeWhile P (xs @ ys) = takeWhile P xs"
by (induct xs) auto

lemma takeWhile_append2 [simp]:
"(!!x. x : set xs ==> P x) ==> takeWhile P (xs @ ys) = xs @ takeWhile P ys"
by (induct xs) auto

lemma takeWhile_tail: "\<not> P x ==> takeWhile P (xs @ (x#l)) = takeWhile P xs"
by (induct xs) auto

lemma dropWhile_append1 [simp]:
"[| x : set xs; ~P(x)|] ==> dropWhile P (xs @ ys) = (dropWhile P xs)@ys"
by (induct xs) auto

lemma dropWhile_append2 [simp]:
"(!!x. x:set xs ==> P(x)) ==> dropWhile P (xs @ ys) = dropWhile P ys"
by (induct xs) auto

lemma set_take_whileD: "x : set (takeWhile P xs) ==> x : set xs \<and> P x"
by (induct xs) (auto split: split_if_asm)


subsection {* @{text zip} *}

lemma zip_Nil [simp]: "zip [] ys = []"
by (induct ys) auto

lemma zip_Cons_Cons [simp]: "zip (x # xs) (y # ys) = (x, y) # zip xs ys"
by simp

declare zip_Cons [simp del]

lemma length_zip [simp]:
"!!xs. length (zip xs ys) = min (length xs) (length ys)"
apply(induct ys)
 apply simp
apply (case_tac xs)
 apply auto
done

lemma zip_append1:
"!!xs. zip (xs @ ys) zs =
zip xs (take (length xs) zs) @ zip ys (drop (length xs) zs)"
apply (induct zs)
 apply simp
apply (case_tac xs)
 apply simp_all
done

lemma zip_append2:
"!!ys. zip xs (ys @ zs) =
zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs"
apply (induct xs)
 apply simp
apply (case_tac ys)
 apply simp_all
done

lemma zip_append [simp]:
 "[| length xs = length us; length ys = length vs |] ==>
zip (xs@ys) (us@vs) = zip xs us @ zip ys vs"
by (simp add: zip_append1)

lemma zip_rev:
"!!xs. length xs = length ys ==> zip (rev xs) (rev ys) = rev (zip xs ys)"
apply(induct ys)
 apply simp
apply (case_tac xs)
 apply simp_all
done

lemma nth_zip [simp]:
"!!i xs. [| i < length xs; i < length ys|] ==> (zip xs ys)!i = (xs!i, ys!i)"
apply (induct ys)
 apply simp
apply (case_tac xs)
 apply (simp_all add: nth.simps split: nat.split)
done

lemma set_zip:
"set (zip xs ys) = {(xs!i, ys!i) | i. i < min (length xs) (length ys)}"
by (simp add: set_conv_nth cong: rev_conj_cong)

lemma zip_update:
"length xs = length ys ==> zip (xs[i:=x]) (ys[i:=y]) = (zip xs ys)[i:=(x,y)]"
by (rule sym, simp add: update_zip)

lemma zip_replicate [simp]:
"!!j. zip (replicate i x) (replicate j y) = replicate (min i j) (x,y)"
apply (induct i)
 apply auto
apply (case_tac j)
 apply auto
done


subsection {* @{text list_all2} *}

lemma list_all2_lengthD: "list_all2 P xs ys ==> length xs = length ys"
by (simp add: list_all2_def)

lemma list_all2_Nil [iff]: "list_all2 P [] ys = (ys = [])"
by (simp add: list_all2_def)

lemma list_all2_Nil2[iff]: "list_all2 P xs [] = (xs = [])"
by (simp add: list_all2_def)

lemma list_all2_Cons [iff]:
"list_all2 P (x # xs) (y # ys) = (P x y \<and> list_all2 P xs ys)"
by (auto simp add: list_all2_def)

lemma list_all2_Cons1:
"list_all2 P (x # xs) ys = (\<exists>z zs. ys = z # zs \<and> P x z \<and> list_all2 P xs zs)"
by (cases ys) auto

lemma list_all2_Cons2:
"list_all2 P xs (y # ys) = (\<exists>z zs. xs = z # zs \<and> P z y \<and> list_all2 P zs ys)"
by (cases xs) auto

lemma list_all2_rev [iff]:
"list_all2 P (rev xs) (rev ys) = list_all2 P xs ys"
by (simp add: list_all2_def zip_rev cong: conj_cong)

lemma list_all2_append1:
"list_all2 P (xs @ ys) zs =
(EX us vs. zs = us @ vs \<and> length us = length xs \<and> length vs = length ys \<and>
list_all2 P xs us \<and> list_all2 P ys vs)"
apply (simp add: list_all2_def zip_append1)
apply (rule iffI)
 apply (rule_tac x = "take (length xs) zs" in exI)
 apply (rule_tac x = "drop (length xs) zs" in exI)
 apply (force split: nat_diff_split simp add: min_def)
apply clarify
apply (simp add: ball_Un)
done

lemma list_all2_append2:
"list_all2 P xs (ys @ zs) =
(EX us vs. xs = us @ vs \<and> length us = length ys \<and> length vs = length zs \<and>
list_all2 P us ys \<and> list_all2 P vs zs)"
apply (simp add: list_all2_def zip_append2)
apply (rule iffI)
 apply (rule_tac x = "take (length ys) xs" in exI)
 apply (rule_tac x = "drop (length ys) xs" in exI)
 apply (force split: nat_diff_split simp add: min_def)
apply clarify
apply (simp add: ball_Un)
done

lemma list_all2_conv_all_nth:
"list_all2 P xs ys =
(length xs = length ys \<and> (\<forall>i < length xs. P (xs!i) (ys!i)))"
by (force simp add: list_all2_def set_zip)

lemma list_all2_trans[rule_format]:
"\<forall>a b c. P1 a b --> P2 b c --> P3 a c ==>
\<forall>bs cs. list_all2 P1 as bs --> list_all2 P2 bs cs --> list_all2 P3 as cs"
apply(induct_tac as)
 apply simp
apply(rule allI)
apply(induct_tac bs)
 apply simp
apply(rule allI)
apply(induct_tac cs)
 apply auto
done


subsection {* @{text foldl} *}

lemma foldl_append [simp]:
"!!a. foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"
by (induct xs) auto

text {*
Note: @{text "n \<le> foldl (op +) n ns"} looks simpler, but is more
difficult to use because it requires an additional transitivity step.
*}

lemma start_le_sum: "!!n::nat. m <= n ==> m <= foldl (op +) n ns"
by (induct ns) auto

lemma elem_le_sum: "!!n::nat. n : set ns ==> n <= foldl (op +) 0 ns"
by (force intro: start_le_sum simp add: in_set_conv_decomp)

lemma sum_eq_0_conv [iff]:
"!!m::nat. (foldl (op +) m ns = 0) = (m = 0 \<and> (\<forall>n \<in> set ns. n = 0))"
by (induct ns) auto


subsection {* @{text upto} *}

lemma upt_rec: "[i..j(] = (if i<j then i#[Suc i..j(] else [])"
-- {* Does not terminate! *}
by (induct j) auto

lemma upt_conv_Nil [simp]: "j <= i ==> [i..j(] = []"
by (subst upt_rec) simp

lemma upt_Suc_append: "i <= j ==> [i..(Suc j)(] = [i..j(]@[j]"
-- {* Only needed if @{text upt_Suc} is deleted from the simpset. *}
by simp

lemma upt_conv_Cons: "i < j ==> [i..j(] = i # [Suc i..j(]"
apply(rule trans)
apply(subst upt_rec)
 prefer 2 apply(rule refl)
apply simp
done

lemma upt_add_eq_append: "i<=j ==> [i..j+k(] = [i..j(]@[j..j+k(]"
-- {* LOOPS as a simprule, since @{text "j <= j"}. *}
by (induct k) auto

lemma length_upt [simp]: "length [i..j(] = j - i"
by (induct j) (auto simp add: Suc_diff_le)

lemma nth_upt [simp]: "i + k < j ==> [i..j(] ! k = i + k"
apply (induct j)
apply (auto simp add: less_Suc_eq nth_append split: nat_diff_split)
done

lemma take_upt [simp]: "!!i. i+m <= n ==> take m [i..n(] = [i..i+m(]"
apply (induct m)
 apply simp
apply (subst upt_rec)
apply (rule sym)
apply (subst upt_rec)
apply (simp del: upt.simps)
done

lemma map_Suc_upt: "map Suc [m..n(] = [Suc m..n]"
by (induct n) auto

lemma nth_map_upt: "!!i. i < n-m ==> (map f [m..n(]) ! i = f(m+i)"
apply (induct n m rule: diff_induct)
prefer 3 apply (subst map_Suc_upt[symmetric])
apply (auto simp add: less_diff_conv nth_upt)
done

lemma nth_take_lemma [rule_format]:
"ALL xs ys. k <= length xs --> k <= length ys
--> (ALL i. i < k --> xs!i = ys!i)
--> take k xs = take k ys"
apply (induct k)
apply (simp_all add: less_Suc_eq_0_disj all_conj_distrib)
apply clarify
txt {* Both lists must be non-empty *}
apply (case_tac xs)
 apply simp
apply (case_tac ys)
 apply clarify
 apply (simp (no_asm_use))
apply clarify
txt {* prenexing's needed, not miniscoping *}
apply (simp (no_asm_use) add: all_simps [symmetric] del: all_simps)
apply blast
done

lemma nth_equalityI:
 "[| length xs = length ys; ALL i < length xs. xs!i = ys!i |] ==> xs = ys"
apply (frule nth_take_lemma [OF le_refl eq_imp_le])
apply (simp_all add: take_all)
done

lemma take_equalityI: "(\<forall>i. take i xs = take i ys) ==> xs = ys"
-- {* The famous take-lemma. *}
apply (drule_tac x = "max (length xs) (length ys)" in spec)
apply (simp add: le_max_iff_disj take_all)
done


subsection {* @{text "distinct"} and @{text remdups} *}

lemma distinct_append [simp]:
"distinct (xs @ ys) = (distinct xs \<and> distinct ys \<and> set xs \<inter> set ys = {})"
by (induct xs) auto

lemma set_remdups [simp]: "set (remdups xs) = set xs"
by (induct xs) (auto simp add: insert_absorb)

lemma distinct_remdups [iff]: "distinct (remdups xs)"
by (induct xs) auto

lemma distinct_filter [simp]: "distinct xs ==> distinct (filter P xs)"
by (induct xs) auto

text {*
It is best to avoid this indexed version of distinct, but sometimes
it is useful. *}
lemma distinct_conv_nth:
"distinct xs = (\<forall>i j. i < size xs \<and> j < size xs \<and> i \<noteq> j --> xs!i \<noteq> xs!j)"
apply (induct_tac xs)
 apply simp
apply simp
apply (rule iffI)
 apply clarsimp
 apply (case_tac i)
apply (case_tac j)
 apply simp
apply (simp add: set_conv_nth)
 apply (case_tac j)
apply (clarsimp simp add: set_conv_nth)
 apply simp
apply (rule conjI)
 apply (clarsimp simp add: set_conv_nth)
 apply (erule_tac x = 0 in allE)
 apply (erule_tac x = "Suc i" in allE)
 apply simp
apply clarsimp
apply (erule_tac x = "Suc i" in allE)
apply (erule_tac x = "Suc j" in allE)
apply simp
done


subsection {* @{text replicate} *}

lemma length_replicate [simp]: "length (replicate n x) = n"
by (induct n) auto

lemma map_replicate [simp]: "map f (replicate n x) = replicate n (f x)"
by (induct n) auto

lemma replicate_app_Cons_same:
"(replicate n x) @ (x # xs) = x # replicate n x @ xs"
by (induct n) auto

lemma rev_replicate [simp]: "rev (replicate n x) = replicate n x"
apply(induct n)
 apply simp
apply (simp add: replicate_app_Cons_same)
done

lemma replicate_add: "replicate (n + m) x = replicate n x @ replicate m x"
by (induct n) auto

lemma hd_replicate [simp]: "n \<noteq> 0 ==> hd (replicate n x) = x"
by (induct n) auto

lemma tl_replicate [simp]: "n \<noteq> 0 ==> tl (replicate n x) = replicate (n - 1) x"
by (induct n) auto

lemma last_replicate [simp]: "n \<noteq> 0 ==> last (replicate n x) = x"
by (atomize (full), induct n) auto

lemma nth_replicate[simp]: "!!i. i < n ==> (replicate n x)!i = x"
apply(induct n)
 apply simp
apply (simp add: nth_Cons split: nat.split)
done

lemma set_replicate_Suc: "set (replicate (Suc n) x) = {x}"
by (induct n) auto

lemma set_replicate [simp]: "n \<noteq> 0 ==> set (replicate n x) = {x}"
by (fast dest!: not0_implies_Suc intro!: set_replicate_Suc)

lemma set_replicate_conv_if: "set (replicate n x) = (if n = 0 then {} else {x})"
by auto

lemma in_set_replicateD: "x : set (replicate n y) ==> x = y"
by (simp add: set_replicate_conv_if split: split_if_asm)


subsection {* Lexcicographic orderings on lists *}

lemma wf_lexn: "wf r ==> wf (lexn r n)"
apply (induct_tac n)
 apply simp
apply simp
apply(rule wf_subset)
 prefer 2 apply (rule Int_lower1)
apply(rule wf_prod_fun_image)
 prefer 2 apply (rule inj_onI)
apply auto
done

lemma lexn_length:
"!!xs ys. (xs, ys) : lexn r n ==> length xs = n \<and> length ys = n"
by (induct n) auto

lemma wf_lex [intro!]: "wf r ==> wf (lex r)"
apply (unfold lex_def)
apply (rule wf_UN)
apply (blast intro: wf_lexn)
apply clarify
apply (rename_tac m n)
apply (subgoal_tac "m \<noteq> n")
 prefer 2 apply blast
apply (blast dest: lexn_length not_sym)
done

lemma lexn_conv:
"lexn r n =
{(xs,ys). length xs = n \<and> length ys = n \<and>
(\<exists>xys x y xs' ys'. xs= xys @ x#xs' \<and> ys= xys @ y # ys' \<and> (x, y):r)}"
apply (induct_tac n)
 apply simp
 apply blast
apply (simp add: image_Collect lex_prod_def)
apply safe
apply blast
 apply (rule_tac x = "ab # xys" in exI)
 apply simp
apply (case_tac xys)
 apply simp_all
apply blast
done

lemma lex_conv:
"lex r =
{(xs,ys). length xs = length ys \<and>
(\<exists>xys x y xs' ys'. xs = xys @ x # xs' \<and> ys = xys @ y # ys' \<and> (x, y):r)}"
by (force simp add: lex_def lexn_conv)

lemma wf_lexico [intro!]: "wf r ==> wf (lexico r)"
by (unfold lexico_def) blast

lemma lexico_conv:
"lexico r = {(xs,ys). length xs < length ys |
length xs = length ys \<and> (xs, ys) : lex r}"
by (simp add: lexico_def diag_def lex_prod_def measure_def inv_image_def)

lemma Nil_notin_lex [iff]: "([], ys) \<notin> lex r"
by (simp add: lex_conv)

lemma Nil2_notin_lex [iff]: "(xs, []) \<notin> lex r"
by (simp add:lex_conv)

lemma Cons_in_lex [iff]:
"((x # xs, y # ys) : lex r) =
((x, y) : r \<and> length xs = length ys | x = y \<and> (xs, ys) : lex r)"
apply (simp add: lex_conv)
apply (rule iffI)
 prefer 2 apply (blast intro: Cons_eq_appendI)
apply clarify
apply (case_tac xys)
 apply simp
apply simp
apply blast
done


subsection {* @{text sublist} --- a generalization of @{text nth} to sets *}

lemma sublist_empty [simp]: "sublist xs {} = []"
by (auto simp add: sublist_def)

lemma sublist_nil [simp]: "sublist [] A = []"
by (auto simp add: sublist_def)

lemma sublist_shift_lemma:
"map fst [p:zip xs [i..i + length xs(] . snd p : A] =
map fst [p:zip xs [0..length xs(] . snd p + i : A]"
by (induct xs rule: rev_induct) (simp_all add: add_commute)

lemma sublist_append:
"sublist (l @ l') A = sublist l A @ sublist l' {j. j + length l : A}"
apply (unfold sublist_def)
apply (induct l' rule: rev_induct)
 apply simp
apply (simp add: upt_add_eq_append[of 0] zip_append sublist_shift_lemma)
apply (simp add: add_commute)
done

lemma sublist_Cons:
"sublist (x # l) A = (if 0:A then [x] else []) @ sublist l {j. Suc j : A}"
apply (induct l rule: rev_induct)
 apply (simp add: sublist_def)
apply (simp del: append_Cons add: append_Cons[symmetric] sublist_append)
done

lemma sublist_singleton [simp]: "sublist [x] A = (if 0 : A then [x] else [])"
by (simp add: sublist_Cons)

lemma sublist_upt_eq_take [simp]: "sublist l {..n(} = take n l"
apply (induct l rule: rev_induct)
 apply simp
apply (simp split: nat_diff_split add: sublist_append)
done


lemma take_Cons':
"take n (x # xs) = (if n = 0 then [] else x # take (n - 1) xs)"
by (cases n) simp_all

lemma drop_Cons':
"drop n (x # xs) = (if n = 0 then x # xs else drop (n - 1) xs)"
by (cases n) simp_all

lemma nth_Cons': "(x # xs)!n = (if n = 0 then x else xs!(n - 1))"
by (cases n) simp_all

lemmas [simp] = take_Cons'[of "number_of v",standard]
                drop_Cons'[of "number_of v",standard]
                nth_Cons'[of _ _ "number_of v",standard]


subsection {* Characters and strings *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

types string = "char list"

syntax
  "_Char" :: "xstr => char"    ("CHR _")
  "_String" :: "xstr => string"    ("_")

parse_ast_translation {*
  let
    val constants = Syntax.Appl o map Syntax.Constant;

    fun mk_nib n = "Nibble" ^ chr (n + (if n <= 9 then ord "0" else ord "A" - 10));
    fun mk_char c =
      if Symbol.is_ascii c andalso Symbol.is_printable c then
        constants ["Char", mk_nib (ord c div 16), mk_nib (ord c mod 16)]
      else error ("Printable ASCII character expected: " ^ quote c);

    fun mk_string [] = Syntax.Constant "Nil"
      | mk_string (c :: cs) = Syntax.Appl [Syntax.Constant "Cons", mk_char c, mk_string cs];

    fun char_ast_tr [Syntax.Variable xstr] =
        (case Syntax.explode_xstr xstr of
          [c] => mk_char c
        | _ => error ("Single character expected: " ^ xstr))
      | char_ast_tr asts = raise AST ("char_ast_tr", asts);

    fun string_ast_tr [Syntax.Variable xstr] =
        (case Syntax.explode_xstr xstr of
          [] => constants [Syntax.constrainC, "Nil", "string"]
        | cs => mk_string cs)
      | string_ast_tr asts = raise AST ("string_tr", asts);
  in [("_Char", char_ast_tr), ("_String", string_ast_tr)] end;
*}

print_ast_translation {*
  let
    fun dest_nib (Syntax.Constant c) =
        (case explode c of
          ["N", "i", "b", "b", "l", "e", h] =>
            if "0" <= h andalso h <= "9" then ord h - ord "0"
            else if "A" <= h andalso h <= "F" then ord h - ord "A" + 10
            else raise Match
        | _ => raise Match)
      | dest_nib _ = raise Match;

    fun dest_chr c1 c2 =
      let val c = chr (dest_nib c1 * 16 + dest_nib c2)
      in if Symbol.is_printable c then c else raise Match end;

    fun dest_char (Syntax.Appl [Syntax.Constant "Char", c1, c2]) = dest_chr c1 c2
      | dest_char _ = raise Match;

    fun xstr cs = Syntax.Appl [Syntax.Constant "_xstr", Syntax.Variable (Syntax.implode_xstr cs)];

    fun char_ast_tr' [c1, c2] = Syntax.Appl [Syntax.Constant "_Char", xstr [dest_chr c1 c2]]
      | char_ast_tr' _ = raise Match;

    fun list_ast_tr' [args] = Syntax.Appl [Syntax.Constant "_String",
            xstr (map dest_char (Syntax.unfold_ast "_args" args))]
      | list_ast_tr' ts = raise Match;
  in [("Char", char_ast_tr'), ("@list", list_ast_tr')] end;
*}

end
