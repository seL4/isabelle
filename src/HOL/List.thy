(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994 TU Muenchen
*)

header {* The datatype of finite lists *}
theory List1 = PreList:

datatype 'a list = Nil ("[]") | Cons 'a "'a list" (infixr "#" 65)

consts
  "@"         :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"            (infixr 65)
  filter      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  concat      :: "'a list list \<Rightarrow> 'a list"
  foldl       :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
  foldr       :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b"
  hd          :: "'a list \<Rightarrow> 'a"
  tl          :: "'a list \<Rightarrow> 'a list"
  last        :: "'a list \<Rightarrow> 'a"
  butlast     :: "'a list \<Rightarrow> 'a list"
  set         :: "'a list \<Rightarrow> 'a set"
  list_all    :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
  list_all2   :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> bool"
  map         :: "('a\<Rightarrow>'b) \<Rightarrow> ('a list \<Rightarrow> 'b list)"
  mem         :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"                    (infixl 55)
  nth         :: "'a list \<Rightarrow> nat \<Rightarrow> 'a"			  (infixl "!" 100)
  list_update :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list"
  take        :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  drop        :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  takeWhile   :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  dropWhile   :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  rev         :: "'a list \<Rightarrow> 'a list"
  zip	      :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list"
  upt         :: "nat \<Rightarrow> nat \<Rightarrow> nat list"                   ("(1[_../_'(])")
  remdups     :: "'a list \<Rightarrow> 'a list"
  null        :: "'a list \<Rightarrow> bool"
  "distinct"  :: "'a list \<Rightarrow> bool"
  replicate   :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list"

nonterminals
  lupdbinds  lupdbind

syntax
  (* list Enumeration *)
  "@list"     :: "args \<Rightarrow> 'a list"                          ("[(_)]")

  (* Special syntax for filter *)
  "@filter"   :: "[pttrn, 'a list, bool] \<Rightarrow> 'a list"        ("(1[_:_./ _])")

  (* list update *)
  "_lupdbind"      :: "['a, 'a] \<Rightarrow> lupdbind"            ("(2_ :=/ _)")
  ""               :: "lupdbind \<Rightarrow> lupdbinds"           ("_")
  "_lupdbinds"     :: "[lupdbind, lupdbinds] \<Rightarrow> lupdbinds" ("_,/ _")
  "_LUpdate"       :: "['a, lupdbinds] \<Rightarrow> 'a"           ("_/[(_)]" [900,0] 900)

  upto        :: "nat \<Rightarrow> nat \<Rightarrow> nat list"                   ("(1[_../_])")

translations
  "[x, xs]"     == "x#[xs]"
  "[x]"         == "x#[]"
  "[x:xs . P]"  == "filter (%x. P) xs"

  "_LUpdate xs (_lupdbinds b bs)"  == "_LUpdate (_LUpdate xs b) bs"
  "xs[i:=x]"                       == "list_update xs i x"

  "[i..j]" == "[i..(Suc j)(]"


syntax (xsymbols)
  "@filter"   :: "[pttrn, 'a list, bool] \<Rightarrow> 'a list"        ("(1[_\<in>_ ./ _])")


consts
  lists        :: "'a set \<Rightarrow> 'a list set"

inductive "lists A"
intros
Nil:  "[]: lists A"
Cons: "\<lbrakk> a: A;  l: lists A \<rbrakk> \<Longrightarrow> a#l : lists A"


(*Function "size" is overloaded for all datatypes.  Users may refer to the
  list version as "length".*)
syntax   length :: "'a list \<Rightarrow> nat"
translations  "length"  =>  "size:: _ list \<Rightarrow> nat"

(* translating size::list -> length *)
typed_print_translation
{*
let
fun size_tr' _ (Type ("fun", (Type ("list", _) :: _))) [t] =
      Syntax.const "length" $ t
  | size_tr' _ _ _ = raise Match;
in [("size", size_tr')] end
*}

primrec
  "hd(x#xs) = x"
primrec
  "tl([])   = []"
  "tl(x#xs) = xs"
primrec
  "null([])   = True"
  "null(x#xs) = False"
primrec
  "last(x#xs) = (if xs=[] then x else last xs)"
primrec
  "butlast []    = []"
  "butlast(x#xs) = (if xs=[] then [] else x#butlast xs)"
primrec
  "x mem []     = False"
  "x mem (y#ys) = (if y=x then True else x mem ys)"
primrec
  "set [] = {}"
  "set (x#xs) = insert x (set xs)"
primrec
  list_all_Nil:  "list_all P [] = True"
  list_all_Cons: "list_all P (x#xs) = (P(x) & list_all P xs)"
primrec
  "map f []     = []"
  "map f (x#xs) = f(x)#map f xs"
primrec
  append_Nil:  "[]    @ys = ys"
  append_Cons: "(x#xs)@ys = x#(xs@ys)"
primrec
  "rev([])   = []"
  "rev(x#xs) = rev(xs) @ [x]"
primrec
  "filter P []     = []"
  "filter P (x#xs) = (if P x then x#filter P xs else filter P xs)"
primrec
  foldl_Nil:  "foldl f a [] = a"
  foldl_Cons: "foldl f a (x#xs) = foldl f (f a x) xs"
primrec
  "foldr f [] a     = a"
  "foldr f (x#xs) a = f x (foldr f xs a)"
primrec
  "concat([])   = []"
  "concat(x#xs) = x @ concat(xs)"
primrec
  drop_Nil:  "drop n [] = []"
  drop_Cons: "drop n (x#xs) = (case n of 0 \<Rightarrow> x#xs | Suc(m) \<Rightarrow> drop m xs)"
  (* Warning: simpset does not contain this definition but separate theorems 
     for n=0 / n=Suc k*)
primrec
  take_Nil:  "take n [] = []"
  take_Cons: "take n (x#xs) = (case n of 0 \<Rightarrow> [] | Suc(m) \<Rightarrow> x # take m xs)"
  (* Warning: simpset does not contain this definition but separate theorems 
     for n=0 / n=Suc k*)
primrec 
  nth_Cons:  "(x#xs)!n = (case n of 0 \<Rightarrow> x | (Suc k) \<Rightarrow> xs!k)"
  (* Warning: simpset does not contain this definition but separate theorems 
     for n=0 / n=Suc k*)
primrec
 "    [][i:=v] = []"
 "(x#xs)[i:=v] = (case i of 0     \<Rightarrow> v # xs 
			  | Suc j \<Rightarrow> x # xs[j:=v])"
primrec
  "takeWhile P []     = []"
  "takeWhile P (x#xs) = (if P x then x#takeWhile P xs else [])"
primrec
  "dropWhile P []     = []"
  "dropWhile P (x#xs) = (if P x then dropWhile P xs else x#xs)"
primrec
  "zip xs []     = []"
zip_Cons:
  "zip xs (y#ys) = (case xs of [] \<Rightarrow> [] | z#zs \<Rightarrow> (z,y)#zip zs ys)"
  (* Warning: simpset does not contain this definition but separate theorems 
     for xs=[] / xs=z#zs *)
primrec
  upt_0:   "[i..0(] = []"
  upt_Suc: "[i..(Suc j)(] = (if i <= j then [i..j(] @ [j] else [])"
primrec
  "distinct []     = True"
  "distinct (x#xs) = (x ~: set xs & distinct xs)"
primrec
  "remdups [] = []"
  "remdups (x#xs) = (if x : set xs then remdups xs else x # remdups xs)"
primrec
  replicate_0:   "replicate  0      x = []"
  replicate_Suc: "replicate (Suc n) x = x # replicate n x"
defs
 list_all2_def:
 "list_all2 P xs ys == length xs = length ys & (!(x,y):set(zip xs ys). P x y)"


(** Lexicographic orderings on lists **)

consts
 lexn :: "('a * 'a)set \<Rightarrow> nat \<Rightarrow> ('a list * 'a list)set"
primrec
"lexn r 0       = {}"
"lexn r (Suc n) = (prod_fun (%(x,xs). x#xs) (%(x,xs). x#xs) ` (r <*lex*> lexn r n)) Int
                  {(xs,ys). length xs = Suc n & length ys = Suc n}"

constdefs
  lex :: "('a * 'a)set \<Rightarrow> ('a list * 'a list)set"
    "lex r == UN n. lexn r n"

  lexico :: "('a * 'a)set \<Rightarrow> ('a list * 'a list)set"
    "lexico r == inv_image (less_than <*lex*> lex r) (%xs. (length xs, xs))"

  sublist :: "['a list, nat set] \<Rightarrow> 'a list"
    "sublist xs A == map fst (filter (%p. snd p : A) (zip xs [0..size xs(]))"


lemma not_Cons_self[simp]: "\<And>x. xs ~= x#xs"
by(induct_tac "xs", auto)

lemmas not_Cons_self2[simp] = not_Cons_self[THEN not_sym]

lemma neq_Nil_conv: "(xs ~= []) = (? y ys. xs = y#ys)";
by(induct_tac "xs", auto)

(* Induction over the length of a list: *)
(* "(!!xs. (!ys. length ys < length xs --> P ys) ==> P xs) ==> P(xs)" *)
lemmas length_induct = measure_induct[of length]


(** "lists": the list-forming operator over sets **)

lemma lists_mono: "A<=B ==> lists A <= lists B"
apply(unfold lists.defs)
apply(blast intro!:lfp_mono)
done

inductive_cases listsE[elim!]: "x#l : lists A"
declare lists.intros[intro!]

lemma lists_IntI[rule_format]:
 "l: lists A ==> l: lists B --> l: lists (A Int B)";
apply(erule lists.induct)
apply blast+
done

lemma lists_Int_eq[simp]: "lists (A Int B) = lists A Int lists B"
apply(rule mono_Int[THEN equalityI])
apply(simp add:mono_def lists_mono)
apply(blast intro!: lists_IntI)
done

lemma append_in_lists_conv[iff]:
 "(xs@ys : lists A) = (xs : lists A & ys : lists A)"
by(induct_tac "xs", auto)

(** length **)
(* needs to come before "@" because of thm append_eq_append_conv *)

section "length"

lemma length_append[simp]: "length(xs@ys) = length(xs)+length(ys)"
by(induct_tac "xs", auto)

lemma length_map[simp]: "length (map f xs) = length xs"
by(induct_tac "xs", auto)

lemma length_rev[simp]: "length(rev xs) = length(xs)"
by(induct_tac "xs", auto)

lemma length_tl[simp]: "length(tl xs) = (length xs) - 1"
by(case_tac "xs", auto)

lemma length_0_conv[iff]: "(length xs = 0) = (xs = [])"
by(induct_tac "xs", auto)

lemma length_greater_0_conv[iff]: "(0 < length xs) = (xs ~= [])"
by(induct_tac xs, auto)

lemma length_Suc_conv:
 "(length xs = Suc n) = (? y ys. xs = y#ys & length ys = n)"
by(induct_tac "xs", auto)

(** @ - append **)

section "@ - append"

lemma append_assoc[simp]: "(xs@ys)@zs = xs@(ys@zs)"
by(induct_tac "xs", auto)

lemma append_Nil2[simp]: "xs @ [] = xs"
by(induct_tac "xs", auto)

lemma append_is_Nil_conv[iff]: "(xs@ys = []) = (xs=[] & ys=[])"
by(induct_tac "xs", auto)

lemma Nil_is_append_conv[iff]: "([] = xs@ys) = (xs=[] & ys=[])"
by(induct_tac "xs", auto)

lemma append_self_conv[iff]: "(xs @ ys = xs) = (ys=[])"
by(induct_tac "xs", auto)

lemma self_append_conv[iff]: "(xs = xs @ ys) = (ys=[])"
by(induct_tac "xs", auto)

lemma append_eq_append_conv[rule_format,simp]:
 "!ys. length xs = length ys | length us = length vs
       --> (xs@us = ys@vs) = (xs=ys & us=vs)"
apply(induct_tac "xs")
 apply(rule allI)
 apply(case_tac "ys")
  apply simp
 apply force
apply(rule allI)
apply(case_tac "ys")
 apply force
apply simp
done

lemma same_append_eq[iff]: "(xs @ ys = xs @ zs) = (ys=zs)"
by simp

lemma append1_eq_conv[iff]: "(xs @ [x] = ys @ [y]) = (xs = ys & x = y)" 
by simp

lemma append_same_eq[iff]: "(ys @ xs = zs @ xs) = (ys=zs)"
by simp

lemma append_self_conv2[iff]: "(xs @ ys = ys) = (xs=[])"
by(insert append_same_eq[of _ _ "[]"], auto)

lemma self_append_conv2[iff]: "(ys = xs @ ys) = (xs=[])"
by(auto simp add: append_same_eq[of "[]", simplified])

lemma hd_Cons_tl[rule_format,simp]: "xs ~= [] --> hd xs # tl xs = xs"
by(induct_tac "xs", auto)

lemma hd_append: "hd(xs@ys) = (if xs=[] then hd ys else hd xs)"
by(induct_tac "xs", auto)

lemma hd_append2[simp]: "xs ~= [] ==> hd(xs @ ys) = hd xs"
by(simp add: hd_append split: list.split)

lemma tl_append: "tl(xs@ys) = (case xs of [] => tl(ys) | z#zs => zs@ys)"
by(simp split: list.split)

lemma tl_append2[simp]: "xs ~= [] ==> tl(xs @ ys) = (tl xs) @ ys"
by(simp add: tl_append split: list.split)

(* trivial rules for solving @-equations automatically *)

lemma eq_Nil_appendI: "xs = ys ==> xs = [] @ ys"
by simp

lemma Cons_eq_appendI: "[| x#xs1 = ys; xs = xs1 @ zs |] ==> x#xs = ys@zs"
by(drule sym, simp)

lemma append_eq_appendI: "[| xs@xs1 = zs; ys = xs1 @ us |] ==> xs@ys = zs@us"
by(drule sym, simp)


(***
Simplification procedure for all list equalities.
Currently only tries to rearrange @ to see if
- both lists end in a singleton list,
- or both lists end in the same list.
***)
ML_setup{*
local

val list_eq_pattern =
  Thm.read_cterm (Theory.sign_of (the_context ())) ("(xs::'a list) = ys",HOLogic.boolT)

fun last (cons as Const("List.list.Cons",_) $ _ $ xs) =
      (case xs of Const("List.list.Nil",_) => cons | _ => last xs)
  | last (Const("List.op @",_) $ _ $ ys) = last ys
  | last t = t

fun list1 (Const("List.list.Cons",_) $ _ $ Const("List.list.Nil",_)) = true
  | list1 _ = false

fun butlast ((cons as Const("List.list.Cons",_) $ x) $ xs) =
      (case xs of Const("List.list.Nil",_) => xs | _ => cons $ butlast xs)
  | butlast ((app as Const("List.op @",_) $ xs) $ ys) = app $ butlast ys
  | butlast xs = Const("List.list.Nil",fastype_of xs)

val rearr_tac =
  simp_tac (HOL_basic_ss addsimps [append_assoc,append_Nil,append_Cons])

fun list_eq sg _ (F as (eq as Const(_,eqT)) $ lhs $ rhs) =
  let
    val lastl = last lhs and lastr = last rhs
    fun rearr conv =
      let val lhs1 = butlast lhs and rhs1 = butlast rhs
          val Type(_,listT::_) = eqT
          val appT = [listT,listT] ---> listT
          val app = Const("List.op @",appT)
          val F2 = eq $ (app$lhs1$lastl) $ (app$rhs1$lastr)
          val ct = cterm_of sg (HOLogic.mk_Trueprop(HOLogic.mk_eq(F,F2)))
          val thm = prove_goalw_cterm [] ct (K [rearr_tac 1])
            handle ERROR =>
            error("The error(s) above occurred while trying to prove " ^
                  string_of_cterm ct)
      in Some((conv RS (thm RS trans)) RS eq_reflection) end

  in if list1 lastl andalso list1 lastr
     then rearr append1_eq_conv
     else
     if lastl aconv lastr
     then rearr append_same_eq
     else None
  end
in
val list_eq_simproc = mk_simproc "list_eq" [list_eq_pattern] list_eq
end;

Addsimprocs [list_eq_simproc];
*}


(** map **)

section "map"

lemma map_ext: "(\<And>x. x : set xs \<longrightarrow> f x = g x) \<Longrightarrow> map f xs = map g xs"
by (induct xs, simp_all)

lemma map_ident[simp]: "map (%x. x) = (%xs. xs)"
by(rule ext, induct_tac "xs", auto)

lemma map_append[simp]: "map f (xs@ys) = map f xs @ map f ys"
by(induct_tac "xs", auto)

lemma map_compose(*[simp]*): "map (f o g) xs = map f (map g xs)"
by(unfold o_def, induct_tac "xs", auto)

lemma rev_map: "rev(map f xs) = map f (rev xs)"
by(induct_tac xs, auto)

(* a congruence rule for map: *)
lemma map_cong:
 "xs=ys ==> (!!x. x : set ys \<Longrightarrow> f x = g x) \<Longrightarrow> map f xs = map g ys"
by (clarify, induct ys, auto)

lemma map_is_Nil_conv[iff]: "(map f xs = []) = (xs = [])"
by(case_tac xs, auto)

lemma Nil_is_map_conv[iff]: "([] = map f xs) = (xs = [])"
by(case_tac xs, auto)

lemma map_eq_Cons:
 "(map f xs = y#ys) = (? x xs'. xs = x#xs' & f x = y & map f xs' = ys)"
by(case_tac xs, auto)

lemma map_injective:
 "\<And>xs. map f xs = map f ys \<Longrightarrow> (!x y. f x = f y --> x=y) \<Longrightarrow> xs=ys"
by(induct "ys", simp, fastsimp simp add:map_eq_Cons)

lemma inj_mapI: "inj f ==> inj (map f)"
by(blast dest:map_injective injD intro:injI)

lemma inj_mapD: "inj (map f) ==> inj f"
apply(unfold inj_on_def)
apply clarify
apply(erule_tac x = "[x]" in ballE)
 apply(erule_tac x = "[y]" in ballE)
  apply simp
 apply blast
apply blast
done

lemma inj_map: "inj (map f) = inj f"
by(blast dest:inj_mapD intro:inj_mapI)

(** rev **)

section "rev"

lemma rev_append[simp]: "rev(xs@ys) = rev(ys) @ rev(xs)"
by(induct_tac xs, auto)

lemma rev_rev_ident[simp]: "rev(rev xs) = xs"
by(induct_tac xs, auto)

lemma rev_is_Nil_conv[iff]: "(rev xs = []) = (xs = [])"
by(induct_tac xs, auto)

lemma Nil_is_rev_conv[iff]: "([] = rev xs) = (xs = [])"
by(induct_tac xs, auto)

lemma rev_is_rev_conv[iff]: "!!ys. (rev xs = rev ys) = (xs = ys)"
apply(induct "xs" )
 apply force
apply(case_tac ys)
 apply simp
apply force
done

lemma rev_induct: "[| P []; !!x xs. P xs ==> P(xs@[x]) |] ==> P xs"
apply(subst rev_rev_ident[symmetric])
apply(rule_tac list = "rev xs" in list.induct, simp_all)
done

(* Instead of (rev_induct_tac xs) use (induct_tac xs rule: rev_induct) *)

lemma rev_exhaust: "(xs = [] \<Longrightarrow> P) \<Longrightarrow>  (!!ys y. xs = ys@[y] \<Longrightarrow> P) \<Longrightarrow> P"
by(induct xs rule: rev_induct, auto)


(** set **)

section "set"

lemma finite_set[iff]: "finite (set xs)"
by(induct_tac xs, auto)

lemma set_append[simp]: "set (xs@ys) = (set xs Un set ys)"
by(induct_tac xs, auto)

lemma set_subset_Cons: "set xs \<subseteq> set (x#xs)"
by auto

lemma set_empty[iff]: "(set xs = {}) = (xs = [])"
by(induct_tac xs, auto)

lemma set_rev[simp]: "set(rev xs) = set(xs)"
by(induct_tac xs, auto)

lemma set_map[simp]: "set(map f xs) = f`(set xs)"
by(induct_tac xs, auto)

lemma set_filter[simp]: "set(filter P xs) = {x. x : set xs & P x}"
by(induct_tac xs, auto)

lemma set_upt[simp]: "set[i..j(] = {k. i <= k & k < j}"
apply(induct_tac j)
 apply simp_all
apply(erule ssubst)
apply auto
apply arith
done

lemma in_set_conv_decomp: "(x : set xs) = (? ys zs. xs = ys@x#zs)"
apply(induct_tac "xs")
 apply simp
apply simp
apply(rule iffI)
 apply(blast intro: eq_Nil_appendI Cons_eq_appendI)
apply(erule exE)+
apply(case_tac "ys")
apply auto
done


(* eliminate `lists' in favour of `set' *)

lemma in_lists_conv_set: "(xs : lists A) = (!x : set xs. x : A)"
by(induct_tac xs, auto)

lemmas in_listsD[dest!] = in_lists_conv_set[THEN iffD1]
lemmas in_listsI[intro!] = in_lists_conv_set[THEN iffD2]


(** mem **)
 
section "mem"

lemma set_mem_eq: "(x mem xs) = (x : set xs)"
by(induct_tac xs, auto)


(** list_all **)

section "list_all"

lemma list_all_conv: "list_all P xs = (!x:set xs. P x)"
by(induct_tac xs, auto)

lemma list_all_append[simp]:
 "list_all P (xs@ys) = (list_all P xs & list_all P ys)"
by(induct_tac xs, auto)


(** filter **)

section "filter"

lemma filter_append[simp]: "filter P (xs@ys) = filter P xs @ filter P ys"
by(induct_tac xs, auto)

lemma filter_filter[simp]: "filter P (filter Q xs) = filter (%x. Q x & P x) xs"
by(induct_tac xs, auto)

lemma filter_True[simp]: "!x : set xs. P x \<Longrightarrow> filter P xs = xs"
by(induct xs, auto)

lemma filter_False[simp]: "!x : set xs. ~P x \<Longrightarrow> filter P xs = []"
by(induct xs, auto)

lemma length_filter[simp]: "length (filter P xs) <= length xs"
by(induct xs, auto simp add: le_SucI)

lemma filter_is_subset[simp]: "set (filter P xs) <= set xs"
by auto


section "concat"

lemma concat_append[simp]: "concat(xs@ys) = concat(xs)@concat(ys)"
by(induct xs, auto)

lemma concat_eq_Nil_conv[iff]: "(concat xss = []) = (!xs:set xss. xs=[])"
by(induct xss, auto)

lemma Nil_eq_concat_conv[iff]: "([] = concat xss) = (!xs:set xss. xs=[])"
by(induct xss, auto)

lemma set_concat[simp]: "set(concat xs) = Union(set ` set xs)"
by(induct xs, auto)

lemma map_concat: "map f (concat xs) = concat (map (map f) xs)" 
by(induct xs, auto)

lemma filter_concat: "filter p (concat xs) = concat (map (filter p) xs)" 
by(induct xs, auto)

lemma rev_concat: "rev(concat xs) = concat (map rev (rev xs))"
by(induct xs, auto)

(** nth **)

section "nth"

lemma nth_Cons_0[simp]: "(x#xs)!0 = x"
by auto

lemma nth_Cons_Suc[simp]: "(x#xs)!(Suc n) = xs!n"
by auto

declare nth.simps[simp del]

lemma nth_append:
 "!!n. (xs@ys)!n = (if n < length xs then xs!n else ys!(n - length xs))"
apply(induct "xs")
 apply simp
apply(case_tac "n" )
 apply auto
done

lemma nth_map[simp]: "!!n. n < length xs \<Longrightarrow> (map f xs)!n = f(xs!n)"
apply(induct "xs" )
 apply simp
apply(case_tac "n")
 apply auto
done

lemma set_conv_nth: "set xs = {xs!i |i. i < length xs}"
apply(induct_tac "xs")
 apply simp
apply simp
apply safe
  apply(rule_tac x = 0 in exI)
  apply simp
 apply(rule_tac x = "Suc i" in exI)
 apply simp
apply(case_tac "i")
 apply simp
apply(rename_tac "j")
apply(rule_tac x = "j" in exI)
apply simp
done

lemma list_ball_nth: "\<lbrakk> n < length xs; !x : set xs. P x \<rbrakk> \<Longrightarrow> P(xs!n)"
by(simp add:set_conv_nth, blast)

lemma nth_mem[simp]: "n < length xs ==> xs!n : set xs"
by(simp add:set_conv_nth, blast)

lemma all_nth_imp_all_set:
 "\<lbrakk> !i < length xs. P(xs!i); x : set xs \<rbrakk> \<Longrightarrow> P x"
by(simp add:set_conv_nth, blast)

lemma all_set_conv_all_nth:
 "(!x : set xs. P x) = (!i. i<length xs --> P (xs ! i))"
by(simp add:set_conv_nth, blast)


(** list update **)

section "list update"

lemma length_list_update[simp]: "!!i. length(xs[i:=x]) = length xs"
by(induct xs, simp, simp split:nat.split)

lemma nth_list_update:
 "!!i j. i < length xs  \<Longrightarrow> (xs[i:=x])!j = (if i=j then x else xs!j)"
by(induct xs, simp, auto simp add:nth_Cons split:nat.split)

lemma nth_list_update_eq[simp]: "i < length xs  ==> (xs[i:=x])!i = x"
by(simp add:nth_list_update)

lemma nth_list_update_neq[simp]: "!!i j. i ~= j \<Longrightarrow> xs[i:=x]!j = xs!j"
by(induct xs, simp, auto simp add:nth_Cons split:nat.split)

lemma list_update_overwrite[simp]:
 "!!i. i < size xs ==> xs[i:=x, i:=y] = xs[i:=y]"
by(induct xs, simp, simp split:nat.split)

lemma list_update_same_conv:
 "!!i. i < length xs \<Longrightarrow> (xs[i := x] = xs) = (xs!i = x)"
by(induct xs, simp, simp split:nat.split, blast)

lemma update_zip:
"!!i xy xs. length xs = length ys \<Longrightarrow>
    (zip xs ys)[i:=xy] = zip (xs[i:=fst xy]) (ys[i:=snd xy])"
by(induct ys, auto, case_tac xs, auto split:nat.split)

lemma set_update_subset_insert: "!!i. set(xs[i:=x]) <= insert x (set xs)"
by(induct xs, simp, simp split:nat.split, fast)

lemma set_update_subsetI: "[| set xs <= A; x:A |] ==> set(xs[i := x]) <= A"
by(fast dest!:set_update_subset_insert[THEN subsetD])


(** last & butlast **)

section "last / butlast"

lemma last_snoc[simp]: "last(xs@[x]) = x"
by(induct xs, auto)

lemma butlast_snoc[simp]:"butlast(xs@[x]) = xs"
by(induct xs, auto)

lemma length_butlast[simp]: "length(butlast xs) = length xs - 1"
by(induct xs rule:rev_induct, auto)

lemma butlast_append:
 "!!ys. butlast (xs@ys) = (if ys=[] then butlast xs else xs@butlast ys)"
by(induct xs, auto)

lemma append_butlast_last_id[simp]:
 "xs ~= [] --> butlast xs @ [last xs] = xs"
by(induct xs, auto)

lemma in_set_butlastD: "x:set(butlast xs) ==> x:set xs"
by(induct xs, auto split:split_if_asm)

lemma in_set_butlast_appendI:
 "x:set(butlast xs) | x:set(butlast ys) ==> x:set(butlast(xs@ys))"
by(auto dest:in_set_butlastD simp add:butlast_append)

(** take  & drop **)
section "take & drop"

lemma take_0[simp]: "take 0 xs = []"
by(induct xs, auto)

lemma drop_0[simp]: "drop 0 xs = xs"
by(induct xs, auto)

lemma take_Suc_Cons[simp]: "take (Suc n) (x#xs) = x # take n xs"
by simp

lemma drop_Suc_Cons[simp]: "drop (Suc n) (x#xs) = drop n xs"
by simp

declare take_Cons[simp del] drop_Cons[simp del]

lemma length_take[simp]: "!!xs. length(take n xs) = min (length xs) n"
by(induct n, auto, case_tac xs, auto)

lemma length_drop[simp]: "!!xs. length(drop n xs) = (length xs - n)"
by(induct n, auto, case_tac xs, auto)

lemma take_all[simp]: "!!xs. length xs <= n ==> take n xs = xs"
by(induct n, auto, case_tac xs, auto)

lemma drop_all[simp]: "!!xs. length xs <= n ==> drop n xs = []"
by(induct n, auto, case_tac xs, auto)

lemma take_append[simp]:
 "!!xs. take n (xs @ ys) = (take n xs @ take (n - length xs) ys)"
by(induct n, auto, case_tac xs, auto)

lemma drop_append[simp]:
 "!!xs. drop n (xs@ys) = drop n xs @ drop (n - length xs) ys" 
by(induct n, auto, case_tac xs, auto)

lemma take_take[simp]: "!!xs n. take n (take m xs) = take (min n m) xs"
apply(induct m)
 apply auto
apply(case_tac xs)
 apply auto
apply(case_tac na)
 apply auto
done

lemma drop_drop[simp]: "!!xs. drop n (drop m xs) = drop (n + m) xs" 
apply(induct m)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma take_drop: "!!xs n. take n (drop m xs) = drop m (take (n + m) xs)"
apply(induct m)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma append_take_drop_id[simp]: "!!xs. take n xs @ drop n xs = xs"
apply(induct n)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma take_map: "!!xs. take n (map f xs) = map f (take n xs)"
apply(induct n)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma drop_map: "!!xs. drop n (map f xs) = map f (drop n xs)" 
apply(induct n)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma rev_take: "!!i. rev (take i xs) = drop (length xs - i) (rev xs)"
apply(induct xs)
 apply auto
apply(case_tac i)
 apply auto
done

lemma rev_drop: "!!i. rev (drop i xs) = take (length xs - i) (rev xs)"
apply(induct xs)
 apply auto
apply(case_tac i)
 apply auto
done

lemma nth_take[simp]: "!!n i. i < n ==> (take n xs)!i = xs!i"
apply(induct xs)
 apply auto
apply(case_tac n)
 apply(blast )
apply(case_tac i)
 apply auto
done

lemma nth_drop[simp]: "!!xs i. n + i <= length xs ==> (drop n xs)!i = xs!(n+i)"
apply(induct n)
 apply auto
apply(case_tac xs)
 apply auto
done

lemma append_eq_conv_conj:
 "!!zs. (xs@ys = zs) = (xs = take (length xs) zs & ys = drop (length xs) zs)"
apply(induct xs)
 apply simp
apply clarsimp
apply(case_tac zs)
apply auto
done

(** takeWhile & dropWhile **)

section "takeWhile & dropWhile"

lemma takeWhile_dropWhile_id[simp]: "takeWhile P xs @ dropWhile P xs = xs"
by(induct xs, auto)

lemma  takeWhile_append1[simp]:
 "\<lbrakk> x:set xs; ~P(x) \<rbrakk> \<Longrightarrow> takeWhile P (xs @ ys) = takeWhile P xs"
by(induct xs, auto)

lemma takeWhile_append2[simp]:
 "(!!x. x : set xs \<Longrightarrow> P(x)) ==> takeWhile P (xs @ ys) = xs @ takeWhile P ys"
by(induct xs, auto)

lemma takeWhile_tail: "~P(x) ==> takeWhile P (xs @ (x#l)) = takeWhile P xs"
by(induct xs, auto)

lemma dropWhile_append1[simp]:
 "\<lbrakk> x : set xs; ~P(x) \<rbrakk> \<Longrightarrow> dropWhile P (xs @ ys) = (dropWhile P xs)@ys"
by(induct xs, auto)

lemma dropWhile_append2[simp]:
 "(!!x. x:set xs \<Longrightarrow> P(x)) ==> dropWhile P (xs @ ys) = dropWhile P ys"
by(induct xs, auto)

lemma set_take_whileD: "x:set(takeWhile P xs) ==> x:set xs & P x"
by(induct xs, auto split:split_if_asm)


(** zip **)
section "zip"

lemma zip_Nil[simp]: "zip [] ys = []"
by(induct ys, auto)

lemma zip_Cons_Cons[simp]: "zip (x#xs) (y#ys) = (x,y)#zip xs ys"
by simp

declare zip_Cons[simp del]

lemma length_zip[simp]:
 "!!xs. length (zip xs ys) = min (length xs) (length ys)"
apply(induct ys)
 apply simp
apply(case_tac xs)
 apply auto
done

lemma zip_append1:
 "!!xs. zip (xs@ys) zs =
        zip xs (take (length xs) zs) @ zip ys (drop (length xs) zs)"
apply(induct zs)
 apply simp
apply(case_tac xs)
 apply simp_all
done

lemma zip_append2:
 "!!ys. zip xs (ys@zs) =
        zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs"
apply(induct xs)
 apply simp
apply(case_tac ys)
 apply simp_all
done

lemma zip_append[simp]:
 "[| length xs = length us; length ys = length vs |] ==> \
\ zip (xs@ys) (us@vs) = zip xs us @ zip ys vs"
by(simp add: zip_append1)

lemma zip_rev:
 "!!xs. length xs = length ys ==> zip (rev xs) (rev ys) = rev (zip xs ys)"
apply(induct ys)
 apply simp
apply(case_tac xs)
 apply simp_all
done

lemma nth_zip[simp]:
"!!i xs. \<lbrakk> i < length xs; i < length ys \<rbrakk> \<Longrightarrow> (zip xs ys)!i = (xs!i, ys!i)"
apply(induct ys)
 apply simp
apply(case_tac xs)
 apply (simp_all add: nth.simps split:nat.split)
done

lemma set_zip:
 "set(zip xs ys) = {(xs!i,ys!i) |i. i < min (length xs) (length ys)}"
by(simp add: set_conv_nth cong: rev_conj_cong)

lemma zip_update:
 "length xs = length ys ==> zip (xs[i:=x]) (ys[i:=y]) = (zip xs ys)[i:=(x,y)]"
by(rule sym, simp add: update_zip)

lemma zip_replicate[simp]:
 "!!j. zip (replicate i x) (replicate j y) = replicate (min i j) (x,y)"
apply(induct i)
 apply auto
apply(case_tac j)
 apply auto
done

(** list_all2 **)
section "list_all2"

lemma list_all2_lengthD: "list_all2 P xs ys ==> length xs = length ys"
by(simp add:list_all2_def)

lemma list_all2_Nil[iff]: "list_all2 P [] ys = (ys=[])"
by(simp add:list_all2_def)

lemma list_all2_Nil2[iff]: "list_all2 P xs [] = (xs=[])"
by(simp add:list_all2_def)

lemma list_all2_Cons[iff]:
 "list_all2 P (x#xs) (y#ys) = (P x y & list_all2 P xs ys)"
by(auto simp add:list_all2_def)

lemma list_all2_Cons1:
 "list_all2 P (x#xs) ys = (? z zs. ys = z#zs & P x z & list_all2 P xs zs)"
by(case_tac ys, auto)

lemma list_all2_Cons2:
 "list_all2 P xs (y#ys) = (? z zs. xs = z#zs & P z y & list_all2 P zs ys)"
by(case_tac xs, auto)

lemma list_all2_rev[iff]:
 "list_all2 P (rev xs) (rev ys) = list_all2 P xs ys"
by(simp add:list_all2_def zip_rev cong:conj_cong)

lemma list_all2_append1:
 "list_all2 P (xs@ys) zs =
  (EX us vs. zs = us@vs & length us = length xs & length vs = length ys &
             list_all2 P xs us & list_all2 P ys vs)"
apply(simp add:list_all2_def zip_append1)
apply(rule iffI)
 apply(rule_tac x = "take (length xs) zs" in exI)
 apply(rule_tac x = "drop (length xs) zs" in exI)
 apply(force split: nat_diff_split simp add:min_def)
apply clarify
apply(simp add: ball_Un)
done

lemma list_all2_append2:
 "list_all2 P xs (ys@zs) =
  (EX us vs. xs = us@vs & length us = length ys & length vs = length zs &
             list_all2 P us ys & list_all2 P vs zs)"
apply(simp add:list_all2_def zip_append2)
apply(rule iffI)
 apply(rule_tac x = "take (length ys) xs" in exI)
 apply(rule_tac x = "drop (length ys) xs" in exI)
 apply(force split: nat_diff_split simp add:min_def)
apply clarify
apply(simp add: ball_Un)
done

lemma list_all2_conv_all_nth:
  "list_all2 P xs ys =
   (length xs = length ys & (!i<length xs. P (xs!i) (ys!i)))"
by(force simp add:list_all2_def set_zip)

lemma list_all2_trans[rule_format]:
 "ALL a b c. P1 a b --> P2 b c --> P3 a c ==>
  ALL bs cs. list_all2 P1 as bs --> list_all2 P2 bs cs --> list_all2 P3 as cs"
apply(induct_tac as)
 apply simp
apply(rule allI)
apply(induct_tac bs)
 apply simp
apply(rule allI)
apply(induct_tac cs)
 apply auto
done


section "foldl"

lemma foldl_append[simp]:
 "!!a. foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"
by(induct xs, auto)

(* Note: `n <= foldl op+ n ns' looks simpler, but is more difficult to use
   because it requires an additional transitivity step
*)
lemma start_le_sum: "!!n::nat. m <= n ==> m <= foldl op+ n ns"
by(induct ns, auto)

lemma elem_le_sum: "!!n::nat. n : set ns ==> n <= foldl op+ 0 ns"
by(force intro: start_le_sum simp add:in_set_conv_decomp)

lemma sum_eq_0_conv[iff]:
 "!!m::nat. (foldl op+ m ns = 0) = (m=0 & (!n : set ns. n=0))"
by(induct ns, auto)

(** upto **)

(* Does not terminate! *)
lemma upt_rec: "[i..j(] = (if i<j then i#[Suc i..j(] else [])"
by(induct j, auto)

lemma upt_conv_Nil[simp]: "j<=i ==> [i..j(] = []"
by(subst upt_rec, simp)

(*Only needed if upt_Suc is deleted from the simpset*)
lemma upt_Suc_append: "i<=j ==> [i..(Suc j)(] = [i..j(]@[j]"
by simp

lemma upt_conv_Cons: "i<j ==> [i..j(] = i#[Suc i..j(]"
apply(rule trans)
apply(subst upt_rec)
 prefer 2 apply(rule refl)
apply simp
done

(*LOOPS as a simprule, since j<=j*)
lemma upt_add_eq_append: "i<=j ==> [i..j+k(] = [i..j(]@[j..j+k(]"
by(induct_tac "k", auto)

lemma length_upt[simp]: "length [i..j(] = j-i"
by(induct_tac j, simp, simp add: Suc_diff_le)

lemma nth_upt[simp]: "i+k < j ==> [i..j(] ! k = i+k"
apply(induct j)
apply(auto simp add: less_Suc_eq nth_append split:nat_diff_split)
done

lemma take_upt[simp]: "!!i. i+m <= n ==> take m [i..n(] = [i..i+m(]"
apply(induct m)
 apply simp
apply(subst upt_rec)
apply(rule sym)
apply(subst upt_rec)
apply(simp del: upt.simps)
done

lemma map_Suc_upt: "map Suc [m..n(] = [Suc m..n]"
by(induct n, auto)

lemma nth_map_upt: "!!i. i < n-m ==> (map f [m..n(]) ! i = f(m+i)"
thm diff_induct
apply(induct n m rule: diff_induct)
prefer 3 apply(subst map_Suc_upt[symmetric])
apply(auto simp add: less_diff_conv nth_upt)
done

lemma nth_take_lemma[rule_format]:
 "ALL xs ys. k <= length xs --> k <= length ys
             --> (ALL i. i < k --> xs!i = ys!i)
             --> take k xs = take k ys"
apply(induct_tac k)
apply(simp_all add: less_Suc_eq_0_disj all_conj_distrib)
apply clarify
(*Both lists must be non-empty*)
apply(case_tac xs)
 apply simp
apply(case_tac ys)
 apply clarify
 apply(simp (no_asm_use))
apply clarify
(*prenexing's needed, not miniscoping*)
apply(simp (no_asm_use) add: all_simps[symmetric] del: all_simps)
apply blast
(*prenexing's needed, not miniscoping*)
done

lemma nth_equalityI:
 "[| length xs = length ys; ALL i < length xs. xs!i = ys!i |] ==> xs = ys"
apply(frule nth_take_lemma[OF le_refl eq_imp_le])
apply(simp_all add: take_all)
done

(*The famous take-lemma*)
lemma take_equalityI: "(ALL i. take i xs = take i ys) ==> xs = ys"
apply(drule_tac x = "max (length xs) (length ys)" in spec)
apply(simp add: le_max_iff_disj take_all)
done


(** distinct & remdups **)
section "distinct & remdups"

lemma distinct_append[simp]:
 "distinct(xs@ys) = (distinct xs & distinct ys & set xs Int set ys = {})"
by(induct xs, auto)

lemma set_remdups[simp]: "set(remdups xs) = set xs"
by(induct xs, simp, simp add:insert_absorb)

lemma distinct_remdups[iff]: "distinct(remdups xs)"
by(induct xs, auto)

lemma distinct_filter[simp]: "distinct xs ==> distinct (filter P xs)"
by(induct xs, auto)

(** replicate **)
section "replicate"

lemma length_replicate[simp]: "length(replicate n x) = n"
by(induct n, auto)

lemma map_replicate[simp]: "map f (replicate n x) = replicate n (f x)"
by(induct n, auto)

lemma replicate_app_Cons_same:
 "(replicate n x) @ (x#xs) = x # replicate n x @ xs"
by(induct n, auto)

lemma rev_replicate[simp]: "rev(replicate n x) = replicate n x"
apply(induct n)
 apply simp
apply(simp add: replicate_app_Cons_same)
done

lemma replicate_add: "replicate (n+m) x = replicate n x @ replicate m x"
by(induct n, auto)

lemma hd_replicate[simp]: "n ~= 0 ==> hd(replicate n x) = x"
by(induct n, auto)

lemma tl_replicate[simp]: "n ~= 0 ==> tl(replicate n x) = replicate (n - 1) x"
by(induct n, auto)

lemma last_replicate[rule_format,simp]:
 "n ~= 0 --> last(replicate n x) = x"
by(induct_tac n, auto)

lemma nth_replicate[simp]: "!!i. i<n ==> (replicate n x)!i = x"
apply(induct n)
 apply simp
apply(simp add: nth_Cons split:nat.split)
done

lemma set_replicate_Suc: "set(replicate (Suc n) x) = {x}"
by(induct n, auto)

lemma set_replicate[simp]: "n ~= 0 ==> set(replicate n x) = {x}"
by(fast dest!: not0_implies_Suc intro!: set_replicate_Suc)

lemma set_replicate_conv_if: "set(replicate n x) = (if n=0 then {} else {x})"
by auto

lemma in_set_replicateD: "x : set(replicate n y) ==> x=y"
by(simp add: set_replicate_conv_if split:split_if_asm)


(*** Lexcicographic orderings on lists ***)
section"Lexcicographic orderings on lists"

lemma wf_lexn: "wf r ==> wf(lexn r n)"
apply(induct_tac n)
 apply simp
apply simp
apply(rule wf_subset)
 prefer 2 apply(rule Int_lower1)
apply(rule wf_prod_fun_image)
 prefer 2 apply(rule injI)
apply auto
done

lemma lexn_length:
 "!!xs ys. (xs,ys) : lexn r n ==> length xs = n & length ys = n"
by(induct n, auto)

lemma wf_lex[intro!]: "wf r ==> wf(lex r)"
apply(unfold lex_def)
apply(rule wf_UN)
apply(blast intro: wf_lexn)
apply clarify
apply(rename_tac m n)
apply(subgoal_tac "m ~= n")
 prefer 2 apply blast
apply(blast dest: lexn_length not_sym)
done


lemma lexn_conv:
 "lexn r n =
  {(xs,ys). length xs = n & length ys = n &
            (? xys x y xs' ys'. xs= xys @ x#xs' & ys= xys @ y#ys' & (x,y):r)}"
apply(induct_tac n)
 apply simp
 apply blast
apply(simp add: image_Collect lex_prod_def)
apply auto
  apply blast
 apply(rename_tac a xys x xs' y ys')
 apply(rule_tac x = "a#xys" in exI)
 apply simp
apply(case_tac xys)
 apply simp_all
apply blast
done

lemma lex_conv:
 "lex r =
  {(xs,ys). length xs = length ys &
            (? xys x y xs' ys'. xs= xys @ x#xs' & ys= xys @ y#ys' & (x,y):r)}"
by(force simp add: lex_def lexn_conv)

lemma wf_lexico[intro!]: "wf r ==> wf(lexico r)"
by(unfold lexico_def, blast)

lemma lexico_conv:
"lexico r = {(xs,ys). length xs < length ys |
                      length xs = length ys & (xs,ys) : lex r}"
by(simp add: lexico_def diag_def lex_prod_def measure_def inv_image_def)

lemma Nil_notin_lex[iff]: "([],ys) ~: lex r"
by(simp add:lex_conv)

lemma Nil2_notin_lex[iff]: "(xs,[]) ~: lex r"
by(simp add:lex_conv)

lemma Cons_in_lex[iff]:
 "((x#xs,y#ys) : lex r) =
  ((x,y) : r & length xs = length ys | x=y & (xs,ys) : lex r)"
apply(simp add:lex_conv)
apply(rule iffI)
 prefer 2 apply(blast intro: Cons_eq_appendI)
apply clarify
apply(case_tac xys)
 apply simp
apply simp
apply blast
done


(*** sublist (a generalization of nth to sets) ***)

lemma sublist_empty[simp]: "sublist xs {} = []"
by(auto simp add:sublist_def)

lemma sublist_nil[simp]: "sublist [] A = []"
by(auto simp add:sublist_def)

lemma sublist_shift_lemma:
 "map fst [p:zip xs [i..i + length xs(] . snd p : A] =
  map fst [p:zip xs [0..length xs(] . snd p + i : A]"
apply(induct_tac xs rule: rev_induct)
 apply simp
apply(simp add:add_commute)
done

lemma sublist_append:
 "sublist (l@l') A = sublist l A @ sublist l' {j. j + length l : A}"
apply(unfold sublist_def)
apply(induct_tac l' rule: rev_induct)
 apply simp
apply(simp add: upt_add_eq_append[of 0] zip_append sublist_shift_lemma)
apply(simp add:add_commute)
done

lemma sublist_Cons:
 "sublist (x#l) A = (if 0:A then [x] else []) @ sublist l {j. Suc j : A}"
apply(induct_tac l rule: rev_induct)
 apply(simp add:sublist_def)
apply(simp del: append_Cons add: append_Cons[symmetric] sublist_append)
done

lemma sublist_singleton[simp]: "sublist [x] A = (if 0 : A then [x] else [])"
by(simp add:sublist_Cons)

lemma sublist_upt_eq_take[simp]: "sublist l {..n(} = take n l"
apply(induct_tac l rule: rev_induct)
 apply simp
apply(simp split:nat_diff_split add:sublist_append)
done


lemma take_Cons': "take n (x#xs) = (if n=0 then [] else x # take (n - 1) xs)"
by(case_tac n, simp_all)

lemma drop_Cons': "drop n (x#xs) = (if n=0 then x#xs else drop (n - 1) xs)"
by(case_tac n, simp_all)

lemma nth_Cons': "(x#xs)!n = (if n=0 then x else xs!(n - 1))"
by(case_tac n, simp_all)

lemmas [simp] = take_Cons'[of "number_of v",standard]
                drop_Cons'[of "number_of v",standard]
                nth_Cons'[of "number_of v",standard]

end;
