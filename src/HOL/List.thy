(*  Title:      HOL/List.thy
    Author:     Tobias Nipkow
*)

header {* The datatype of finite lists *}

theory List
imports Plain Relation_Power Presburger Recdef ATP_Linkup
uses "Tools/string_syntax.ML"
begin

datatype 'a list =
    Nil    ("[]")
  | Cons 'a  "'a list"    (infixr "#" 65)

subsection{*Basic list processing functions*}

consts
  filter:: "('a => bool) => 'a list => 'a list"
  concat:: "'a list list => 'a list"
  foldl :: "('b => 'a => 'b) => 'b => 'a list => 'b"
  foldr :: "('a => 'b => 'b) => 'a list => 'b => 'b"
  hd:: "'a list => 'a"
  tl:: "'a list => 'a list"
  last:: "'a list => 'a"
  butlast :: "'a list => 'a list"
  set :: "'a list => 'a set"
  map :: "('a=>'b) => ('a list => 'b list)"
  listsum ::  "'a list => 'a::monoid_add"
  list_update :: "'a list => nat => 'a => 'a list"
  take:: "nat => 'a list => 'a list"
  drop:: "nat => 'a list => 'a list"
  takeWhile :: "('a => bool) => 'a list => 'a list"
  dropWhile :: "('a => bool) => 'a list => 'a list"
  rev :: "'a list => 'a list"
  zip :: "'a list => 'b list => ('a * 'b) list"
  upt :: "nat => nat => nat list" ("(1[_..</_'])")
  remdups :: "'a list => 'a list"
  remove1 :: "'a => 'a list => 'a list"
  removeAll :: "'a => 'a list => 'a list"
  "distinct":: "'a list => bool"
  replicate :: "nat => 'a => 'a list"
  splice :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"


nonterminals lupdbinds lupdbind

syntax
  -- {* list Enumeration *}
  "@list" :: "args => 'a list"    ("[(_)]")

  -- {* Special syntax for filter *}
  "@filter" :: "[pttrn, 'a list, bool] => 'a list"    ("(1[_<-_./ _])")

  -- {* list update *}
  "_lupdbind":: "['a, 'a] => lupdbind"    ("(2_ :=/ _)")
  "" :: "lupdbind => lupdbinds"    ("_")
  "_lupdbinds" :: "[lupdbind, lupdbinds] => lupdbinds"    ("_,/ _")
  "_LUpdate" :: "['a, lupdbinds] => 'a"    ("_/[(_)]" [900,0] 900)

translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
  "[x<-xs . P]"== "filter (%x. P) xs"

  "_LUpdate xs (_lupdbinds b bs)"== "_LUpdate (_LUpdate xs b) bs"
  "xs[i:=x]" == "list_update xs i x"


syntax (xsymbols)
  "@filter" :: "[pttrn, 'a list, bool] => 'a list"("(1[_\<leftarrow>_ ./ _])")
syntax (HTML output)
  "@filter" :: "[pttrn, 'a list, bool] => 'a list"("(1[_\<leftarrow>_ ./ _])")


text {*
  Function @{text size} is overloaded for all datatypes. Users may
  refer to the list version as @{text length}. *}

abbreviation
  length :: "'a list => nat" where
  "length == size"

primrec
  "hd(x#xs) = x"

primrec
  "tl([]) = []"
  "tl(x#xs) = xs"

primrec
  "last(x#xs) = (if xs=[] then x else last xs)"

primrec
  "butlast []= []"
  "butlast(x#xs) = (if xs=[] then [] else x#butlast xs)"

primrec
  "set [] = {}"
  "set (x#xs) = insert x (set xs)"

primrec
  "map f [] = []"
  "map f (x#xs) = f(x)#map f xs"

primrec
  append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65)
where
  append_Nil:"[] @ ys = ys"
  | append_Cons: "(x#xs) @ ys = x # xs @ ys"

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
"listsum [] = 0"
"listsum (x # xs) = x + listsum xs"

primrec
  drop_Nil:"drop n [] = []"
  drop_Cons: "drop n (x#xs) = (case n of 0 => x#xs | Suc(m) => drop m xs)"
  -- {*Warning: simpset does not contain this definition, but separate
       theorems for @{text "n = 0"} and @{text "n = Suc k"} *}

primrec
  take_Nil:"take n [] = []"
  take_Cons: "take n (x#xs) = (case n of 0 => [] | Suc(m) => x # take m xs)"
  -- {*Warning: simpset does not contain this definition, but separate
       theorems for @{text "n = 0"} and @{text "n = Suc k"} *}

primrec nth :: "'a list => nat => 'a" (infixl "!" 100) where
  nth_Cons: "(x#xs)!n = (case n of 0 => x | (Suc k) => xs!k)"
  -- {*Warning: simpset does not contain this definition, but separate
       theorems for @{text "n = 0"} and @{text "n = Suc k"} *}

primrec
  "[][i:=v] = []"
  "(x#xs)[i:=v] = (case i of 0 => v # xs | Suc j => x # xs[j:=v])"

primrec
  "takeWhile P [] = []"
  "takeWhile P (x#xs) = (if P x then x#takeWhile P xs else [])"

primrec
  "dropWhile P [] = []"
  "dropWhile P (x#xs) = (if P x then dropWhile P xs else x#xs)"

primrec
  "zip xs [] = []"
  zip_Cons: "zip xs (y#ys) = (case xs of [] => [] | z#zs => (z,y)#zip zs ys)"
  -- {*Warning: simpset does not contain this definition, but separate
       theorems for @{text "xs = []"} and @{text "xs = z # zs"} *}

primrec
  upt_0: "[i..<0] = []"
  upt_Suc: "[i..<(Suc j)] = (if i <= j then [i..<j] @ [j] else [])"

primrec
  "distinct [] = True"
  "distinct (x#xs) = (x ~: set xs \<and> distinct xs)"

primrec
  "remdups [] = []"
  "remdups (x#xs) = (if x : set xs then remdups xs else x # remdups xs)"

primrec
  "remove1 x [] = []"
  "remove1 x (y#xs) = (if x=y then xs else y # remove1 x xs)"

primrec
  "removeAll x [] = []"
  "removeAll x (y#xs) = (if x=y then removeAll x xs else y # removeAll x xs)"

primrec
  replicate_0: "replicate 0 x = []"
  replicate_Suc: "replicate (Suc n) x = x # replicate n x"

definition
  rotate1 :: "'a list \<Rightarrow> 'a list" where
  "rotate1 xs = (case xs of [] \<Rightarrow> [] | x#xs \<Rightarrow> xs @ [x])"

definition
  rotate :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rotate n = rotate1 ^ n"

definition
  list_all2 :: "('a => 'b => bool) => 'a list => 'b list => bool" where
  [code del]: "list_all2 P xs ys =
    (length xs = length ys \<and> (\<forall>(x, y) \<in> set (zip xs ys). P x y))"

definition
  sublist :: "'a list => nat set => 'a list" where
  "sublist xs A = map fst (filter (\<lambda>p. snd p \<in> A) (zip xs [0..<size xs]))"

primrec
  "splice [] ys = ys"
  "splice (x#xs) ys = (if ys=[] then x#xs else x # hd ys # splice xs (tl ys))"
    -- {*Warning: simpset does not contain the second eqn but a derived one. *}

text{*
\begin{figure}[htbp]
\fbox{
\begin{tabular}{l}
@{lemma "[a,b]@[c,d] = [a,b,c,d]" by simp}\\
@{lemma "length [a,b,c] = 3" by simp}\\
@{lemma "set [a,b,c] = {a,b,c}" by simp}\\
@{lemma "map f [a,b,c] = [f a, f b, f c]" by simp}\\
@{lemma "rev [a,b,c] = [c,b,a]" by simp}\\
@{lemma "hd [a,b,c,d] = a" by simp}\\
@{lemma "tl [a,b,c,d] = [b,c,d]" by simp}\\
@{lemma "last [a,b,c,d] = d" by simp}\\
@{lemma "butlast [a,b,c,d] = [a,b,c]" by simp}\\
@{lemma[source] "filter (\<lambda>n::nat. n<2) [0,2,1] = [0,1]" by simp}\\
@{lemma "concat [[a,b],[c,d,e],[],[f]] = [a,b,c,d,e,f]" by simp}\\
@{lemma "foldl f x [a,b,c] = f (f (f x a) b) c" by simp}\\
@{lemma "foldr f [a,b,c] x = f a (f b (f c x))" by simp}\\
@{lemma "zip [a,b,c] [x,y,z] = [(a,x),(b,y),(c,z)]" by simp}\\
@{lemma "zip [a,b] [x,y,z] = [(a,x),(b,y)]" by simp}\\
@{lemma "splice [a,b,c] [x,y,z] = [a,x,b,y,c,z]" by simp}\\
@{lemma "splice [a,b,c,d] [x,y] = [a,x,b,y,c,d]" by simp}\\
@{lemma "take 2 [a,b,c,d] = [a,b]" by simp}\\
@{lemma "take 6 [a,b,c,d] = [a,b,c,d]" by simp}\\
@{lemma "drop 2 [a,b,c,d] = [c,d]" by simp}\\
@{lemma "drop 6 [a,b,c,d] = []" by simp}\\
@{lemma "takeWhile (%n::nat. n<3) [1,2,3,0] = [1,2]" by simp}\\
@{lemma "dropWhile (%n::nat. n<3) [1,2,3,0] = [3,0]" by simp}\\
@{lemma "distinct [2,0,1::nat]" by simp}\\
@{lemma "remdups [2,0,2,1::nat,2] = [0,1,2]" by simp}\\
@{lemma "remove1 2 [2,0,2,1::nat,2] = [0,2,1,2]" by simp}\\
@{lemma "removeAll 2 [2,0,2,1::nat,2] = [0,1]" by simp}\\
@{lemma "nth [a,b,c,d] 2 = c" by simp}\\
@{lemma "[a,b,c,d][2 := x] = [a,b,x,d]" by simp}\\
@{lemma "sublist [a,b,c,d,e] {0,2,3} = [a,c,d]" by (simp add:sublist_def)}\\
@{lemma "rotate1 [a,b,c,d] = [b,c,d,a]" by (simp add:rotate1_def)}\\
@{lemma "rotate 3 [a,b,c,d] = [d,a,b,c]" by (simp add:rotate1_def rotate_def nat_number)}\\
@{lemma "replicate 4 a = [a,a,a,a]" by (simp add:nat_number)}\\
@{lemma "[2..<5] = [2,3,4]" by (simp add:nat_number)}\\
@{lemma "listsum [1,2,3::nat] = 6" by simp}
\end{tabular}}
\caption{Characteristic examples}
\label{fig:Characteristic}
\end{figure}
Figure~\ref{fig:Characteristic} shows characteristic examples
that should give an intuitive understanding of the above functions.
*}

text{* The following simple sort functions are intended for proofs,
not for efficient implementations. *}

context linorder
begin

fun sorted :: "'a list \<Rightarrow> bool" where
"sorted [] \<longleftrightarrow> True" |
"sorted [x] \<longleftrightarrow> True" |
"sorted (x#y#zs) \<longleftrightarrow> x <= y \<and> sorted (y#zs)"

primrec insort :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insort x [] = [x]" |
"insort x (y#ys) = (if x <= y then (x#y#ys) else y#(insort x ys))"

primrec sort :: "'a list \<Rightarrow> 'a list" where
"sort [] = []" |
"sort (x#xs) = insort x (sort xs)"

end


subsubsection {* List comprehension *}

text{* Input syntax for Haskell-like list comprehension notation.
Typical example: @{text"[(x,y). x \<leftarrow> xs, y \<leftarrow> ys, x \<noteq> y]"},
the list of all pairs of distinct elements from @{text xs} and @{text ys}.
The syntax is as in Haskell, except that @{text"|"} becomes a dot
(like in Isabelle's set comprehension): @{text"[e. x \<leftarrow> xs, \<dots>]"} rather than
\verb![e| x <- xs, ...]!.

The qualifiers after the dot are
\begin{description}
\item[generators] @{text"p \<leftarrow> xs"},
 where @{text p} is a pattern and @{text xs} an expression of list type, or
\item[guards] @{text"b"}, where @{text b} is a boolean expression.
%\item[local bindings] @ {text"let x = e"}.
\end{description}

Just like in Haskell, list comprehension is just a shorthand. To avoid
misunderstandings, the translation into desugared form is not reversed
upon output. Note that the translation of @{text"[e. x \<leftarrow> xs]"} is
optmized to @{term"map (%x. e) xs"}.

It is easy to write short list comprehensions which stand for complex
expressions. During proofs, they may become unreadable (and
mangled). In such cases it can be advisable to introduce separate
definitions for the list comprehensions in question.  *}

(*
Proper theorem proving support would be nice. For example, if
@{text"set[f x y. x \<leftarrow> xs, y \<leftarrow> ys, P x y]"}
produced something like
@{term"{z. EX x: set xs. EX y:set ys. P x y \<and> z = f x y}"}.
*)

nonterminals lc_qual lc_quals

syntax
"_listcompr" :: "'a \<Rightarrow> lc_qual \<Rightarrow> lc_quals \<Rightarrow> 'a list"  ("[_ . __")
"_lc_gen" :: "'a \<Rightarrow> 'a list \<Rightarrow> lc_qual" ("_ <- _")
"_lc_test" :: "bool \<Rightarrow> lc_qual" ("_")
(*"_lc_let" :: "letbinds => lc_qual"  ("let _")*)
"_lc_end" :: "lc_quals" ("]")
"_lc_quals" :: "lc_qual \<Rightarrow> lc_quals \<Rightarrow> lc_quals" (", __")
"_lc_abs" :: "'a => 'b list => 'b list"

(* These are easier than ML code but cannot express the optimized
   translation of [e. p<-xs]
translations
"[e. p<-xs]" => "concat(map (_lc_abs p [e]) xs)"
"_listcompr e (_lc_gen p xs) (_lc_quals Q Qs)"
 => "concat (map (_lc_abs p (_listcompr e Q Qs)) xs)"
"[e. P]" => "if P then [e] else []"
"_listcompr e (_lc_test P) (_lc_quals Q Qs)"
 => "if P then (_listcompr e Q Qs) else []"
"_listcompr e (_lc_let b) (_lc_quals Q Qs)"
 => "_Let b (_listcompr e Q Qs)"
*)

syntax (xsymbols)
"_lc_gen" :: "'a \<Rightarrow> 'a list \<Rightarrow> lc_qual" ("_ \<leftarrow> _")
syntax (HTML output)
"_lc_gen" :: "'a \<Rightarrow> 'a list \<Rightarrow> lc_qual" ("_ \<leftarrow> _")

parse_translation (advanced) {*
let
  val NilC = Syntax.const @{const_name Nil};
  val ConsC = Syntax.const @{const_name Cons};
  val mapC = Syntax.const @{const_name map};
  val concatC = Syntax.const @{const_name concat};
  val IfC = Syntax.const @{const_name If};
  fun singl x = ConsC $ x $ NilC;

   fun pat_tr ctxt p e opti = (* %x. case x of p => e | _ => [] *)
    let
      val x = Free (Name.variant (fold Term.add_free_names [p, e] []) "x", dummyT);
      val e = if opti then singl e else e;
      val case1 = Syntax.const "_case1" $ p $ e;
      val case2 = Syntax.const "_case1" $ Syntax.const Term.dummy_patternN
                                        $ NilC;
      val cs = Syntax.const "_case2" $ case1 $ case2
      val ft = DatatypeCase.case_tr false DatatypePackage.datatype_of_constr
                 ctxt [x, cs]
    in lambda x ft end;

  fun abs_tr ctxt (p as Free(s,T)) e opti =
        let val thy = ProofContext.theory_of ctxt;
            val s' = Sign.intern_const thy s
        in if Sign.declared_const thy s'
           then (pat_tr ctxt p e opti, false)
           else (lambda p e, true)
        end
    | abs_tr ctxt p e opti = (pat_tr ctxt p e opti, false);

  fun lc_tr ctxt [e, Const("_lc_test",_)$b, qs] =
        let val res = case qs of Const("_lc_end",_) => singl e
                      | Const("_lc_quals",_)$q$qs => lc_tr ctxt [e,q,qs];
        in IfC $ b $ res $ NilC end
    | lc_tr ctxt [e, Const("_lc_gen",_) $ p $ es, Const("_lc_end",_)] =
        (case abs_tr ctxt p e true of
           (f,true) => mapC $ f $ es
         | (f, false) => concatC $ (mapC $ f $ es))
    | lc_tr ctxt [e, Const("_lc_gen",_) $ p $ es, Const("_lc_quals",_)$q$qs] =
        let val e' = lc_tr ctxt [e,q,qs];
        in concatC $ (mapC $ (fst(abs_tr ctxt p e' false)) $ es) end

in [("_listcompr", lc_tr)] end
*}

(*
term "[(x,y,z). b]"
term "[(x,y,z). x\<leftarrow>xs]"
term "[e x y. x\<leftarrow>xs, y\<leftarrow>ys]"
term "[(x,y,z). x<a, x>b]"
term "[(x,y,z). x\<leftarrow>xs, x>b]"
term "[(x,y,z). x<a, x\<leftarrow>xs]"
term "[(x,y). Cons True x \<leftarrow> xs]"
term "[(x,y,z). Cons x [] \<leftarrow> xs]"
term "[(x,y,z). x<a, x>b, x=d]"
term "[(x,y,z). x<a, x>b, y\<leftarrow>ys]"
term "[(x,y,z). x<a, x\<leftarrow>xs,y>b]"
term "[(x,y,z). x<a, x\<leftarrow>xs, y\<leftarrow>ys]"
term "[(x,y,z). x\<leftarrow>xs, x>b, y<a]"
term "[(x,y,z). x\<leftarrow>xs, x>b, y\<leftarrow>ys]"
term "[(x,y,z). x\<leftarrow>xs, y\<leftarrow>ys,y>x]"
term "[(x,y,z). x\<leftarrow>xs, y\<leftarrow>ys,z\<leftarrow>zs]"
term "[(x,y). x\<leftarrow>xs, let xx = x+x, y\<leftarrow>ys, y \<noteq> xx]"
*)

subsubsection {* @{const Nil} and @{const Cons} *}

lemma not_Cons_self [simp]:
  "xs \<noteq> x # xs"
by (induct xs) auto

lemmas not_Cons_self2 [simp] = not_Cons_self [symmetric]

lemma neq_Nil_conv: "(xs \<noteq> []) = (\<exists>y ys. xs = y # ys)"
by (induct xs) auto

lemma length_induct:
  "(\<And>xs. \<forall>ys. length ys < length xs \<longrightarrow> P ys \<Longrightarrow> P xs) \<Longrightarrow> P xs"
by (rule measure_induct [of length]) iprover


subsubsection {* @{const length} *}

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

lemma length_pos_if_in_set: "x : set xs \<Longrightarrow> length xs > 0"
by auto

lemma length_Suc_conv:
"(length xs = Suc n) = (\<exists>y ys. xs = y # ys \<and> length ys = n)"
by (induct xs) auto

lemma Suc_length_conv:
"(Suc n = length xs) = (\<exists>y ys. xs = y # ys \<and> length ys = n)"
apply (induct xs, simp, simp)
apply blast
done

lemma impossible_Cons: "length xs <= length ys ==> xs = x # ys = False"
  by (induct xs) auto

lemma list_induct2 [consumes 1, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (x#xs) (y#ys))
   \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs ys) then show ?case by (cases ys) simp_all
qed

lemma list_induct3 [consumes 2, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P [] [] [] \<Longrightarrow>
   (\<And>x xs y ys z zs. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (x#xs) (y#ys) (z#zs))
   \<Longrightarrow> P xs ys zs"
proof (induct xs arbitrary: ys zs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs) then show ?case by (cases ys, simp_all)
    (cases zs, simp_all)
qed

lemma list_induct2': 
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
by (induct xs arbitrary: ys) (case_tac x, auto)+

lemma neq_if_length_neq: "length xs \<noteq> length ys \<Longrightarrow> (xs = ys) == False"
by (rule Eq_FalseI) auto

simproc_setup list_neq ("(xs::'a list) = ys") = {*
(*
Reduces xs=ys to False if xs and ys cannot be of the same length.
This is the case if the atomic sublists of one are a submultiset
of those of the other list and there are fewer Cons's in one than the other.
*)

let

fun len (Const(@{const_name Nil},_)) acc = acc
  | len (Const(@{const_name Cons},_) $ _ $ xs) (ts,n) = len xs (ts,n+1)
  | len (Const(@{const_name append},_) $ xs $ ys) acc = len xs (len ys acc)
  | len (Const(@{const_name rev},_) $ xs) acc = len xs acc
  | len (Const(@{const_name map},_) $ _ $ xs) acc = len xs acc
  | len t (ts,n) = (t::ts,n);

fun list_neq _ ss ct =
  let
    val (Const(_,eqT) $ lhs $ rhs) = Thm.term_of ct;
    val (ls,m) = len lhs ([],0) and (rs,n) = len rhs ([],0);
    fun prove_neq() =
      let
        val Type(_,listT::_) = eqT;
        val size = HOLogic.size_const listT;
        val eq_len = HOLogic.mk_eq (size $ lhs, size $ rhs);
        val neq_len = HOLogic.mk_Trueprop (HOLogic.Not $ eq_len);
        val thm = Goal.prove (Simplifier.the_context ss) [] [] neq_len
          (K (simp_tac (Simplifier.inherit_context ss @{simpset}) 1));
      in SOME (thm RS @{thm neq_if_length_neq}) end
  in
    if m < n andalso submultiset (op aconv) (ls,rs) orelse
       n < m andalso submultiset (op aconv) (rs,ls)
    then prove_neq() else NONE
  end;
in list_neq end;
*}


subsubsection {* @{text "@"} -- append *}

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

lemma append_eq_append_conv [simp, noatp]:
 "length xs = length ys \<or> length us = length vs
 ==> (xs@us = ys@vs) = (xs=ys \<and> us=vs)"
apply (induct xs arbitrary: ys)
 apply (case_tac ys, simp, force)
apply (case_tac ys, force, simp)
done

lemma append_eq_append_conv2: "(xs @ ys = zs @ ts) =
  (EX us. xs = zs @ us & us @ ys = ts | xs @ us = zs & ys = us@ ts)"
apply (induct xs arbitrary: ys zs ts)
 apply fastsimp
apply(case_tac zs)
 apply simp
apply fastsimp
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

lemma hd_Cons_tl [simp,noatp]: "xs \<noteq> [] ==> hd xs # tl xs = xs"
by (induct xs) auto

lemma hd_append: "hd (xs @ ys) = (if xs = [] then hd ys else hd xs)"
by (induct xs) auto

lemma hd_append2 [simp]: "xs \<noteq> [] ==> hd (xs @ ys) = hd xs"
by (simp add: hd_append split: list.split)

lemma tl_append: "tl (xs @ ys) = (case xs of [] => tl ys | z#zs => zs @ ys)"
by (simp split: list.split)

lemma tl_append2 [simp]: "xs \<noteq> [] ==> tl (xs @ ys) = tl xs @ ys"
by (simp add: tl_append split: list.split)


lemma Cons_eq_append_conv: "x#xs = ys@zs =
 (ys = [] & x#xs = zs | (EX ys'. x#ys' = ys & xs = ys'@zs))"
by(cases ys) auto

lemma append_eq_Cons_conv: "(ys@zs = x#xs) =
 (ys = [] & zs = x#xs | (EX ys'. ys = x#ys' & ys'@zs = xs))"
by(cases ys) auto


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

ML {*
local

fun last (cons as Const(@{const_name Cons},_) $ _ $ xs) =
  (case xs of Const(@{const_name Nil},_) => cons | _ => last xs)
  | last (Const(@{const_name append},_) $ _ $ ys) = last ys
  | last t = t;

fun list1 (Const(@{const_name Cons},_) $ _ $ Const(@{const_name Nil},_)) = true
  | list1 _ = false;

fun butlast ((cons as Const(@{const_name Cons},_) $ x) $ xs) =
  (case xs of Const(@{const_name Nil},_) => xs | _ => cons $ butlast xs)
  | butlast ((app as Const(@{const_name append},_) $ xs) $ ys) = app $ butlast ys
  | butlast xs = Const(@{const_name Nil},fastype_of xs);

val rearr_ss = HOL_basic_ss addsimps [@{thm append_assoc},
  @{thm append_Nil}, @{thm append_Cons}];

fun list_eq ss (F as (eq as Const(_,eqT)) $ lhs $ rhs) =
  let
    val lastl = last lhs and lastr = last rhs;
    fun rearr conv =
      let
        val lhs1 = butlast lhs and rhs1 = butlast rhs;
        val Type(_,listT::_) = eqT
        val appT = [listT,listT] ---> listT
        val app = Const(@{const_name append},appT)
        val F2 = eq $ (app$lhs1$lastl) $ (app$rhs1$lastr)
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (F,F2));
        val thm = Goal.prove (Simplifier.the_context ss) [] [] eq
          (K (simp_tac (Simplifier.inherit_context ss rearr_ss) 1));
      in SOME ((conv RS (thm RS trans)) RS eq_reflection) end;

  in
    if list1 lastl andalso list1 lastr then rearr @{thm append1_eq_conv}
    else if lastl aconv lastr then rearr @{thm append_same_eq}
    else NONE
  end;

in

val list_eq_simproc =
  Simplifier.simproc (the_context ()) "list_eq" ["(xs::'a list) = ys"] (K list_eq);

end;

Addsimprocs [list_eq_simproc];
*}


subsubsection {* @{text map} *}

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

lemma map_eq_conv[simp]: "(map f xs = map g xs) = (!x : set xs. f x = g x)"
by (induct xs) auto

lemma map_cong [fundef_cong, recdef_cong]:
"xs = ys ==> (!!x. x : set ys ==> f x = g x) ==> map f xs = map g ys"
-- {* a congruence rule for @{text map} *}
by simp

lemma map_is_Nil_conv [iff]: "(map f xs = []) = (xs = [])"
by (cases xs) auto

lemma Nil_is_map_conv [iff]: "([] = map f xs) = (xs = [])"
by (cases xs) auto

lemma map_eq_Cons_conv:
 "(map f xs = y#ys) = (\<exists>z zs. xs = z#zs \<and> f z = y \<and> map f zs = ys)"
by (cases xs) auto

lemma Cons_eq_map_conv:
 "(x#xs = map f ys) = (\<exists>z zs. ys = z#zs \<and> x = f z \<and> xs = map f zs)"
by (cases ys) auto

lemmas map_eq_Cons_D = map_eq_Cons_conv [THEN iffD1]
lemmas Cons_eq_map_D = Cons_eq_map_conv [THEN iffD1]
declare map_eq_Cons_D [dest!]  Cons_eq_map_D [dest!]

lemma ex_map_conv:
  "(EX xs. ys = map f xs) = (ALL y : set ys. EX x. y = f x)"
by(induct ys, auto simp add: Cons_eq_map_conv)

lemma map_eq_imp_length_eq:
  assumes "map f xs = map f ys"
  shows "length xs = length ys"
using assms proof (induct ys arbitrary: xs)
  case Nil then show ?case by simp
next
  case (Cons y ys) then obtain z zs where xs: "xs = z # zs" by auto
  from Cons xs have "map f zs = map f ys" by simp
  moreover with Cons have "length zs = length ys" by blast
  with xs show ?case by simp
qed
  
lemma map_inj_on:
 "[| map f xs = map f ys; inj_on f (set xs Un set ys) |]
  ==> xs = ys"
apply(frule map_eq_imp_length_eq)
apply(rotate_tac -1)
apply(induct rule:list_induct2)
 apply simp
apply(simp)
apply (blast intro:sym)
done

lemma inj_on_map_eq_map:
 "inj_on f (set xs Un set ys) \<Longrightarrow> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_inj_on)

lemma map_injective:
 "map f xs = map f ys ==> inj f ==> xs = ys"
by (induct ys arbitrary: xs) (auto dest!:injD)

lemma inj_map_eq_map[simp]: "inj f \<Longrightarrow> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_injective)

lemma inj_mapI: "inj f ==> inj (map f)"
by (iprover dest: map_injective injD intro: inj_onI)

lemma inj_mapD: "inj (map f) ==> inj f"
apply (unfold inj_on_def, clarify)
apply (erule_tac x = "[x]" in ballE)
 apply (erule_tac x = "[y]" in ballE, simp, blast)
apply blast
done

lemma inj_map[iff]: "inj (map f) = inj f"
by (blast dest: inj_mapD intro: inj_mapI)

lemma inj_on_mapI: "inj_on f (\<Union>(set ` A)) \<Longrightarrow> inj_on (map f) A"
apply(rule inj_onI)
apply(erule map_inj_on)
apply(blast intro:inj_onI dest:inj_onD)
done

lemma map_idI: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = x) \<Longrightarrow> map f xs = xs"
by (induct xs, auto)

lemma map_fun_upd [simp]: "y \<notin> set xs \<Longrightarrow> map (f(y:=v)) xs = map f xs"
by (induct xs) auto

lemma map_fst_zip[simp]:
  "length xs = length ys \<Longrightarrow> map fst (zip xs ys) = xs"
by (induct rule:list_induct2, simp_all)

lemma map_snd_zip[simp]:
  "length xs = length ys \<Longrightarrow> map snd (zip xs ys) = ys"
by (induct rule:list_induct2, simp_all)


subsubsection {* @{text rev} *}

lemma rev_append [simp]: "rev (xs @ ys) = rev ys @ rev xs"
by (induct xs) auto

lemma rev_rev_ident [simp]: "rev (rev xs) = xs"
by (induct xs) auto

lemma rev_swap: "(rev xs = ys) = (xs = rev ys)"
by auto

lemma rev_is_Nil_conv [iff]: "(rev xs = []) = (xs = [])"
by (induct xs) auto

lemma Nil_is_rev_conv [iff]: "([] = rev xs) = (xs = [])"
by (induct xs) auto

lemma rev_singleton_conv [simp]: "(rev xs = [x]) = (xs = [x])"
by (cases xs) auto

lemma singleton_rev_conv [simp]: "([x] = rev xs) = (xs = [x])"
by (cases xs) auto

lemma rev_is_rev_conv [iff]: "(rev xs = rev ys) = (xs = ys)"
apply (induct xs arbitrary: ys, force)
apply (case_tac ys, simp, force)
done

lemma inj_on_rev[iff]: "inj_on rev A"
by(simp add:inj_on_def)

lemma rev_induct [case_names Nil snoc]:
  "[| P []; !!x xs. P xs ==> P (xs @ [x]) |] ==> P xs"
apply(simplesubst rev_rev_ident[symmetric])
apply(rule_tac list = "rev xs" in list.induct, simp_all)
done

lemma rev_exhaust [case_names Nil snoc]:
  "(xs = [] ==> P) ==>(!!ys y. xs = ys @ [y] ==> P) ==> P"
by (induct xs rule: rev_induct) auto

lemmas rev_cases = rev_exhaust

lemma rev_eq_Cons_iff[iff]: "(rev xs = y#ys) = (xs = rev ys @ [y])"
by(rule rev_cases[of xs]) auto


subsubsection {* @{text set} *}

lemma finite_set [iff]: "finite (set xs)"
by (induct xs) auto

lemma set_append [simp]: "set (xs @ ys) = (set xs \<union> set ys)"
by (induct xs) auto

lemma hd_in_set[simp]: "xs \<noteq> [] \<Longrightarrow> hd xs : set xs"
by(cases xs) auto

lemma set_subset_Cons: "set xs \<subseteq> set (x # xs)"
by auto

lemma set_ConsD: "y \<in> set (x # xs) \<Longrightarrow> y=x \<or> y \<in> set xs" 
by auto

lemma set_empty [iff]: "(set xs = {}) = (xs = [])"
by (induct xs) auto

lemma set_empty2[iff]: "({} = set xs) = (xs = [])"
by(induct xs) auto

lemma set_rev [simp]: "set (rev xs) = set xs"
by (induct xs) auto

lemma set_map [simp]: "set (map f xs) = f`(set xs)"
by (induct xs) auto

lemma set_filter [simp]: "set (filter P xs) = {x. x : set xs \<and> P x}"
by (induct xs) auto

lemma set_upt [simp]: "set[i..<j] = {k. i \<le> k \<and> k < j}"
apply (induct j, simp_all)
apply (erule ssubst, auto)
done


lemma split_list: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case Cons thus ?case by (auto intro: Cons_eq_appendI)
qed

lemma in_set_conv_decomp: "x \<in> set xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ x # zs)"
  by (auto elim: split_list)

lemma split_list_first: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof cases
    assume "x = a" thus ?case using Cons by fastsimp
  next
    assume "x \<noteq> a" thus ?case using Cons by(fastsimp intro!: Cons_eq_appendI)
  qed
qed

lemma in_set_conv_decomp_first:
  "(x : set xs) = (\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys)"
  by (auto dest!: split_list_first)

lemma split_list_last: "x : set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set zs"
proof (induct xs rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a xs)
  show ?case
  proof cases
    assume "x = a" thus ?case using snoc by simp (metis ex_in_conv set_empty2)
  next
    assume "x \<noteq> a" thus ?case using snoc by fastsimp
  qed
qed

lemma in_set_conv_decomp_last:
  "(x : set xs) = (\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set zs)"
  by (auto dest!: split_list_last)

lemma split_list_prop: "\<exists>x \<in> set xs. P x \<Longrightarrow> \<exists>ys x zs. xs = ys @ x # zs & P x"
proof (induct xs)
  case Nil thus ?case by simp
next
  case Cons thus ?case
    by(simp add:Bex_def)(metis append_Cons append.simps(1))
qed

lemma split_list_propE:
  assumes "\<exists>x \<in> set xs. P x"
  obtains ys x zs where "xs = ys @ x # zs" and "P x"
using split_list_prop [OF assms] by blast

lemma split_list_first_prop:
  "\<exists>x \<in> set xs. P x \<Longrightarrow>
   \<exists>ys x zs. xs = ys@x#zs \<and> P x \<and> (\<forall>y \<in> set ys. \<not> P y)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof cases
    assume "P x"
    thus ?thesis by simp
      (metis Un_upper1 contra_subsetD in_set_conv_decomp_first self_append_conv2 set_append)
  next
    assume "\<not> P x"
    hence "\<exists>x\<in>set xs. P x" using Cons(2) by simp
    thus ?thesis using `\<not> P x` Cons(1) by (metis append_Cons set_ConsD)
  qed
qed

lemma split_list_first_propE:
  assumes "\<exists>x \<in> set xs. P x"
  obtains ys x zs where "xs = ys @ x # zs" and "P x" and "\<forall>y \<in> set ys. \<not> P y"
using split_list_first_prop [OF assms] by blast

lemma split_list_first_prop_iff:
  "(\<exists>x \<in> set xs. P x) \<longleftrightarrow>
   (\<exists>ys x zs. xs = ys@x#zs \<and> P x \<and> (\<forall>y \<in> set ys. \<not> P y))"
by (rule, erule split_list_first_prop) auto

lemma split_list_last_prop:
  "\<exists>x \<in> set xs. P x \<Longrightarrow>
   \<exists>ys x zs. xs = ys@x#zs \<and> P x \<and> (\<forall>z \<in> set zs. \<not> P z)"
proof(induct xs rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  show ?case
  proof cases
    assume "P x" thus ?thesis by (metis emptyE set_empty)
  next
    assume "\<not> P x"
    hence "\<exists>x\<in>set xs. P x" using snoc(2) by simp
    thus ?thesis using `\<not> P x` snoc(1) by fastsimp
  qed
qed

lemma split_list_last_propE:
  assumes "\<exists>x \<in> set xs. P x"
  obtains ys x zs where "xs = ys @ x # zs" and "P x" and "\<forall>z \<in> set zs. \<not> P z"
using split_list_last_prop [OF assms] by blast

lemma split_list_last_prop_iff:
  "(\<exists>x \<in> set xs. P x) \<longleftrightarrow>
   (\<exists>ys x zs. xs = ys@x#zs \<and> P x \<and> (\<forall>z \<in> set zs. \<not> P z))"
by (metis split_list_last_prop [where P=P] in_set_conv_decomp)

lemma finite_list: "finite A ==> EX xs. set xs = A"
  by (erule finite_induct)
    (auto simp add: set.simps(2) [symmetric] simp del: set.simps(2))

lemma card_length: "card (set xs) \<le> length xs"
by (induct xs) (auto simp add: card_insert_if)

lemma set_minus_filter_out:
  "set xs - {y} = set (filter (\<lambda>x. \<not> (x = y)) xs)"
  by (induct xs) auto

subsubsection {* @{text filter} *}

lemma filter_append [simp]: "filter P (xs @ ys) = filter P xs @ filter P ys"
by (induct xs) auto

lemma rev_filter: "rev (filter P xs) = filter P (rev xs)"
by (induct xs) simp_all

lemma filter_filter [simp]: "filter P (filter Q xs) = filter (\<lambda>x. Q x \<and> P x) xs"
by (induct xs) auto

lemma length_filter_le [simp]: "length (filter P xs) \<le> length xs"
by (induct xs) (auto simp add: le_SucI)

lemma sum_length_filter_compl:
  "length(filter P xs) + length(filter (%x. ~P x) xs) = length xs"
by(induct xs) simp_all

lemma filter_True [simp]: "\<forall>x \<in> set xs. P x ==> filter P xs = xs"
by (induct xs) auto

lemma filter_False [simp]: "\<forall>x \<in> set xs. \<not> P x ==> filter P xs = []"
by (induct xs) auto

lemma filter_empty_conv: "(filter P xs = []) = (\<forall>x\<in>set xs. \<not> P x)" 
by (induct xs) simp_all

lemma filter_id_conv: "(filter P xs = xs) = (\<forall>x\<in>set xs. P x)"
apply (induct xs)
 apply auto
apply(cut_tac P=P and xs=xs in length_filter_le)
apply simp
done

lemma filter_map:
  "filter P (map f xs) = map f (filter (P o f) xs)"
by (induct xs) simp_all

lemma length_filter_map[simp]:
  "length (filter P (map f xs)) = length(filter (P o f) xs)"
by (simp add:filter_map)

lemma filter_is_subset [simp]: "set (filter P xs) \<le> set xs"
by auto

lemma length_filter_less:
  "\<lbrakk> x : set xs; ~ P x \<rbrakk> \<Longrightarrow> length(filter P xs) < length xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case
    apply (auto split:split_if_asm)
    using length_filter_le[of P xs] apply arith
  done
qed

lemma length_filter_conv_card:
 "length(filter p xs) = card{i. i < length xs & p(xs!i)}"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  let ?S = "{i. i < length xs & p(xs!i)}"
  have fin: "finite ?S" by(fast intro: bounded_nat_set_is_finite)
  show ?case (is "?l = card ?S'")
  proof (cases)
    assume "p x"
    hence eq: "?S' = insert 0 (Suc ` ?S)"
      by(auto simp: image_def split:nat.split dest:gr0_implies_Suc)
    have "length (filter p (x # xs)) = Suc(card ?S)"
      using Cons `p x` by simp
    also have "\<dots> = Suc(card(Suc ` ?S))" using fin
      by (simp add: card_image inj_Suc)
    also have "\<dots> = card ?S'" using eq fin
      by (simp add:card_insert_if) (simp add:image_def)
    finally show ?thesis .
  next
    assume "\<not> p x"
    hence eq: "?S' = Suc ` ?S"
      by(auto simp add: image_def split:nat.split elim:lessE)
    have "length (filter p (x # xs)) = card ?S"
      using Cons `\<not> p x` by simp
    also have "\<dots> = card(Suc ` ?S)" using fin
      by (simp add: card_image inj_Suc)
    also have "\<dots> = card ?S'" using eq fin
      by (simp add:card_insert_if)
    finally show ?thesis .
  qed
qed

lemma Cons_eq_filterD:
 "x#xs = filter P ys \<Longrightarrow>
  \<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> xs = filter P vs"
  (is "_ \<Longrightarrow> \<exists>us vs. ?P ys us vs")
proof(induct ys)
  case Nil thus ?case by simp
next
  case (Cons y ys)
  show ?case (is "\<exists>x. ?Q x")
  proof cases
    assume Py: "P y"
    show ?thesis
    proof cases
      assume "x = y"
      with Py Cons.prems have "?Q []" by simp
      then show ?thesis ..
    next
      assume "x \<noteq> y"
      with Py Cons.prems show ?thesis by simp
    qed
  next
    assume "\<not> P y"
    with Cons obtain us vs where "?P (y#ys) (y#us) vs" by fastsimp
    then have "?Q (y#us)" by simp
    then show ?thesis ..
  qed
qed

lemma filter_eq_ConsD:
 "filter P ys = x#xs \<Longrightarrow>
  \<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> xs = filter P vs"
by(rule Cons_eq_filterD) simp

lemma filter_eq_Cons_iff:
 "(filter P ys = x#xs) =
  (\<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> xs = filter P vs)"
by(auto dest:filter_eq_ConsD)

lemma Cons_eq_filter_iff:
 "(x#xs = filter P ys) =
  (\<exists>us vs. ys = us @ x # vs \<and> (\<forall>u\<in>set us. \<not> P u) \<and> P x \<and> xs = filter P vs)"
by(auto dest:Cons_eq_filterD)

lemma filter_cong[fundef_cong, recdef_cong]:
 "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> P x = Q x) \<Longrightarrow> filter P xs = filter Q ys"
apply simp
apply(erule thin_rl)
by (induct ys) simp_all


subsubsection {* List partitioning *}

primrec partition :: "('a \<Rightarrow> bool) \<Rightarrow>'a list \<Rightarrow> 'a list \<times> 'a list" where
  "partition P [] = ([], [])"
  | "partition P (x # xs) = 
      (let (yes, no) = partition P xs
      in if P x then (x # yes, no) else (yes, x # no))"

lemma partition_filter1:
    "fst (partition P xs) = filter P xs"
by (induct xs) (auto simp add: Let_def split_def)

lemma partition_filter2:
    "snd (partition P xs) = filter (Not o P) xs"
by (induct xs) (auto simp add: Let_def split_def)

lemma partition_P:
  assumes "partition P xs = (yes, no)"
  shows "(\<forall>p \<in> set yes.  P p) \<and> (\<forall>p  \<in> set no. \<not> P p)"
proof -
  from assms have "yes = fst (partition P xs)" and "no = snd (partition P xs)"
    by simp_all
  then show ?thesis by (simp_all add: partition_filter1 partition_filter2)
qed

lemma partition_set:
  assumes "partition P xs = (yes, no)"
  shows "set yes \<union> set no = set xs"
proof -
  from assms have "yes = fst (partition P xs)" and "no = snd (partition P xs)"
    by simp_all
  then show ?thesis by (auto simp add: partition_filter1 partition_filter2) 
qed


subsubsection {* @{text concat} *}

lemma concat_append [simp]: "concat (xs @ ys) = concat xs @ concat ys"
by (induct xs) auto

lemma concat_eq_Nil_conv [simp]: "(concat xss = []) = (\<forall>xs \<in> set xss. xs = [])"
by (induct xss) auto

lemma Nil_eq_concat_conv [simp]: "([] = concat xss) = (\<forall>xs \<in> set xss. xs = [])"
by (induct xss) auto

lemma set_concat [simp]: "set (concat xs) = (UN x:set xs. set x)"
by (induct xs) auto

lemma concat_map_singleton[simp]: "concat(map (%x. [f x]) xs) = map f xs"
by (induct xs) auto

lemma map_concat: "map f (concat xs) = concat (map (map f) xs)"
by (induct xs) auto

lemma filter_concat: "filter p (concat xs) = concat (map (filter p) xs)"
by (induct xs) auto

lemma rev_concat: "rev (concat xs) = concat (map rev (rev xs))"
by (induct xs) auto


subsubsection {* @{text nth} *}

lemma nth_Cons_0 [simp, code]: "(x # xs)!0 = x"
by auto

lemma nth_Cons_Suc [simp, code]: "(x # xs)!(Suc n) = xs!n"
by auto

declare nth.simps [simp del]

lemma nth_append:
  "(xs @ ys)!n = (if n < length xs then xs!n else ys!(n - length xs))"
apply (induct xs arbitrary: n, simp)
apply (case_tac n, auto)
done

lemma nth_append_length [simp]: "(xs @ x # ys) ! length xs = x"
by (induct xs) auto

lemma nth_append_length_plus[simp]: "(xs @ ys) ! (length xs + n) = ys ! n"
by (induct xs) auto

lemma nth_map [simp]: "n < length xs ==> (map f xs)!n = f(xs!n)"
apply (induct xs arbitrary: n, simp)
apply (case_tac n, auto)
done

lemma hd_conv_nth: "xs \<noteq> [] \<Longrightarrow> hd xs = xs!0"
by(cases xs) simp_all


lemma list_eq_iff_nth_eq:
 "(xs = ys) = (length xs = length ys \<and> (ALL i<length xs. xs!i = ys!i))"
apply(induct xs arbitrary: ys)
 apply force
apply(case_tac ys)
 apply simp
apply(simp add:nth_Cons split:nat.split)apply blast
done

lemma set_conv_nth: "set xs = {xs!i | i. i < length xs}"
apply (induct xs, simp, simp)
apply safe
apply (metis nat_case_0 nth.simps zero_less_Suc)
apply (metis less_Suc_eq_0_disj nth_Cons_Suc)
apply (case_tac i, simp)
apply (metis diff_Suc_Suc nat_case_Suc nth.simps zero_less_diff)
done

lemma in_set_conv_nth: "(x \<in> set xs) = (\<exists>i < length xs. xs!i = x)"
by(auto simp:set_conv_nth)

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

lemma rev_nth:
  "n < size xs \<Longrightarrow> rev xs ! n = xs ! (length xs - Suc n)"
proof (induct xs arbitrary: n)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  hence n: "n < Suc (length xs)" by simp
  moreover
  { assume "n < length xs"
    with n obtain n' where "length xs - n = Suc n'"
      by (cases "length xs - n", auto)
    moreover
    then have "length xs - Suc n = n'" by simp
    ultimately
    have "xs ! (length xs - Suc n) = (x # xs) ! (length xs - n)" by simp
  }
  ultimately
  show ?case by (clarsimp simp add: Cons nth_append)
qed

subsubsection {* @{text list_update} *}

lemma length_list_update [simp]: "length(xs[i:=x]) = length xs"
by (induct xs arbitrary: i) (auto split: nat.split)

lemma nth_list_update:
"i < length xs==> (xs[i:=x])!j = (if i = j then x else xs!j)"
by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma nth_list_update_eq [simp]: "i < length xs ==> (xs[i:=x])!i = x"
by (simp add: nth_list_update)

lemma nth_list_update_neq [simp]: "i \<noteq> j ==> xs[i:=x]!j = xs!j"
by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma list_update_id[simp]: "xs[i := xs!i] = xs"
by (induct xs arbitrary: i) (simp_all split:nat.splits)

lemma list_update_beyond[simp]: "length xs \<le> i \<Longrightarrow> xs[i:=x] = xs"
apply (induct xs arbitrary: i)
 apply simp
apply (case_tac i)
apply simp_all
done

lemma list_update_same_conv:
"i < length xs ==> (xs[i := x] = xs) = (xs!i = x)"
by (induct xs arbitrary: i) (auto split: nat.split)

lemma list_update_append1:
 "i < size xs \<Longrightarrow> (xs @ ys)[i:=x] = xs[i:=x] @ ys"
apply (induct xs arbitrary: i, simp)
apply(simp split:nat.split)
done

lemma list_update_append:
  "(xs @ ys) [n:= x] = 
  (if n < length xs then xs[n:= x] @ ys else xs @ (ys [n-length xs:= x]))"
by (induct xs arbitrary: n) (auto split:nat.splits)

lemma list_update_length [simp]:
 "(xs @ x # ys)[length xs := y] = (xs @ y # ys)"
by (induct xs, auto)

lemma update_zip:
  "length xs = length ys ==>
  (zip xs ys)[i:=xy] = zip (xs[i:=fst xy]) (ys[i:=snd xy])"
by (induct ys arbitrary: i xy xs) (auto, case_tac xs, auto split: nat.split)

lemma set_update_subset_insert: "set(xs[i:=x]) <= insert x (set xs)"
by (induct xs arbitrary: i) (auto split: nat.split)

lemma set_update_subsetI: "[| set xs <= A; x:A |] ==> set(xs[i := x]) <= A"
by (blast dest!: set_update_subset_insert [THEN subsetD])

lemma set_update_memI: "n < length xs \<Longrightarrow> x \<in> set (xs[n := x])"
by (induct xs arbitrary: n) (auto split:nat.splits)

lemma list_update_overwrite:
  "xs [i := x, i := y] = xs [i := y]"
apply (induct xs arbitrary: i)
apply simp
apply (case_tac i)
apply simp_all
done

lemma list_update_swap:
  "i \<noteq> i' \<Longrightarrow> xs [i := x, i' := x'] = xs [i' := x', i := x]"
apply (induct xs arbitrary: i i')
apply simp
apply (case_tac i, case_tac i')
apply auto
apply (case_tac i')
apply auto
done

lemma list_update_code [code]:
  "[][i := y] = []"
  "(x # xs)[0 := y] = y # xs"
  "(x # xs)[Suc i := y] = x # xs[i := y]"
  by simp_all


subsubsection {* @{text last} and @{text butlast} *}

lemma last_snoc [simp]: "last (xs @ [x]) = x"
by (induct xs) auto

lemma butlast_snoc [simp]: "butlast (xs @ [x]) = xs"
by (induct xs) auto

lemma last_ConsL: "xs = [] \<Longrightarrow> last(x#xs) = x"
by(simp add:last.simps)

lemma last_ConsR: "xs \<noteq> [] \<Longrightarrow> last(x#xs) = last xs"
by(simp add:last.simps)

lemma last_append: "last(xs @ ys) = (if ys = [] then last xs else last ys)"
by (induct xs) (auto)

lemma last_appendL[simp]: "ys = [] \<Longrightarrow> last(xs @ ys) = last xs"
by(simp add:last_append)

lemma last_appendR[simp]: "ys \<noteq> [] \<Longrightarrow> last(xs @ ys) = last ys"
by(simp add:last_append)

lemma hd_rev: "xs \<noteq> [] \<Longrightarrow> hd(rev xs) = last xs"
by(rule rev_exhaust[of xs]) simp_all

lemma last_rev: "xs \<noteq> [] \<Longrightarrow> last(rev xs) = hd xs"
by(cases xs) simp_all

lemma last_in_set[simp]: "as \<noteq> [] \<Longrightarrow> last as \<in> set as"
by (induct as) auto

lemma length_butlast [simp]: "length (butlast xs) = length xs - 1"
by (induct xs rule: rev_induct) auto

lemma butlast_append:
  "butlast (xs @ ys) = (if ys = [] then butlast xs else xs @ butlast ys)"
by (induct xs arbitrary: ys) auto

lemma append_butlast_last_id [simp]:
"xs \<noteq> [] ==> butlast xs @ [last xs] = xs"
by (induct xs) auto

lemma in_set_butlastD: "x : set (butlast xs) ==> x : set xs"
by (induct xs) (auto split: split_if_asm)

lemma in_set_butlast_appendI:
"x : set (butlast xs) | x : set (butlast ys) ==> x : set (butlast (xs @ ys))"
by (auto dest: in_set_butlastD simp add: butlast_append)

lemma last_drop[simp]: "n < length xs \<Longrightarrow> last (drop n xs) = last xs"
apply (induct xs arbitrary: n)
 apply simp
apply (auto split:nat.split)
done

lemma last_conv_nth: "xs\<noteq>[] \<Longrightarrow> last xs = xs!(length xs - 1)"
by(induct xs)(auto simp:neq_Nil_conv)

lemma butlast_conv_take: "butlast xs = take (length xs - 1) xs"
by (induct xs, simp, case_tac xs, simp_all)


subsubsection {* @{text take} and @{text drop} *}

lemma take_0 [simp]: "take 0 xs = []"
by (induct xs) auto

lemma drop_0 [simp]: "drop 0 xs = xs"
by (induct xs) auto

lemma take_Suc_Cons [simp]: "take (Suc n) (x # xs) = x # take n xs"
by simp

lemma drop_Suc_Cons [simp]: "drop (Suc n) (x # xs) = drop n xs"
by simp

declare take_Cons [simp del] and drop_Cons [simp del]

lemma take_1_Cons [simp]: "take 1 (x # xs) = [x]"
  unfolding One_nat_def by simp

lemma drop_1_Cons [simp]: "drop 1 (x # xs) = xs"
  unfolding One_nat_def by simp

lemma take_Suc: "xs ~= [] ==> take (Suc n) xs = hd xs # take n (tl xs)"
by(clarsimp simp add:neq_Nil_conv)

lemma drop_Suc: "drop (Suc n) xs = drop n (tl xs)"
by(cases xs, simp_all)

lemma take_tl: "take n (tl xs) = tl (take (Suc n) xs)"
by (induct xs arbitrary: n) simp_all

lemma drop_tl: "drop n (tl xs) = tl(drop n xs)"
by(induct xs arbitrary: n, simp_all add:drop_Cons drop_Suc split:nat.split)

lemma tl_take: "tl (take n xs) = take (n - 1) (tl xs)"
by (cases n, simp, cases xs, auto)

lemma tl_drop: "tl (drop n xs) = drop n (tl xs)"
by (simp only: drop_tl)

lemma nth_via_drop: "drop n xs = y#ys \<Longrightarrow> xs!n = y"
apply (induct xs arbitrary: n, simp)
apply(simp add:drop_Cons nth_Cons split:nat.splits)
done

lemma take_Suc_conv_app_nth:
  "i < length xs \<Longrightarrow> take (Suc i) xs = take i xs @ [xs!i]"
apply (induct xs arbitrary: i, simp)
apply (case_tac i, auto)
done

lemma drop_Suc_conv_tl:
  "i < length xs \<Longrightarrow> (xs!i) # (drop (Suc i) xs) = drop i xs"
apply (induct xs arbitrary: i, simp)
apply (case_tac i, auto)
done

lemma length_take [simp]: "length (take n xs) = min (length xs) n"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma length_drop [simp]: "length (drop n xs) = (length xs - n)"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_all [simp]: "length xs <= n ==> take n xs = xs"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma drop_all [simp]: "length xs <= n ==> drop n xs = []"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_append [simp]:
  "take n (xs @ ys) = (take n xs @ take (n - length xs) ys)"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma drop_append [simp]:
  "drop n (xs @ ys) = drop n xs @ drop (n - length xs) ys"
by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_take [simp]: "take n (take m xs) = take (min n m) xs"
apply (induct m arbitrary: xs n, auto)
apply (case_tac xs, auto)
apply (case_tac n, auto)
done

lemma drop_drop [simp]: "drop n (drop m xs) = drop (n + m) xs"
apply (induct m arbitrary: xs, auto)
apply (case_tac xs, auto)
done

lemma take_drop: "take n (drop m xs) = drop m (take (n + m) xs)"
apply (induct m arbitrary: xs n, auto)
apply (case_tac xs, auto)
done

lemma drop_take: "drop n (take m xs) = take (m-n) (drop n xs)"
apply(induct xs arbitrary: m n)
 apply simp
apply(simp add: take_Cons drop_Cons split:nat.split)
done

lemma append_take_drop_id [simp]: "take n xs @ drop n xs = xs"
apply (induct n arbitrary: xs, auto)
apply (case_tac xs, auto)
done

lemma take_eq_Nil[simp]: "(take n xs = []) = (n = 0 \<or> xs = [])"
apply(induct xs arbitrary: n)
 apply simp
apply(simp add:take_Cons split:nat.split)
done

lemma drop_eq_Nil[simp]: "(drop n xs = []) = (length xs <= n)"
apply(induct xs arbitrary: n)
apply simp
apply(simp add:drop_Cons split:nat.split)
done

lemma take_map: "take n (map f xs) = map f (take n xs)"
apply (induct n arbitrary: xs, auto)
apply (case_tac xs, auto)
done

lemma drop_map: "drop n (map f xs) = map f (drop n xs)"
apply (induct n arbitrary: xs, auto)
apply (case_tac xs, auto)
done

lemma rev_take: "rev (take i xs) = drop (length xs - i) (rev xs)"
apply (induct xs arbitrary: i, auto)
apply (case_tac i, auto)
done

lemma rev_drop: "rev (drop i xs) = take (length xs - i) (rev xs)"
apply (induct xs arbitrary: i, auto)
apply (case_tac i, auto)
done

lemma nth_take [simp]: "i < n ==> (take n xs)!i = xs!i"
apply (induct xs arbitrary: i n, auto)
apply (case_tac n, blast)
apply (case_tac i, auto)
done

lemma nth_drop [simp]:
  "n + i <= length xs ==> (drop n xs)!i = xs!(n + i)"
apply (induct n arbitrary: xs i, auto)
apply (case_tac xs, auto)
done

lemma butlast_take:
  "n <= length xs ==> butlast (take n xs) = take (n - 1) xs"
by (simp add: butlast_conv_take min_max.inf_absorb1 min_max.inf_absorb2)

lemma butlast_drop: "butlast (drop n xs) = drop n (butlast xs)"
by (simp add: butlast_conv_take drop_take add_ac)

lemma take_butlast: "n < length xs ==> take n (butlast xs) = take n xs"
by (simp add: butlast_conv_take min_max.inf_absorb1)

lemma drop_butlast: "drop n (butlast xs) = butlast (drop n xs)"
by (simp add: butlast_conv_take drop_take add_ac)

lemma hd_drop_conv_nth: "\<lbrakk> xs \<noteq> []; n < length xs \<rbrakk> \<Longrightarrow> hd(drop n xs) = xs!n"
by(simp add: hd_conv_nth)

lemma set_take_subset: "set(take n xs) \<subseteq> set xs"
by(induct xs arbitrary: n)(auto simp:take_Cons split:nat.split)

lemma set_drop_subset: "set(drop n xs) \<subseteq> set xs"
by(induct xs arbitrary: n)(auto simp:drop_Cons split:nat.split)

lemma in_set_takeD: "x : set(take n xs) \<Longrightarrow> x : set xs"
using set_take_subset by fast

lemma in_set_dropD: "x : set(drop n xs) \<Longrightarrow> x : set xs"
using set_drop_subset by fast

lemma append_eq_conv_conj:
  "(xs @ ys = zs) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
apply (induct xs arbitrary: zs, simp, clarsimp)
apply (case_tac zs, auto)
done

lemma take_add: 
  "i+j \<le> length(xs) \<Longrightarrow> take (i+j) xs = take i xs @ take j (drop i xs)"
apply (induct xs arbitrary: i, auto) 
apply (case_tac i, simp_all)
done

lemma append_eq_append_conv_if:
 "(xs\<^isub>1 @ xs\<^isub>2 = ys\<^isub>1 @ ys\<^isub>2) =
  (if size xs\<^isub>1 \<le> size ys\<^isub>1
   then xs\<^isub>1 = take (size xs\<^isub>1) ys\<^isub>1 \<and> xs\<^isub>2 = drop (size xs\<^isub>1) ys\<^isub>1 @ ys\<^isub>2
   else take (size ys\<^isub>1) xs\<^isub>1 = ys\<^isub>1 \<and> drop (size ys\<^isub>1) xs\<^isub>1 @ xs\<^isub>2 = ys\<^isub>2)"
apply(induct xs\<^isub>1 arbitrary: ys\<^isub>1)
 apply simp
apply(case_tac ys\<^isub>1)
apply simp_all
done

lemma take_hd_drop:
  "n < length xs \<Longrightarrow> take n xs @ [hd (drop n xs)] = take (Suc n) xs"
apply(induct xs arbitrary: n)
apply simp
apply(simp add:drop_Cons split:nat.split)
done

lemma id_take_nth_drop:
 "i < length xs \<Longrightarrow> xs = take i xs @ xs!i # drop (Suc i) xs" 
proof -
  assume si: "i < length xs"
  hence "xs = take (Suc i) xs @ drop (Suc i) xs" by auto
  moreover
  from si have "take (Suc i) xs = take i xs @ [xs!i]"
    apply (rule_tac take_Suc_conv_app_nth) by arith
  ultimately show ?thesis by auto
qed
  
lemma upd_conv_take_nth_drop:
 "i < length xs \<Longrightarrow> xs[i:=a] = take i xs @ a # drop (Suc i) xs"
proof -
  assume i: "i < length xs"
  have "xs[i:=a] = (take i xs @ xs!i # drop (Suc i) xs)[i:=a]"
    by(rule arg_cong[OF id_take_nth_drop[OF i]])
  also have "\<dots> = take i xs @ a # drop (Suc i) xs"
    using i by (simp add: list_update_append)
  finally show ?thesis .
qed

lemma nth_drop':
  "i < length xs \<Longrightarrow> xs ! i # drop (Suc i) xs = drop i xs"
apply (induct i arbitrary: xs)
apply (simp add: neq_Nil_conv)
apply (erule exE)+
apply simp
apply (case_tac xs)
apply simp_all
done


subsubsection {* @{text takeWhile} and @{text dropWhile} *}

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

lemma set_takeWhileD: "x : set (takeWhile P xs) ==> x : set xs \<and> P x"
by (induct xs) (auto split: split_if_asm)

lemma takeWhile_eq_all_conv[simp]:
 "(takeWhile P xs = xs) = (\<forall>x \<in> set xs. P x)"
by(induct xs, auto)

lemma dropWhile_eq_Nil_conv[simp]:
 "(dropWhile P xs = []) = (\<forall>x \<in> set xs. P x)"
by(induct xs, auto)

lemma dropWhile_eq_Cons_conv:
 "(dropWhile P xs = y#ys) = (xs = takeWhile P xs @ y # ys & \<not> P y)"
by(induct xs, auto)

text{* The following two lemmmas could be generalized to an arbitrary
property. *}

lemma takeWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
 takeWhile (\<lambda>y. y \<noteq> x) (rev xs) = rev (tl (dropWhile (\<lambda>y. y \<noteq> x) xs))"
by(induct xs) (auto simp: takeWhile_tail[where l="[]"])

lemma dropWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  dropWhile (\<lambda>y. y \<noteq> x) (rev xs) = x # rev (takeWhile (\<lambda>y. y \<noteq> x) xs)"
apply(induct xs)
 apply simp
apply auto
apply(subst dropWhile_append2)
apply auto
done

lemma takeWhile_not_last:
 "\<lbrakk> xs \<noteq> []; distinct xs\<rbrakk> \<Longrightarrow> takeWhile (\<lambda>y. y \<noteq> last xs) xs = butlast xs"
apply(induct xs)
 apply simp
apply(case_tac xs)
apply(auto)
done

lemma takeWhile_cong [fundef_cong, recdef_cong]:
  "[| l = k; !!x. x : set l ==> P x = Q x |] 
  ==> takeWhile P l = takeWhile Q k"
by (induct k arbitrary: l) (simp_all)

lemma dropWhile_cong [fundef_cong, recdef_cong]:
  "[| l = k; !!x. x : set l ==> P x = Q x |] 
  ==> dropWhile P l = dropWhile Q k"
by (induct k arbitrary: l, simp_all)


subsubsection {* @{text zip} *}

lemma zip_Nil [simp]: "zip [] ys = []"
by (induct ys) auto

lemma zip_Cons_Cons [simp]: "zip (x # xs) (y # ys) = (x, y) # zip xs ys"
by simp

declare zip_Cons [simp del]

lemma zip_Cons1:
 "zip (x#xs) ys = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (x,y)#zip xs ys)"
by(auto split:list.split)

lemma length_zip [simp]:
"length (zip xs ys) = min (length xs) (length ys)"
by (induct xs ys rule:list_induct2') auto

lemma zip_append1:
"zip (xs @ ys) zs =
zip xs (take (length xs) zs) @ zip ys (drop (length xs) zs)"
by (induct xs zs rule:list_induct2') auto

lemma zip_append2:
"zip xs (ys @ zs) =
zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs"
by (induct xs ys rule:list_induct2') auto

lemma zip_append [simp]:
 "[| length xs = length us; length ys = length vs |] ==>
zip (xs@ys) (us@vs) = zip xs us @ zip ys vs"
by (simp add: zip_append1)

lemma zip_rev:
"length xs = length ys ==> zip (rev xs) (rev ys) = rev (zip xs ys)"
by (induct rule:list_induct2, simp_all)

lemma map_zip_map:
 "map f (zip (map g xs) ys) = map (%(x,y). f(g x, y)) (zip xs ys)"
apply(induct xs arbitrary:ys) apply simp
apply(case_tac ys)
apply simp_all
done

lemma map_zip_map2:
 "map f (zip xs (map g ys)) = map (%(x,y). f(x, g y)) (zip xs ys)"
apply(induct xs arbitrary:ys) apply simp
apply(case_tac ys)
apply simp_all
done

lemma nth_zip [simp]:
"[| i < length xs; i < length ys|] ==> (zip xs ys)!i = (xs!i, ys!i)"
apply (induct ys arbitrary: i xs, simp)
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
  "zip (replicate i x) (replicate j y) = replicate (min i j) (x,y)"
apply (induct i arbitrary: j, auto)
apply (case_tac j, auto)
done

lemma take_zip:
  "take n (zip xs ys) = zip (take n xs) (take n ys)"
apply (induct n arbitrary: xs ys)
 apply simp
apply (case_tac xs, simp)
apply (case_tac ys, simp_all)
done

lemma drop_zip:
  "drop n (zip xs ys) = zip (drop n xs) (drop n ys)"
apply (induct n arbitrary: xs ys)
 apply simp
apply (case_tac xs, simp)
apply (case_tac ys, simp_all)
done

lemma set_zip_leftD:
  "(x,y)\<in> set (zip xs ys) \<Longrightarrow> x \<in> set xs"
by (induct xs ys rule:list_induct2') auto

lemma set_zip_rightD:
  "(x,y)\<in> set (zip xs ys) \<Longrightarrow> y \<in> set ys"
by (induct xs ys rule:list_induct2') auto

lemma in_set_zipE:
  "(x,y) : set(zip xs ys) \<Longrightarrow> (\<lbrakk> x : set xs; y : set ys \<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
by(blast dest: set_zip_leftD set_zip_rightD)

lemma zip_map_fst_snd:
  "zip (map fst zs) (map snd zs) = zs"
  by (induct zs) simp_all

lemma zip_eq_conv:
  "length xs = length ys \<Longrightarrow> zip xs ys = zs \<longleftrightarrow> map fst zs = xs \<and> map snd zs = ys"
  by (auto simp add: zip_map_fst_snd)


subsubsection {* @{text list_all2} *}

lemma list_all2_lengthD [intro?]: 
  "list_all2 P xs ys ==> length xs = length ys"
by (simp add: list_all2_def)

lemma list_all2_Nil [iff, code]: "list_all2 P [] ys = (ys = [])"
by (simp add: list_all2_def)

lemma list_all2_Nil2 [iff, code]: "list_all2 P xs [] = (xs = [])"
by (simp add: list_all2_def)

lemma list_all2_Cons [iff, code]:
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

lemma list_all2_rev1:
"list_all2 P (rev xs) ys = list_all2 P xs (rev ys)"
by (subst list_all2_rev [symmetric]) simp

lemma list_all2_append1:
"list_all2 P (xs @ ys) zs =
(EX us vs. zs = us @ vs \<and> length us = length xs \<and> length vs = length ys \<and>
list_all2 P xs us \<and> list_all2 P ys vs)"
apply (simp add: list_all2_def zip_append1)
apply (rule iffI)
 apply (rule_tac x = "take (length xs) zs" in exI)
 apply (rule_tac x = "drop (length xs) zs" in exI)
 apply (force split: nat_diff_split simp add: min_def, clarify)
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
 apply (force split: nat_diff_split simp add: min_def, clarify)
apply (simp add: ball_Un)
done

lemma list_all2_append:
  "length xs = length ys \<Longrightarrow>
  list_all2 P (xs@us) (ys@vs) = (list_all2 P xs ys \<and> list_all2 P us vs)"
by (induct rule:list_induct2, simp_all)

lemma list_all2_appendI [intro?, trans]:
  "\<lbrakk> list_all2 P a b; list_all2 P c d \<rbrakk> \<Longrightarrow> list_all2 P (a@c) (b@d)"
by (simp add: list_all2_append list_all2_lengthD)

lemma list_all2_conv_all_nth:
"list_all2 P xs ys =
(length xs = length ys \<and> (\<forall>i < length xs. P (xs!i) (ys!i)))"
by (force simp add: list_all2_def set_zip)

lemma list_all2_trans:
  assumes tr: "!!a b c. P1 a b ==> P2 b c ==> P3 a c"
  shows "!!bs cs. list_all2 P1 as bs ==> list_all2 P2 bs cs ==> list_all2 P3 as cs"
        (is "!!bs cs. PROP ?Q as bs cs")
proof (induct as)
  fix x xs bs assume I1: "!!bs cs. PROP ?Q xs bs cs"
  show "!!cs. PROP ?Q (x # xs) bs cs"
  proof (induct bs)
    fix y ys cs assume I2: "!!cs. PROP ?Q (x # xs) ys cs"
    show "PROP ?Q (x # xs) (y # ys) cs"
      by (induct cs) (auto intro: tr I1 I2)
  qed simp
qed simp

lemma list_all2_all_nthI [intro?]:
  "length a = length b \<Longrightarrow> (\<And>n. n < length a \<Longrightarrow> P (a!n) (b!n)) \<Longrightarrow> list_all2 P a b"
by (simp add: list_all2_conv_all_nth)

lemma list_all2I:
  "\<forall>x \<in> set (zip a b). split P x \<Longrightarrow> length a = length b \<Longrightarrow> list_all2 P a b"
by (simp add: list_all2_def)

lemma list_all2_nthD:
  "\<lbrakk> list_all2 P xs ys; p < size xs \<rbrakk> \<Longrightarrow> P (xs!p) (ys!p)"
by (simp add: list_all2_conv_all_nth)

lemma list_all2_nthD2:
  "\<lbrakk>list_all2 P xs ys; p < size ys\<rbrakk> \<Longrightarrow> P (xs!p) (ys!p)"
by (frule list_all2_lengthD) (auto intro: list_all2_nthD)

lemma list_all2_map1: 
  "list_all2 P (map f as) bs = list_all2 (\<lambda>x y. P (f x) y) as bs"
by (simp add: list_all2_conv_all_nth)

lemma list_all2_map2: 
  "list_all2 P as (map f bs) = list_all2 (\<lambda>x y. P x (f y)) as bs"
by (auto simp add: list_all2_conv_all_nth)

lemma list_all2_refl [intro?]:
  "(\<And>x. P x x) \<Longrightarrow> list_all2 P xs xs"
by (simp add: list_all2_conv_all_nth)

lemma list_all2_update_cong:
  "\<lbrakk> i<size xs; list_all2 P xs ys; P x y \<rbrakk> \<Longrightarrow> list_all2 P (xs[i:=x]) (ys[i:=y])"
by (simp add: list_all2_conv_all_nth nth_list_update)

lemma list_all2_update_cong2:
  "\<lbrakk>list_all2 P xs ys; P x y; i < length ys\<rbrakk> \<Longrightarrow> list_all2 P (xs[i:=x]) (ys[i:=y])"
by (simp add: list_all2_lengthD list_all2_update_cong)

lemma list_all2_takeI [simp,intro?]:
  "list_all2 P xs ys \<Longrightarrow> list_all2 P (take n xs) (take n ys)"
apply (induct xs arbitrary: n ys)
 apply simp
apply (clarsimp simp add: list_all2_Cons1)
apply (case_tac n)
apply auto
done

lemma list_all2_dropI [simp,intro?]:
  "list_all2 P as bs \<Longrightarrow> list_all2 P (drop n as) (drop n bs)"
apply (induct as arbitrary: n bs, simp)
apply (clarsimp simp add: list_all2_Cons1)
apply (case_tac n, simp, simp)
done

lemma list_all2_mono [intro?]:
  "list_all2 P xs ys \<Longrightarrow> (\<And>xs ys. P xs ys \<Longrightarrow> Q xs ys) \<Longrightarrow> list_all2 Q xs ys"
apply (induct xs arbitrary: ys, simp)
apply (case_tac ys, auto)
done

lemma list_all2_eq:
  "xs = ys \<longleftrightarrow> list_all2 (op =) xs ys"
by (induct xs ys rule: list_induct2') auto


subsubsection {* @{text foldl} and @{text foldr} *}

lemma foldl_append [simp]:
  "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"
by (induct xs arbitrary: a) auto

lemma foldr_append[simp]: "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)"
by (induct xs) auto

lemma foldr_map: "foldr g (map f xs) a = foldr (g o f) xs a"
by(induct xs) simp_all

text{* For efficient code generation: avoid intermediate list. *}
lemma foldl_map[code unfold]:
  "foldl g a (map f xs) = foldl (%a x. g a (f x)) a xs"
by(induct xs arbitrary:a) simp_all

lemma foldl_cong [fundef_cong, recdef_cong]:
  "[| a = b; l = k; !!a x. x : set l ==> f a x = g a x |] 
  ==> foldl f a l = foldl g b k"
by (induct k arbitrary: a b l) simp_all

lemma foldr_cong [fundef_cong, recdef_cong]:
  "[| a = b; l = k; !!a x. x : set l ==> f x a = g x a |] 
  ==> foldr f l a = foldr g k b"
by (induct k arbitrary: a b l) simp_all

lemma (in semigroup_add) foldl_assoc:
shows "foldl op+ (x+y) zs = x + (foldl op+ y zs)"
by (induct zs arbitrary: y) (simp_all add:add_assoc)

lemma (in monoid_add) foldl_absorb0:
shows "x + (foldl op+ 0 zs) = foldl op+ x zs"
by (induct zs) (simp_all add:foldl_assoc)


text{* The ``First Duality Theorem'' in Bird \& Wadler: *}

lemma foldl_foldr1_lemma:
 "foldl op + a xs = a + foldr op + xs (0\<Colon>'a::monoid_add)"
by (induct xs arbitrary: a) (auto simp:add_assoc)

corollary foldl_foldr1:
 "foldl op + 0 xs = foldr op + xs (0\<Colon>'a::monoid_add)"
by (simp add:foldl_foldr1_lemma)


text{* The ``Third Duality Theorem'' in Bird \& Wadler: *}

lemma foldr_foldl: "foldr f xs a = foldl (%x y. f y x) a (rev xs)"
by (induct xs) auto

lemma foldl_foldr: "foldl f a xs = foldr (%x y. f y x) (rev xs) a"
by (simp add: foldr_foldl [of "%x y. f y x" "rev xs"])

lemma (in ab_semigroup_add) foldr_conv_foldl: "foldr op + xs a = foldl op + a xs"
  by (induct xs, auto simp add: foldl_assoc add_commute)

text {*
Note: @{text "n \<le> foldl (op +) n ns"} looks simpler, but is more
difficult to use because it requires an additional transitivity step.
*}

lemma start_le_sum: "(m::nat) <= n ==> m <= foldl (op +) n ns"
by (induct ns arbitrary: n) auto

lemma elem_le_sum: "(n::nat) : set ns ==> n <= foldl (op +) 0 ns"
by (force intro: start_le_sum simp add: in_set_conv_decomp)

lemma sum_eq_0_conv [iff]:
  "(foldl (op +) (m::nat) ns = 0) = (m = 0 \<and> (\<forall>n \<in> set ns. n = 0))"
by (induct ns arbitrary: m) auto

lemma foldr_invariant: 
  "\<lbrakk>Q x ; \<forall> x\<in> set xs. P x; \<forall> x y. P x \<and> Q y \<longrightarrow> Q (f x y) \<rbrakk> \<Longrightarrow> Q (foldr f xs x)"
  by (induct xs, simp_all)

lemma foldl_invariant: 
  "\<lbrakk>Q x ; \<forall> x\<in> set xs. P x; \<forall> x y. P x \<and> Q y \<longrightarrow> Q (f y x) \<rbrakk> \<Longrightarrow> Q (foldl f x xs)"
  by (induct xs arbitrary: x, simp_all)

text{* @{const foldl} and @{text concat} *}

lemma foldl_conv_concat:
  "foldl (op @) xs xss = xs @ concat xss"
proof (induct xss arbitrary: xs)
  case Nil show ?case by simp
next
  interpret monoid_add "[]" "op @" proof qed simp_all
  case Cons then show ?case by (simp add: foldl_absorb0)
qed

lemma concat_conv_foldl: "concat xss = foldl (op @) [] xss"
  by (simp add: foldl_conv_concat)


subsubsection {* List summation: @{const listsum} and @{text"\<Sum>"}*}

lemma listsum_append [simp]: "listsum (xs @ ys) = listsum xs + listsum ys"
by (induct xs) (simp_all add:add_assoc)

lemma listsum_rev [simp]:
  fixes xs :: "'a\<Colon>comm_monoid_add list"
  shows "listsum (rev xs) = listsum xs"
by (induct xs) (simp_all add:add_ac)

lemma listsum_foldr: "listsum xs = foldr (op +) xs 0"
by (induct xs) auto

lemma length_concat: "length (concat xss) = listsum (map length xss)"
by (induct xss) simp_all

text{* For efficient code generation ---
       @{const listsum} is not tail recursive but @{const foldl} is. *}
lemma listsum[code unfold]: "listsum xs = foldl (op +) 0 xs"
by(simp add:listsum_foldr foldl_foldr1)


text{* Some syntactic sugar for summing a function over a list: *}

syntax
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3SUM _<-_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Sum>_\<leftarrow>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_listsum" :: "pttrn => 'a list => 'b => 'b"    ("(3\<Sum>_\<leftarrow>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM x<-xs. b" == "CONST listsum (map (%x. b) xs)"
  "\<Sum>x\<leftarrow>xs. b" == "CONST listsum (map (%x. b) xs)"

lemma listsum_triv: "(\<Sum>x\<leftarrow>xs. r) = of_nat (length xs) * r"
  by (induct xs) (simp_all add: left_distrib)

lemma listsum_0 [simp]: "(\<Sum>x\<leftarrow>xs. 0) = 0"
  by (induct xs) (simp_all add: left_distrib)

text{* For non-Abelian groups @{text xs} needs to be reversed on one side: *}
lemma uminus_listsum_map:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>ab_group_add"
  shows "- listsum (map f xs) = (listsum (map (uminus o f) xs))"
by (induct xs) simp_all


subsubsection {* @{text upt} *}

lemma upt_rec[code]: "[i..<j] = (if i<j then i#[Suc i..<j] else [])"
-- {* simp does not terminate! *}
by (induct j) auto

lemma upt_conv_Nil [simp]: "j <= i ==> [i..<j] = []"
by (subst upt_rec) simp

lemma upt_eq_Nil_conv[simp]: "([i..<j] = []) = (j = 0 \<or> j <= i)"
by(induct j)simp_all

lemma upt_eq_Cons_conv:
 "([i..<j] = x#xs) = (i < j & i = x & [i+1..<j] = xs)"
apply(induct j arbitrary: x xs)
 apply simp
apply(clarsimp simp add: append_eq_Cons_conv)
apply arith
done

lemma upt_Suc_append: "i <= j ==> [i..<(Suc j)] = [i..<j]@[j]"
-- {* Only needed if @{text upt_Suc} is deleted from the simpset. *}
by simp

lemma upt_conv_Cons: "i < j ==> [i..<j] = i # [Suc i..<j]"
  by (simp add: upt_rec)

lemma upt_add_eq_append: "i<=j ==> [i..<j+k] = [i..<j]@[j..<j+k]"
-- {* LOOPS as a simprule, since @{text "j <= j"}. *}
by (induct k) auto

lemma length_upt [simp]: "length [i..<j] = j - i"
by (induct j) (auto simp add: Suc_diff_le)

lemma nth_upt [simp]: "i + k < j ==> [i..<j] ! k = i + k"
apply (induct j)
apply (auto simp add: less_Suc_eq nth_append split: nat_diff_split)
done


lemma hd_upt[simp]: "i < j \<Longrightarrow> hd[i..<j] = i"
by(simp add:upt_conv_Cons)

lemma last_upt[simp]: "i < j \<Longrightarrow> last[i..<j] = j - 1"
apply(cases j)
 apply simp
by(simp add:upt_Suc_append)

lemma take_upt [simp]: "i+m <= n ==> take m [i..<n] = [i..<i+m]"
apply (induct m arbitrary: i, simp)
apply (subst upt_rec)
apply (rule sym)
apply (subst upt_rec)
apply (simp del: upt.simps)
done

lemma drop_upt[simp]: "drop m [i..<j] = [i+m..<j]"
apply(induct j)
apply auto
done

lemma map_Suc_upt: "map Suc [m..<n] = [Suc m..<Suc n]"
by (induct n) auto

lemma nth_map_upt: "i < n-m ==> (map f [m..<n]) ! i = f(m+i)"
apply (induct n m  arbitrary: i rule: diff_induct)
prefer 3 apply (subst map_Suc_upt[symmetric])
apply (auto simp add: less_diff_conv nth_upt)
done

lemma nth_take_lemma:
  "k <= length xs ==> k <= length ys ==>
     (!!i. i < k --> xs!i = ys!i) ==> take k xs = take k ys"
apply (atomize, induct k arbitrary: xs ys)
apply (simp_all add: less_Suc_eq_0_disj all_conj_distrib, clarify)
txt {* Both lists must be non-empty *}
apply (case_tac xs, simp)
apply (case_tac ys, clarify)
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

lemma map_nth:
  "map (\<lambda>i. xs ! i) [0..<length xs] = xs"
  by (rule nth_equalityI, auto)

(* needs nth_equalityI *)
lemma list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>P x y; Q y x\<rbrakk> \<Longrightarrow> x = y); list_all2 P xs ys; list_all2 Q ys xs \<rbrakk> 
  \<Longrightarrow> xs = ys"
  apply (simp add: list_all2_conv_all_nth) 
  apply (rule nth_equalityI, blast, simp)
  done

lemma take_equalityI: "(\<forall>i. take i xs = take i ys) ==> xs = ys"
-- {* The famous take-lemma. *}
apply (drule_tac x = "max (length xs) (length ys)" in spec)
apply (simp add: le_max_iff_disj take_all)
done


lemma take_Cons':
     "take n (x # xs) = (if n = 0 then [] else x # take (n - 1) xs)"
by (cases n) simp_all

lemma drop_Cons':
     "drop n (x # xs) = (if n = 0 then x # xs else drop (n - 1) xs)"
by (cases n) simp_all

lemma nth_Cons': "(x # xs)!n = (if n = 0 then x else xs!(n - 1))"
by (cases n) simp_all

lemmas take_Cons_number_of = take_Cons'[of "number_of v",standard]
lemmas drop_Cons_number_of = drop_Cons'[of "number_of v",standard]
lemmas nth_Cons_number_of = nth_Cons'[of _ _ "number_of v",standard]

declare take_Cons_number_of [simp] 
        drop_Cons_number_of [simp] 
        nth_Cons_number_of [simp] 


subsubsection {* @{text "distinct"} and @{text remdups} *}

lemma distinct_append [simp]:
"distinct (xs @ ys) = (distinct xs \<and> distinct ys \<and> set xs \<inter> set ys = {})"
by (induct xs) auto

lemma distinct_rev[simp]: "distinct(rev xs) = distinct xs"
by(induct xs) auto

lemma set_remdups [simp]: "set (remdups xs) = set xs"
by (induct xs) (auto simp add: insert_absorb)

lemma distinct_remdups [iff]: "distinct (remdups xs)"
by (induct xs) auto

lemma distinct_remdups_id: "distinct xs ==> remdups xs = xs"
by (induct xs, auto)

lemma remdups_id_iff_distinct [simp]: "remdups xs = xs \<longleftrightarrow> distinct xs"
by (metis distinct_remdups distinct_remdups_id)

lemma finite_distinct_list: "finite A \<Longrightarrow> EX xs. set xs = A & distinct xs"
by (metis distinct_remdups finite_list set_remdups)

lemma remdups_eq_nil_iff [simp]: "(remdups x = []) = (x = [])"
by (induct x, auto) 

lemma remdups_eq_nil_right_iff [simp]: "([] = remdups x) = (x = [])"
by (induct x, auto)

lemma length_remdups_leq[iff]: "length(remdups xs) <= length xs"
by (induct xs) auto

lemma length_remdups_eq[iff]:
  "(length (remdups xs) = length xs) = (remdups xs = xs)"
apply(induct xs)
 apply auto
apply(subgoal_tac "length (remdups xs) <= length xs")
 apply arith
apply(rule length_remdups_leq)
done


lemma distinct_map:
  "distinct(map f xs) = (distinct xs & inj_on f (set xs))"
by (induct xs) auto


lemma distinct_filter [simp]: "distinct xs ==> distinct (filter P xs)"
by (induct xs) auto

lemma distinct_upt[simp]: "distinct[i..<j]"
by (induct j) auto

lemma distinct_take[simp]: "distinct xs \<Longrightarrow> distinct (take i xs)"
apply(induct xs arbitrary: i)
 apply simp
apply (case_tac i)
 apply simp_all
apply(blast dest:in_set_takeD)
done

lemma distinct_drop[simp]: "distinct xs \<Longrightarrow> distinct (drop i xs)"
apply(induct xs arbitrary: i)
 apply simp
apply (case_tac i)
 apply simp_all
done

lemma distinct_list_update:
assumes d: "distinct xs" and a: "a \<notin> set xs - {xs!i}"
shows "distinct (xs[i:=a])"
proof (cases "i < length xs")
  case True
  with a have "a \<notin> set (take i xs @ xs ! i # drop (Suc i) xs) - {xs!i}"
    apply (drule_tac id_take_nth_drop) by simp
  with d True show ?thesis
    apply (simp add: upd_conv_take_nth_drop)
    apply (drule subst [OF id_take_nth_drop]) apply assumption
    apply simp apply (cases "a = xs!i") apply simp by blast
next
  case False with d show ?thesis by auto
qed


text {* It is best to avoid this indexed version of distinct, but
sometimes it is useful. *}

lemma distinct_conv_nth:
"distinct xs = (\<forall>i < size xs. \<forall>j < size xs. i \<noteq> j --> xs!i \<noteq> xs!j)"
apply (induct xs, simp, simp)
apply (rule iffI, clarsimp)
 apply (case_tac i)
apply (case_tac j, simp)
apply (simp add: set_conv_nth)
 apply (case_tac j)
apply (clarsimp simp add: set_conv_nth, simp) 
apply (rule conjI)
(*TOO SLOW
apply (metis Zero_neq_Suc gr0_conv_Suc in_set_conv_nth lessI less_trans_Suc nth_Cons' nth_Cons_Suc)
*)
 apply (clarsimp simp add: set_conv_nth)
 apply (erule_tac x = 0 in allE, simp)
 apply (erule_tac x = "Suc i" in allE, simp, clarsimp)
(*TOO SLOW
apply (metis Suc_Suc_eq lessI less_trans_Suc nth_Cons_Suc)
*)
apply (erule_tac x = "Suc i" in allE, simp)
apply (erule_tac x = "Suc j" in allE, simp)
done

lemma nth_eq_iff_index_eq:
 "\<lbrakk> distinct xs; i < length xs; j < length xs \<rbrakk> \<Longrightarrow> (xs!i = xs!j) = (i = j)"
by(auto simp: distinct_conv_nth)

lemma distinct_card: "distinct xs ==> card (set xs) = size xs"
by (induct xs) auto

lemma card_distinct: "card (set xs) = size xs ==> distinct xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> set xs")
    case False with Cons show ?thesis by simp
  next
    case True with Cons.prems
    have "card (set xs) = Suc (length xs)" 
      by (simp add: card_insert_if split: split_if_asm)
    moreover have "card (set xs) \<le> length xs" by (rule card_length)
    ultimately have False by simp
    thus ?thesis ..
  qed
qed

lemma not_distinct_decomp: "~ distinct ws ==> EX xs ys zs y. ws = xs@[y]@ys@[y]@zs"
apply (induct n == "length ws" arbitrary:ws) apply simp
apply(case_tac ws) apply simp
apply (simp split:split_if_asm)
apply (metis Cons_eq_appendI eq_Nil_appendI split_list)
done

lemma length_remdups_concat:
 "length(remdups(concat xss)) = card(\<Union>xs \<in> set xss. set xs)"
by(simp add: set_concat distinct_card[symmetric])


subsubsection {* @{text remove1} *}

lemma remove1_append:
  "remove1 x (xs @ ys) =
  (if x \<in> set xs then remove1 x xs @ ys else xs @ remove1 x ys)"
by (induct xs) auto

lemma in_set_remove1[simp]:
  "a \<noteq> b \<Longrightarrow> a : set(remove1 b xs) = (a : set xs)"
apply (induct xs)
apply auto
done

lemma set_remove1_subset: "set(remove1 x xs) <= set xs"
apply(induct xs)
 apply simp
apply simp
apply blast
done

lemma set_remove1_eq [simp]: "distinct xs ==> set(remove1 x xs) = set xs - {x}"
apply(induct xs)
 apply simp
apply simp
apply blast
done

lemma length_remove1:
  "length(remove1 x xs) = (if x : set xs then length xs - 1 else length xs)"
apply (induct xs)
 apply (auto dest!:length_pos_if_in_set)
done

lemma remove1_filter_not[simp]:
  "\<not> P x \<Longrightarrow> remove1 x (filter P xs) = filter P xs"
by(induct xs) auto

lemma notin_set_remove1[simp]: "x ~: set xs ==> x ~: set(remove1 y xs)"
apply(insert set_remove1_subset)
apply fast
done

lemma distinct_remove1[simp]: "distinct xs ==> distinct(remove1 x xs)"
by (induct xs) simp_all


subsubsection {* @{text removeAll} *}

lemma removeAll_append[simp]:
  "removeAll x (xs @ ys) = removeAll x xs @ removeAll x ys"
by (induct xs) auto

lemma set_removeAll[simp]: "set(removeAll x xs) = set xs - {x}"
by (induct xs) auto

lemma removeAll_id[simp]: "x \<notin> set xs \<Longrightarrow> removeAll x xs = xs"
by (induct xs) auto

(* Needs count:: 'a \<Rightarrow> a' list \<Rightarrow> nat
lemma length_removeAll:
  "length(removeAll x xs) = length xs - count x xs"
*)

lemma removeAll_filter_not[simp]:
  "\<not> P x \<Longrightarrow> removeAll x (filter P xs) = filter P xs"
by(induct xs) auto


lemma distinct_remove1_removeAll:
  "distinct xs ==> remove1 x xs = removeAll x xs"
by (induct xs) simp_all

lemma map_removeAll_inj_on: "inj_on f (insert x (set xs)) \<Longrightarrow>
  map f (removeAll x xs) = removeAll (f x) (map f xs)"
by (induct xs) (simp_all add:inj_on_def)

lemma map_removeAll_inj: "inj f \<Longrightarrow>
  map f (removeAll x xs) = removeAll (f x) (map f xs)"
by(metis map_removeAll_inj_on subset_inj_on subset_UNIV)


subsubsection {* @{text replicate} *}

lemma length_replicate [simp]: "length (replicate n x) = n"
by (induct n) auto

lemma map_replicate [simp]: "map f (replicate n x) = replicate n (f x)"
by (induct n) auto

lemma replicate_app_Cons_same:
"(replicate n x) @ (x # xs) = x # replicate n x @ xs"
by (induct n) auto

lemma rev_replicate [simp]: "rev (replicate n x) = replicate n x"
apply (induct n, simp)
apply (simp add: replicate_app_Cons_same)
done

lemma replicate_add: "replicate (n + m) x = replicate n x @ replicate m x"
by (induct n) auto

text{* Courtesy of Matthias Daum: *}
lemma append_replicate_commute:
  "replicate n x @ replicate k x = replicate k x @ replicate n x"
apply (simp add: replicate_add [THEN sym])
apply (simp add: add_commute)
done

lemma hd_replicate [simp]: "n \<noteq> 0 ==> hd (replicate n x) = x"
by (induct n) auto

lemma tl_replicate [simp]: "n \<noteq> 0 ==> tl (replicate n x) = replicate (n - 1) x"
by (induct n) auto

lemma last_replicate [simp]: "n \<noteq> 0 ==> last (replicate n x) = x"
by (atomize (full), induct n) auto

lemma nth_replicate[simp]: "i < n ==> (replicate n x)!i = x"
apply (induct n arbitrary: i, simp)
apply (simp add: nth_Cons split: nat.split)
done

text{* Courtesy of Matthias Daum (2 lemmas): *}
lemma take_replicate[simp]: "take i (replicate k x) = replicate (min i k) x"
apply (case_tac "k \<le> i")
 apply  (simp add: min_def)
apply (drule not_leE)
apply (simp add: min_def)
apply (subgoal_tac "replicate k x = replicate i x @ replicate (k - i) x")
 apply  simp
apply (simp add: replicate_add [symmetric])
done

lemma drop_replicate[simp]: "drop i (replicate k x) = replicate (k-i) x"
apply (induct k arbitrary: i)
 apply simp
apply clarsimp
apply (case_tac i)
 apply simp
apply clarsimp
done


lemma set_replicate_Suc: "set (replicate (Suc n) x) = {x}"
by (induct n) auto

lemma set_replicate [simp]: "n \<noteq> 0 ==> set (replicate n x) = {x}"
by (fast dest!: not0_implies_Suc intro!: set_replicate_Suc)

lemma set_replicate_conv_if: "set (replicate n x) = (if n = 0 then {} else {x})"
by auto

lemma in_set_replicateD: "x : set (replicate n y) ==> x = y"
by (simp add: set_replicate_conv_if split: split_if_asm)

lemma replicate_append_same:
  "replicate i x @ [x] = x # replicate i x"
  by (induct i) simp_all

lemma map_replicate_trivial:
  "map (\<lambda>i. x) [0..<i] = replicate i x"
  by (induct i) (simp_all add: replicate_append_same)


lemma replicate_empty[simp]: "(replicate n x = []) \<longleftrightarrow> n=0"
by (induct n) auto

lemma empty_replicate[simp]: "([] = replicate n x) \<longleftrightarrow> n=0"
by (induct n) auto

lemma replicate_eq_replicate[simp]:
  "(replicate m x = replicate n y) \<longleftrightarrow> (m=n & (m\<noteq>0 \<longrightarrow> x=y))"
apply(induct m arbitrary: n)
 apply simp
apply(induct_tac n)
apply auto
done


subsubsection{*@{text rotate1} and @{text rotate}*}

lemma rotate_simps[simp]: "rotate1 [] = [] \<and> rotate1 (x#xs) = xs @ [x]"
by(simp add:rotate1_def)

lemma rotate0[simp]: "rotate 0 = id"
by(simp add:rotate_def)

lemma rotate_Suc[simp]: "rotate (Suc n) xs = rotate1(rotate n xs)"
by(simp add:rotate_def)

lemma rotate_add:
  "rotate (m+n) = rotate m o rotate n"
by(simp add:rotate_def funpow_add)

lemma rotate_rotate: "rotate m (rotate n xs) = rotate (m+n) xs"
by(simp add:rotate_add)

lemma rotate1_rotate_swap: "rotate1 (rotate n xs) = rotate n (rotate1 xs)"
by(simp add:rotate_def funpow_swap1)

lemma rotate1_length01[simp]: "length xs <= 1 \<Longrightarrow> rotate1 xs = xs"
by(cases xs) simp_all

lemma rotate_length01[simp]: "length xs <= 1 \<Longrightarrow> rotate n xs = xs"
apply(induct n)
 apply simp
apply (simp add:rotate_def)
done

lemma rotate1_hd_tl: "xs \<noteq> [] \<Longrightarrow> rotate1 xs = tl xs @ [hd xs]"
by(simp add:rotate1_def split:list.split)

lemma rotate_drop_take:
  "rotate n xs = drop (n mod length xs) xs @ take (n mod length xs) xs"
apply(induct n)
 apply simp
apply(simp add:rotate_def)
apply(cases "xs = []")
 apply (simp)
apply(case_tac "n mod length xs = 0")
 apply(simp add:mod_Suc)
 apply(simp add: rotate1_hd_tl drop_Suc take_Suc)
apply(simp add:mod_Suc rotate1_hd_tl drop_Suc[symmetric] drop_tl[symmetric]
                take_hd_drop linorder_not_le)
done

lemma rotate_conv_mod: "rotate n xs = rotate (n mod length xs) xs"
by(simp add:rotate_drop_take)

lemma rotate_id[simp]: "n mod length xs = 0 \<Longrightarrow> rotate n xs = xs"
by(simp add:rotate_drop_take)

lemma length_rotate1[simp]: "length(rotate1 xs) = length xs"
by(simp add:rotate1_def split:list.split)

lemma length_rotate[simp]: "length(rotate n xs) = length xs"
by (induct n arbitrary: xs) (simp_all add:rotate_def)

lemma distinct1_rotate[simp]: "distinct(rotate1 xs) = distinct xs"
by(simp add:rotate1_def split:list.split) blast

lemma distinct_rotate[simp]: "distinct(rotate n xs) = distinct xs"
by (induct n) (simp_all add:rotate_def)

lemma rotate_map: "rotate n (map f xs) = map f (rotate n xs)"
by(simp add:rotate_drop_take take_map drop_map)

lemma set_rotate1[simp]: "set(rotate1 xs) = set xs"
by(simp add:rotate1_def split:list.split)

lemma set_rotate[simp]: "set(rotate n xs) = set xs"
by (induct n) (simp_all add:rotate_def)

lemma rotate1_is_Nil_conv[simp]: "(rotate1 xs = []) = (xs = [])"
by(simp add:rotate1_def split:list.split)

lemma rotate_is_Nil_conv[simp]: "(rotate n xs = []) = (xs = [])"
by (induct n) (simp_all add:rotate_def)

lemma rotate_rev:
  "rotate n (rev xs) = rev(rotate (length xs - (n mod length xs)) xs)"
apply(simp add:rotate_drop_take rev_drop rev_take)
apply(cases "length xs = 0")
 apply simp
apply(cases "n mod length xs = 0")
 apply simp
apply(simp add:rotate_drop_take rev_drop rev_take)
done

lemma hd_rotate_conv_nth: "xs \<noteq> [] \<Longrightarrow> hd(rotate n xs) = xs!(n mod length xs)"
apply(simp add:rotate_drop_take hd_append hd_drop_conv_nth hd_conv_nth)
apply(subgoal_tac "length xs \<noteq> 0")
 prefer 2 apply simp
using mod_less_divisor[of "length xs" n] by arith


subsubsection {* @{text sublist} --- a generalization of @{text nth} to sets *}

lemma sublist_empty [simp]: "sublist xs {} = []"
by (auto simp add: sublist_def)

lemma sublist_nil [simp]: "sublist [] A = []"
by (auto simp add: sublist_def)

lemma length_sublist:
  "length(sublist xs I) = card{i. i < length xs \<and> i : I}"
by(simp add: sublist_def length_filter_conv_card cong:conj_cong)

lemma sublist_shift_lemma_Suc:
  "map fst (filter (%p. P(Suc(snd p))) (zip xs is)) =
   map fst (filter (%p. P(snd p)) (zip xs (map Suc is)))"
apply(induct xs arbitrary: "is")
 apply simp
apply (case_tac "is")
 apply simp
apply simp
done

lemma sublist_shift_lemma:
     "map fst [p<-zip xs [i..<i + length xs] . snd p : A] =
      map fst [p<-zip xs [0..<length xs] . snd p + i : A]"
by (induct xs rule: rev_induct) (simp_all add: add_commute)

lemma sublist_append:
     "sublist (l @ l') A = sublist l A @ sublist l' {j. j + length l : A}"
apply (unfold sublist_def)
apply (induct l' rule: rev_induct, simp)
apply (simp add: upt_add_eq_append[of 0] zip_append sublist_shift_lemma)
apply (simp add: add_commute)
done

lemma sublist_Cons:
"sublist (x # l) A = (if 0:A then [x] else []) @ sublist l {j. Suc j : A}"
apply (induct l rule: rev_induct)
 apply (simp add: sublist_def)
apply (simp del: append_Cons add: append_Cons[symmetric] sublist_append)
done

lemma set_sublist: "set(sublist xs I) = {xs!i|i. i<size xs \<and> i \<in> I}"
apply(induct xs arbitrary: I)
apply(auto simp: sublist_Cons nth_Cons split:nat.split dest!: gr0_implies_Suc)
done

lemma set_sublist_subset: "set(sublist xs I) \<subseteq> set xs"
by(auto simp add:set_sublist)

lemma notin_set_sublistI[simp]: "x \<notin> set xs \<Longrightarrow> x \<notin> set(sublist xs I)"
by(auto simp add:set_sublist)

lemma in_set_sublistD: "x \<in> set(sublist xs I) \<Longrightarrow> x \<in> set xs"
by(auto simp add:set_sublist)

lemma sublist_singleton [simp]: "sublist [x] A = (if 0 : A then [x] else [])"
by (simp add: sublist_Cons)


lemma distinct_sublistI[simp]: "distinct xs \<Longrightarrow> distinct(sublist xs I)"
apply(induct xs arbitrary: I)
 apply simp
apply(auto simp add:sublist_Cons)
done


lemma sublist_upt_eq_take [simp]: "sublist l {..<n} = take n l"
apply (induct l rule: rev_induct, simp)
apply (simp split: nat_diff_split add: sublist_append)
done

lemma filter_in_sublist:
 "distinct xs \<Longrightarrow> filter (%x. x \<in> set(sublist xs s)) xs = sublist xs s"
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  moreover hence "!x. x: set xs \<longrightarrow> x \<noteq> a" by auto
  ultimately show ?case by(simp add: sublist_Cons cong:filter_cong)
qed


subsubsection {* @{const splice} *}

lemma splice_Nil2 [simp, code]:
 "splice xs [] = xs"
by (cases xs) simp_all

lemma splice_Cons_Cons [simp, code]:
 "splice (x#xs) (y#ys) = x # y # splice xs ys"
by simp

declare splice.simps(2) [simp del, code del]

lemma length_splice[simp]: "length(splice xs ys) = length xs + length ys"
apply(induct xs arbitrary: ys) apply simp
apply(case_tac ys)
 apply auto
done


subsubsection {* Infiniteness *}

lemma finite_maxlen:
  "finite (M::'a list set) ==> EX n. ALL s:M. size s < n"
proof (induct rule: finite.induct)
  case emptyI show ?case by simp
next
  case (insertI M xs)
  then obtain n where "\<forall>s\<in>M. length s < n" by blast
  hence "ALL s:insert xs M. size s < max n (size xs) + 1" by auto
  thus ?case ..
qed

lemma infinite_UNIV_listI: "~ finite(UNIV::'a list set)"
apply(rule notI)
apply(drule finite_maxlen)
apply (metis UNIV_I length_replicate less_not_refl)
done


subsection {*Sorting*}

text{* Currently it is not shown that @{const sort} returns a
permutation of its input because the nicest proof is via multisets,
which are not yet available. Alternatively one could define a function
that counts the number of occurrences of an element in a list and use
that instead of multisets to state the correctness property. *}

context linorder
begin

lemma sorted_Cons: "sorted (x#xs) = (sorted xs & (ALL y:set xs. x <= y))"
apply(induct xs arbitrary: x) apply simp
by simp (blast intro: order_trans)

lemma sorted_append:
  "sorted (xs@ys) = (sorted xs & sorted ys & (\<forall>x \<in> set xs. \<forall>y \<in> set ys. x\<le>y))"
by (induct xs) (auto simp add:sorted_Cons)

lemma set_insort: "set(insort x xs) = insert x (set xs)"
by (induct xs) auto

lemma set_sort[simp]: "set(sort xs) = set xs"
by (induct xs) (simp_all add:set_insort)

lemma distinct_insort: "distinct (insort x xs) = (x \<notin> set xs \<and> distinct xs)"
by(induct xs)(auto simp:set_insort)

lemma distinct_sort[simp]: "distinct (sort xs) = distinct xs"
by(induct xs)(simp_all add:distinct_insort set_sort)

lemma sorted_insort: "sorted (insort x xs) = sorted xs"
apply (induct xs)
 apply(auto simp:sorted_Cons set_insort)
done

theorem sorted_sort[simp]: "sorted (sort xs)"
by (induct xs) (auto simp:sorted_insort)

lemma insort_is_Cons: "\<forall>x\<in>set xs. a \<le> x \<Longrightarrow> insort a xs = a # xs"
by (cases xs) auto

lemma sorted_remove1: "sorted xs \<Longrightarrow> sorted (remove1 a xs)"
by (induct xs, auto simp add: sorted_Cons)

lemma insort_remove1: "\<lbrakk> a \<in> set xs; sorted xs \<rbrakk> \<Longrightarrow> insort a (remove1 a xs) = xs"
by (induct xs, auto simp add: sorted_Cons insort_is_Cons)

lemma sorted_remdups[simp]:
  "sorted l \<Longrightarrow> sorted (remdups l)"
by (induct l) (auto simp: sorted_Cons)

lemma sorted_distinct_set_unique:
assumes "sorted xs" "distinct xs" "sorted ys" "distinct ys" "set xs = set ys"
shows "xs = ys"
proof -
  from assms have 1: "length xs = length ys" by (auto dest!: distinct_card)
  from assms show ?thesis
  proof(induct rule:list_induct2[OF 1])
    case 1 show ?case by simp
  next
    case 2 thus ?case by (simp add:sorted_Cons)
       (metis Diff_insert_absorb antisym insertE insert_iff)
  qed
qed

lemma finite_sorted_distinct_unique:
shows "finite A \<Longrightarrow> EX! xs. set xs = A & sorted xs & distinct xs"
apply(drule finite_distinct_list)
apply clarify
apply(rule_tac a="sort xs" in ex1I)
apply (auto simp: sorted_distinct_set_unique)
done

lemma sorted_take:
  "sorted xs \<Longrightarrow> sorted (take n xs)"
proof (induct xs arbitrary: n rule: sorted.induct)
  case 1 show ?case by simp
next
  case 2 show ?case by (cases n) simp_all
next
  case (3 x y xs)
  then have "x \<le> y" by simp
  show ?case proof (cases n)
    case 0 then show ?thesis by simp
  next
    case (Suc m) 
    with 3 have "sorted (take m (y # xs))" by simp
    with Suc  `x \<le> y` show ?thesis by (cases m) simp_all
  qed
qed

lemma sorted_drop:
  "sorted xs \<Longrightarrow> sorted (drop n xs)"
proof (induct xs arbitrary: n rule: sorted.induct)
  case 1 show ?case by simp
next
  case 2 show ?case by (cases n) simp_all
next
  case 3 then show ?case by (cases n) simp_all
qed


end

lemma sorted_upt[simp]: "sorted[i..<j]"
by (induct j) (simp_all add:sorted_append)


subsubsection {* @{text sorted_list_of_set} *}

text{* This function maps (finite) linearly ordered sets to sorted
lists. Warning: in most cases it is not a good idea to convert from
sets to lists but one should convert in the other direction (via
@{const set}). *}


context linorder
begin

definition
 sorted_list_of_set :: "'a set \<Rightarrow> 'a list" where
 [code del]: "sorted_list_of_set A == THE xs. set xs = A & sorted xs & distinct xs"

lemma sorted_list_of_set[simp]: "finite A \<Longrightarrow>
  set(sorted_list_of_set A) = A &
  sorted(sorted_list_of_set A) & distinct(sorted_list_of_set A)"
apply(simp add:sorted_list_of_set_def)
apply(rule the1I2)
 apply(simp_all add: finite_sorted_distinct_unique)
done

lemma sorted_list_of_empty[simp]: "sorted_list_of_set {} = []"
unfolding sorted_list_of_set_def
apply(subst the_equality[of _ "[]"])
apply simp_all
done

end


subsubsection {* @{text upto}: the generic interval-list *}

class finite_intvl_succ = linorder +
fixes successor :: "'a \<Rightarrow> 'a"
assumes finite_intvl: "finite{a..b}"
and successor_incr: "a < successor a"
and ord_discrete: "\<not>(\<exists>x. a < x & x < successor a)"

context finite_intvl_succ
begin

definition
 upto :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list" ("(1[_../_])") where
"upto i j == sorted_list_of_set {i..j}"

lemma upto[simp]: "set[a..b] = {a..b} & sorted[a..b] & distinct[a..b]"
by(simp add:upto_def finite_intvl)

lemma insert_intvl: "i \<le> j \<Longrightarrow> insert i {successor i..j} = {i..j}"
apply(insert successor_incr[of i])
apply(auto simp: atLeastAtMost_def atLeast_def atMost_def)
apply(metis ord_discrete less_le not_le)
done

lemma sorted_list_of_set_rec: "i \<le> j \<Longrightarrow>
  sorted_list_of_set {i..j} = i # sorted_list_of_set {successor i..j}"
apply(simp add:sorted_list_of_set_def upto_def)
apply (rule the1_equality[OF finite_sorted_distinct_unique])
 apply (simp add:finite_intvl)
apply(rule the1I2[OF finite_sorted_distinct_unique])
 apply (simp add:finite_intvl)
apply (simp add: sorted_Cons insert_intvl Ball_def)
apply (metis successor_incr leD less_imp_le order_trans)
done

lemma sorted_list_of_set_rec2: "i \<le> j \<Longrightarrow>
  sorted_list_of_set {i..successor j} =
  sorted_list_of_set {i..j} @ [successor j]"
apply(simp add:sorted_list_of_set_def upto_def)
apply (rule the1_equality[OF finite_sorted_distinct_unique])
 apply (simp add:finite_intvl)
apply(rule the1I2[OF finite_sorted_distinct_unique])
 apply (simp add:finite_intvl)
apply (simp add: sorted_append Ball_def expand_set_eq)
apply(rule conjI)
apply (metis eq_iff leD linear not_leE ord_discrete order_trans successor_incr)
apply (metis leD linear order_trans successor_incr)
done

lemma upto_rec[code]: "[i..j] = (if i \<le> j then i # [successor i..j] else [])"
by(simp add: upto_def sorted_list_of_set_rec)

lemma upto_empty[simp]: "j < i \<Longrightarrow> [i..j] = []"
by(simp add: upto_rec)

lemma upto_rec2: "i \<le> j \<Longrightarrow> [i..successor j] = [i..j] @ [successor j]"
by(simp add: upto_def sorted_list_of_set_rec2)

end

text{* The integers are an instance of the above class: *}

instantiation int:: finite_intvl_succ
begin

definition
successor_int_def: "successor = (%i\<Colon>int. i+1)"

instance
by intro_classes (simp_all add: successor_int_def)

end

text{* Now @{term"[i..j::int]"} is defined for integers. *}

hide (open) const successor

lemma upto_rec2_int: "(i::int) \<le> j \<Longrightarrow> [i..j+1] = [i..j] @ [j+1]"
by(rule upto_rec2[where 'a = int, simplified successor_int_def])


subsubsection {* @{text lists}: the list-forming operator over sets *}

inductive_set
  lists :: "'a set => 'a list set"
  for A :: "'a set"
where
    Nil [intro!]: "[]: lists A"
  | Cons [intro!,noatp]: "[| a: A; l: lists A|] ==> a#l : lists A"

inductive_cases listsE [elim!,noatp]: "x#l : lists A"
inductive_cases listspE [elim!,noatp]: "listsp A (x # l)"

lemma listsp_mono [mono]: "A \<le> B ==> listsp A \<le> listsp B"
by (rule predicate1I, erule listsp.induct, blast+)

lemmas lists_mono = listsp_mono [to_set pred_subset_eq]

lemma listsp_infI:
  assumes l: "listsp A l" shows "listsp B l ==> listsp (inf A B) l" using l
by induct blast+

lemmas lists_IntI = listsp_infI [to_set]

lemma listsp_inf_eq [simp]: "listsp (inf A B) = inf (listsp A) (listsp B)"
proof (rule mono_inf [where f=listsp, THEN order_antisym])
  show "mono listsp" by (simp add: mono_def listsp_mono)
  show "inf (listsp A) (listsp B) \<le> listsp (inf A B)" by (blast intro!: listsp_infI predicate1I)
qed

lemmas listsp_conj_eq [simp] = listsp_inf_eq [simplified inf_fun_eq inf_bool_eq]

lemmas lists_Int_eq [simp] = listsp_inf_eq [to_set pred_equals_eq]

lemma append_in_listsp_conv [iff]:
     "(listsp A (xs @ ys)) = (listsp A xs \<and> listsp A ys)"
by (induct xs) auto

lemmas append_in_lists_conv [iff] = append_in_listsp_conv [to_set]

lemma in_listsp_conv_set: "(listsp A xs) = (\<forall>x \<in> set xs. A x)"
-- {* eliminate @{text listsp} in favour of @{text set} *}
by (induct xs) auto

lemmas in_lists_conv_set = in_listsp_conv_set [to_set]

lemma in_listspD [dest!,noatp]: "listsp A xs ==> \<forall>x\<in>set xs. A x"
by (rule in_listsp_conv_set [THEN iffD1])

lemmas in_listsD [dest!,noatp] = in_listspD [to_set]

lemma in_listspI [intro!,noatp]: "\<forall>x\<in>set xs. A x ==> listsp A xs"
by (rule in_listsp_conv_set [THEN iffD2])

lemmas in_listsI [intro!,noatp] = in_listspI [to_set]

lemma lists_UNIV [simp]: "lists UNIV = UNIV"
by auto



subsubsection{* Inductive definition for membership *}

inductive ListMem :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
    elem:  "ListMem x (x # xs)"
  | insert:  "ListMem x xs \<Longrightarrow> ListMem x (y # xs)"

lemma ListMem_iff: "(ListMem x xs) = (x \<in> set xs)"
apply (rule iffI)
 apply (induct set: ListMem)
  apply auto
apply (induct xs)
 apply (auto intro: ListMem.intros)
done



subsubsection{*Lists as Cartesian products*}

text{*@{text"set_Cons A Xs"}: the set of lists with head drawn from
@{term A} and tail drawn from @{term Xs}.*}

constdefs
  set_Cons :: "'a set \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
  "set_Cons A XS == {z. \<exists>x xs. z = x#xs & x \<in> A & xs \<in> XS}"
declare set_Cons_def [code del]

lemma set_Cons_sing_Nil [simp]: "set_Cons A {[]} = (%x. [x])`A"
by (auto simp add: set_Cons_def)

text{*Yields the set of lists, all of the same length as the argument and
with elements drawn from the corresponding element of the argument.*}

consts  listset :: "'a set list \<Rightarrow> 'a list set"
primrec
   "listset []    = {[]}"
   "listset(A#As) = set_Cons A (listset As)"


subsection{*Relations on Lists*}

subsubsection {* Length Lexicographic Ordering *}

text{*These orderings preserve well-foundedness: shorter lists 
  precede longer lists. These ordering are not used in dictionaries.*}

consts lexn :: "('a * 'a)set => nat => ('a list * 'a list)set"
        --{*The lexicographic ordering for lists of the specified length*}
primrec
  "lexn r 0 = {}"
  "lexn r (Suc n) =
    (prod_fun (%(x,xs). x#xs) (%(x,xs). x#xs) ` (r <*lex*> lexn r n)) Int
    {(xs,ys). length xs = Suc n \<and> length ys = Suc n}"

constdefs
  lex :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
    "lex r == \<Union>n. lexn r n"
        --{*Holds only between lists of the same length*}

  lenlex :: "('a \<times> 'a) set => ('a list \<times> 'a list) set"
    "lenlex r == inv_image (less_than <*lex*> lex r) (%xs. (length xs, xs))"
        --{*Compares lists by their length and then lexicographically*}

declare lex_def [code del]


lemma wf_lexn: "wf r ==> wf (lexn r n)"
apply (induct n, simp, simp)
apply(rule wf_subset)
 prefer 2 apply (rule Int_lower1)
apply(rule wf_prod_fun_image)
 prefer 2 apply (rule inj_onI, auto)
done

lemma lexn_length:
  "(xs, ys) : lexn r n ==> length xs = n \<and> length ys = n"
by (induct n arbitrary: xs ys) auto

lemma wf_lex [intro!]: "wf r ==> wf (lex r)"
apply (unfold lex_def)
apply (rule wf_UN)
apply (blast intro: wf_lexn, clarify)
apply (rename_tac m n)
apply (subgoal_tac "m \<noteq> n")
 prefer 2 apply blast
apply (blast dest: lexn_length not_sym)
done

lemma lexn_conv:
  "lexn r n =
    {(xs,ys). length xs = n \<and> length ys = n \<and>
    (\<exists>xys x y xs' ys'. xs= xys @ x#xs' \<and> ys= xys @ y # ys' \<and> (x, y):r)}"
apply (induct n, simp)
apply (simp add: image_Collect lex_prod_def, safe, blast)
 apply (rule_tac x = "ab # xys" in exI, simp)
apply (case_tac xys, simp_all, blast)
done

lemma lex_conv:
  "lex r =
    {(xs,ys). length xs = length ys \<and>
    (\<exists>xys x y xs' ys'. xs = xys @ x # xs' \<and> ys = xys @ y # ys' \<and> (x, y):r)}"
by (force simp add: lex_def lexn_conv)

lemma wf_lenlex [intro!]: "wf r ==> wf (lenlex r)"
by (unfold lenlex_def) blast

lemma lenlex_conv:
    "lenlex r = {(xs,ys). length xs < length ys |
                 length xs = length ys \<and> (xs, ys) : lex r}"
by (simp add: lenlex_def Id_on_def lex_prod_def inv_image_def)

lemma Nil_notin_lex [iff]: "([], ys) \<notin> lex r"
by (simp add: lex_conv)

lemma Nil2_notin_lex [iff]: "(xs, []) \<notin> lex r"
by (simp add:lex_conv)

lemma Cons_in_lex [simp]:
    "((x # xs, y # ys) : lex r) =
      ((x, y) : r \<and> length xs = length ys | x = y \<and> (xs, ys) : lex r)"
apply (simp add: lex_conv)
apply (rule iffI)
 prefer 2 apply (blast intro: Cons_eq_appendI, clarify)
apply (case_tac xys, simp, simp)
apply blast
done


subsubsection {* Lexicographic Ordering *}

text {* Classical lexicographic ordering on lists, ie. "a" < "ab" < "b".
    This ordering does \emph{not} preserve well-foundedness.
     Author: N. Voelker, March 2005. *} 

constdefs 
  lexord :: "('a * 'a)set \<Rightarrow> ('a list * 'a list) set" 
  "lexord  r == {(x,y). \<exists> a v. y = x @ a # v \<or> 
            (\<exists> u a b v w. (a,b) \<in> r \<and> x = u @ (a # v) \<and> y = u @ (b # w))}"
declare lexord_def [code del]

lemma lexord_Nil_left[simp]:  "([],y) \<in> lexord r = (\<exists> a x. y = a # x)"
by (unfold lexord_def, induct_tac y, auto) 

lemma lexord_Nil_right[simp]: "(x,[]) \<notin> lexord r"
by (unfold lexord_def, induct_tac x, auto)

lemma lexord_cons_cons[simp]:
     "((a # x, b # y) \<in> lexord r) = ((a,b)\<in> r | (a = b & (x,y)\<in> lexord r))"
  apply (unfold lexord_def, safe, simp_all)
  apply (case_tac u, simp, simp)
  apply (case_tac u, simp, clarsimp, blast, blast, clarsimp)
  apply (erule_tac x="b # u" in allE)
  by force

lemmas lexord_simps = lexord_Nil_left lexord_Nil_right lexord_cons_cons

lemma lexord_append_rightI: "\<exists> b z. y = b # z \<Longrightarrow> (x, x @ y) \<in> lexord r"
by (induct_tac x, auto)  

lemma lexord_append_left_rightI:
     "(a,b) \<in> r \<Longrightarrow> (u @ a # x, u @ b # y) \<in> lexord r"
by (induct_tac u, auto)

lemma lexord_append_leftI: " (u,v) \<in> lexord r \<Longrightarrow> (x @ u, x @ v) \<in> lexord r"
by (induct x, auto)

lemma lexord_append_leftD:
     "\<lbrakk> (x @ u, x @ v) \<in> lexord r; (! a. (a,a) \<notin> r) \<rbrakk> \<Longrightarrow> (u,v) \<in> lexord r"
by (erule rev_mp, induct_tac x, auto)

lemma lexord_take_index_conv: 
   "((x,y) : lexord r) = 
    ((length x < length y \<and> take (length x) y = x) \<or> 
     (\<exists>i. i < min(length x)(length y) & take i x = take i y & (x!i,y!i) \<in> r))"
  apply (unfold lexord_def Let_def, clarsimp) 
  apply (rule_tac f = "(% a b. a \<or> b)" in arg_cong2)
  apply auto 
  apply (rule_tac x="hd (drop (length x) y)" in exI)
  apply (rule_tac x="tl (drop (length x) y)" in exI)
  apply (erule subst, simp add: min_def) 
  apply (rule_tac x ="length u" in exI, simp) 
  apply (rule_tac x ="take i x" in exI) 
  apply (rule_tac x ="x ! i" in exI) 
  apply (rule_tac x ="y ! i" in exI, safe) 
  apply (rule_tac x="drop (Suc i) x" in exI)
  apply (drule sym, simp add: drop_Suc_conv_tl) 
  apply (rule_tac x="drop (Suc i) y" in exI)
  by (simp add: drop_Suc_conv_tl) 

-- {* lexord is extension of partial ordering List.lex *} 
lemma lexord_lex: " (x,y) \<in> lex r = ((x,y) \<in> lexord r \<and> length x = length y)"
  apply (rule_tac x = y in spec) 
  apply (induct_tac x, clarsimp) 
  by (clarify, case_tac x, simp, force)

lemma lexord_irreflexive: "(! x. (x,x) \<notin> r) \<Longrightarrow> (y,y) \<notin> lexord r"
  by (induct y, auto)

lemma lexord_trans: 
    "\<lbrakk> (x, y) \<in> lexord r; (y, z) \<in> lexord r; trans r \<rbrakk> \<Longrightarrow> (x, z) \<in> lexord r"
   apply (erule rev_mp)+
   apply (rule_tac x = x in spec) 
  apply (rule_tac x = z in spec) 
  apply ( induct_tac y, simp, clarify)
  apply (case_tac xa, erule ssubst) 
  apply (erule allE, erule allE) -- {* avoid simp recursion *} 
  apply (case_tac x, simp, simp) 
  apply (case_tac x, erule allE, erule allE, simp)
  apply (erule_tac x = listb in allE) 
  apply (erule_tac x = lista in allE, simp)
  apply (unfold trans_def)
  by blast

lemma lexord_transI:  "trans r \<Longrightarrow> trans (lexord r)"
by (rule transI, drule lexord_trans, blast) 

lemma lexord_linear: "(! a b. (a,b)\<in> r | a = b | (b,a) \<in> r) \<Longrightarrow> (x,y) : lexord r | x = y | (y,x) : lexord r"
  apply (rule_tac x = y in spec) 
  apply (induct_tac x, rule allI) 
  apply (case_tac x, simp, simp) 
  apply (rule allI, case_tac x, simp, simp) 
  by blast


subsection {* Lexicographic combination of measure functions *}

text {* These are useful for termination proofs *}

definition
  "measures fs = inv_image (lex less_than) (%a. map (%f. f a) fs)"

lemma wf_measures[recdef_wf, simp]: "wf (measures fs)"
unfolding measures_def
by blast

lemma in_measures[simp]: 
  "(x, y) \<in> measures [] = False"
  "(x, y) \<in> measures (f # fs)
         = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"  
unfolding measures_def
by auto

lemma measures_less: "f x < f y ==> (x, y) \<in> measures (f#fs)"
by simp

lemma measures_lesseq: "f x <= f y ==> (x, y) \<in> measures fs ==> (x, y) \<in> measures (f#fs)"
by auto


subsubsection{*Lifting a Relation on List Elements to the Lists*}

inductive_set
  listrel :: "('a * 'a)set => ('a list * 'a list)set"
  for r :: "('a * 'a)set"
where
    Nil:  "([],[]) \<in> listrel r"
  | Cons: "[| (x,y) \<in> r; (xs,ys) \<in> listrel r |] ==> (x#xs, y#ys) \<in> listrel r"

inductive_cases listrel_Nil1 [elim!]: "([],xs) \<in> listrel r"
inductive_cases listrel_Nil2 [elim!]: "(xs,[]) \<in> listrel r"
inductive_cases listrel_Cons1 [elim!]: "(y#ys,xs) \<in> listrel r"
inductive_cases listrel_Cons2 [elim!]: "(xs,y#ys) \<in> listrel r"


lemma listrel_mono: "r \<subseteq> s \<Longrightarrow> listrel r \<subseteq> listrel s"
apply clarify  
apply (erule listrel.induct)
apply (blast intro: listrel.intros)+
done

lemma listrel_subset: "r \<subseteq> A \<times> A \<Longrightarrow> listrel r \<subseteq> lists A \<times> lists A"
apply clarify 
apply (erule listrel.induct, auto) 
done

lemma listrel_refl_on: "refl_on A r \<Longrightarrow> refl_on (lists A) (listrel r)" 
apply (simp add: refl_on_def listrel_subset Ball_def)
apply (rule allI) 
apply (induct_tac x) 
apply (auto intro: listrel.intros)
done

lemma listrel_sym: "sym r \<Longrightarrow> sym (listrel r)" 
apply (auto simp add: sym_def)
apply (erule listrel.induct) 
apply (blast intro: listrel.intros)+
done

lemma listrel_trans: "trans r \<Longrightarrow> trans (listrel r)" 
apply (simp add: trans_def)
apply (intro allI) 
apply (rule impI) 
apply (erule listrel.induct) 
apply (blast intro: listrel.intros)+
done

theorem equiv_listrel: "equiv A r \<Longrightarrow> equiv (lists A) (listrel r)"
by (simp add: equiv_def listrel_refl_on listrel_sym listrel_trans) 

lemma listrel_Nil [simp]: "listrel r `` {[]} = {[]}"
by (blast intro: listrel.intros)

lemma listrel_Cons:
     "listrel r `` {x#xs} = set_Cons (r``{x}) (listrel r `` {xs})";
by (auto simp add: set_Cons_def intro: listrel.intros) 


subsection{*Miscellany*}

subsubsection {* Characters and strings *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

lemma UNIV_nibble:
  "UNIV = {Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x show "x \<in> ?A" by (cases x) simp_all
qed

instance nibble :: finite
  by default (simp add: UNIV_nibble)

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

lemma UNIV_char:
  "UNIV = image (split Char) (UNIV \<times> UNIV)"
proof (rule UNIV_eq_I)
  fix x show "x \<in> image (split Char) (UNIV \<times> UNIV)" by (cases x) auto
qed

instance char :: finite
  by default (simp add: UNIV_char)

lemma size_char [code, simp]:
  "size (c::char) = 0" by (cases c) simp

lemma char_size [code, simp]:
  "char_size (c::char) = 0" by (cases c) simp

primrec nibble_pair_of_char :: "char \<Rightarrow> nibble \<times> nibble" where
  "nibble_pair_of_char (Char n m) = (n, m)"

declare nibble_pair_of_char.simps [code del]

setup {*
let
  val nibbles = map (Thm.cterm_of @{theory} o HOLogic.mk_nibble) (0 upto 15);
  val thms = map_product
   (fn n => fn m => Drule.instantiate' [] [SOME n, SOME m] @{thm nibble_pair_of_char.simps})
      nibbles nibbles;
in
  PureThy.note_thmss Thm.lemmaK [((Binding.name "nibble_pair_of_char_simps", []), [(thms, [])])]
  #-> (fn [(_, thms)] => fold_rev Code.add_eqn thms)
end
*}

lemma char_case_nibble_pair [code, code inline]:
  "char_case f = split f o nibble_pair_of_char"
  by (simp add: expand_fun_eq split: char.split)

lemma char_rec_nibble_pair [code, code inline]:
  "char_rec f = split f o nibble_pair_of_char"
  unfolding char_case_nibble_pair [symmetric]
  by (simp add: expand_fun_eq split: char.split)

types string = "char list"

syntax
  "_Char" :: "xstr => char"    ("CHR _")
  "_String" :: "xstr => string"    ("_")

setup StringSyntax.setup


subsection {* Size function *}

lemma [measure_function]: "is_measure f \<Longrightarrow> is_measure (list_size f)"
by (rule is_measure_trivial)

lemma [measure_function]: "is_measure f \<Longrightarrow> is_measure (option_size f)"
by (rule is_measure_trivial)

lemma list_size_estimation[termination_simp]: 
  "x \<in> set xs \<Longrightarrow> y < f x \<Longrightarrow> y < list_size f xs"
by (induct xs) auto

lemma list_size_estimation'[termination_simp]: 
  "x \<in> set xs \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> list_size f xs"
by (induct xs) auto

lemma list_size_map[simp]: "list_size f (map g xs) = list_size (f o g) xs"
by (induct xs) auto

lemma list_size_pointwise[termination_simp]: 
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x < g x) \<Longrightarrow> list_size f xs \<le> list_size g xs"
by (induct xs) force+

subsection {* Code generator *}

subsubsection {* Setup *}

types_code
  "list" ("_ list")
attach (term_of) {*
fun term_of_list f T = HOLogic.mk_list T o map f;
*}
attach (test) {*
fun gen_list' aG aT i j = frequency
  [(i, fn () =>
      let
        val (x, t) = aG j;
        val (xs, ts) = gen_list' aG aT (i-1) j
      in (x :: xs, fn () => HOLogic.cons_const aT $ t () $ ts ()) end),
   (1, fn () => ([], fn () => HOLogic.nil_const aT))] ()
and gen_list aG aT i = gen_list' aG aT i i;
*}
  "char" ("string")
attach (term_of) {*
val term_of_char = HOLogic.mk_char o ord;
*}
attach (test) {*
fun gen_char i =
  let val j = random_range (ord "a") (Int.min (ord "a" + i, ord "z"))
  in (chr j, fn () => HOLogic.mk_char j) end;
*}

consts_code "Cons" ("(_ ::/ _)")

code_type list
  (SML "_ list")
  (OCaml "_ list")
  (Haskell "![_]")

code_reserved SML
  list

code_reserved OCaml
  list

code_const Nil
  (SML "[]")
  (OCaml "[]")
  (Haskell "[]")

ML {*
local

open Basic_Code_Thingol;

fun implode_list naming t = case pairself
  (Code_Thingol.lookup_const naming) (@{const_name Nil}, @{const_name Cons})
   of (SOME nil', SOME cons') => let
          fun dest_cons (IConst (c, _) `$ t1 `$ t2) =
                if c = cons'
                then SOME (t1, t2)
                else NONE
            | dest_cons _ = NONE;
          val (ts, t') = Code_Thingol.unfoldr dest_cons t;
        in case t'
         of IConst (c, _) => if c = nil' then SOME ts else NONE
          | _ => NONE
        end
    | _ => NONE

fun decode_char naming (IConst (c1, _), IConst (c2, _)) = (case map_filter
  (Code_Thingol.lookup_const naming)[@{const_name Nibble0}, @{const_name Nibble1},
   @{const_name Nibble2}, @{const_name Nibble3},
   @{const_name Nibble4}, @{const_name Nibble5},
   @{const_name Nibble6}, @{const_name Nibble7},
   @{const_name Nibble8}, @{const_name Nibble9},
   @{const_name NibbleA}, @{const_name NibbleB},
   @{const_name NibbleC}, @{const_name NibbleD},
   @{const_name NibbleE}, @{const_name NibbleF}]
   of nibbles' as [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => let
          fun idx c = find_index (curry (op =) c) nibbles';
          fun decode ~1 _ = NONE
            | decode _ ~1 = NONE
            | decode n m = SOME (chr (n * 16 + m));
        in decode (idx c1) (idx c2) end
    | _ => NONE)
 | decode_char _ _ = NONE
   
fun implode_string naming mk_char mk_string ts = case
  Code_Thingol.lookup_const naming @{const_name Char}
   of SOME char' => let
        fun implode_char (IConst (c, _) `$ t1 `$ t2) =
              if c = char' then decode_char naming (t1, t2) else NONE
          | implode_char _ = NONE;
        val ts' = map implode_char ts;
      in if forall is_some ts'
        then (SOME o Code_Printer.str o mk_string o implode o map_filter I) ts'
        else NONE
      end
    | _ => NONE;

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  Code_Printer.brackify_infix (target_fxy, Code_Printer.R) fxy [
    pr (Code_Printer.INFX (target_fxy, Code_Printer.X)) t1,
    Code_Printer.str target_cons,
    pr (Code_Printer.INFX (target_fxy, Code_Printer.R)) t2
  ];

fun pretty_list literals =
  let
    val mk_list = Code_Printer.literal_list literals;
    fun pretty pr naming thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list naming t2)
       of SOME ts => mk_list (map (pr vars Code_Printer.NOBR) ts)
        | NONE => default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_list_string literals =
  let
    val mk_list = Code_Printer.literal_list literals;
    val mk_char = Code_Printer.literal_char literals;
    val mk_string = Code_Printer.literal_string literals;
    fun pretty pr naming thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list naming t2)
       of SOME ts => (case implode_string naming mk_char mk_string ts
           of SOME p => p
            | NONE => mk_list (map (pr vars Code_Printer.NOBR) ts))
        | NONE => default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_char literals =
  let
    val mk_char = Code_Printer.literal_char literals;
    fun pretty _ naming thm _ _ [(t1, _), (t2, _)] =
      case decode_char naming (t1, t2)
       of SOME c => (Code_Printer.str o mk_char) c
        | NONE => Code_Printer.nerror thm "Illegal character expression";
  in (2, pretty) end;

fun pretty_message literals =
  let
    val mk_char = Code_Printer.literal_char literals;
    val mk_string = Code_Printer.literal_string literals;
    fun pretty _ naming thm _ _ [(t, _)] =
      case implode_list naming t
       of SOME ts => (case implode_string naming mk_char mk_string ts
           of SOME p => p
            | NONE => Code_Printer.nerror thm "Illegal message expression")
        | NONE => Code_Printer.nerror thm "Illegal message expression";
  in (1, pretty) end;

in

fun add_literal_list target thy =
  let
    val pr = pretty_list (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Cons} (SOME pr)
  end;

fun add_literal_list_string target thy =
  let
    val pr = pretty_list_string (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Cons} (SOME pr)
  end;

fun add_literal_char target thy =
  let
    val pr = pretty_char (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Char} (SOME pr)
  end;

fun add_literal_message str target thy =
  let
    val pr = pretty_message (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target str (SOME pr)
  end;

end;
*}

setup {*
  fold (fn target => add_literal_list target) ["SML", "OCaml", "Haskell"]
*}

code_instance list :: eq
  (Haskell -)

code_const "eq_class.eq \<Colon> 'a\<Colon>eq list \<Rightarrow> 'a list \<Rightarrow> bool"
  (Haskell infixl 4 "==")

setup {*
let

fun list_codegen thy defs dep thyname b t gr =
  let
    val ts = HOLogic.dest_list t;
    val (_, gr') = Codegen.invoke_tycodegen thy defs dep thyname false
      (fastype_of t) gr;
    val (ps, gr'') = fold_map
      (Codegen.invoke_codegen thy defs dep thyname false) ts gr'
  in SOME (Pretty.list "[" "]" ps, gr'') end handle TERM _ => NONE;

fun char_codegen thy defs dep thyname b t gr =
  let
    val i = HOLogic.dest_char t;
    val (_, gr') = Codegen.invoke_tycodegen thy defs dep thyname false
      (fastype_of t) gr;
  in SOME (Codegen.str (ML_Syntax.print_string (chr i)), gr')
  end handle TERM _ => NONE;

in
  Codegen.add_codegen "list_codegen" list_codegen
  #> Codegen.add_codegen "char_codegen" char_codegen
end;
*}


subsubsection {* Generation of efficient code *}

primrec
  member :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "mem" 55)
where 
  "x mem [] \<longleftrightarrow> False"
  | "x mem (y#ys) \<longleftrightarrow> x = y \<or> x mem ys"

primrec
  null:: "'a list \<Rightarrow> bool"
where
  "null [] = True"
  | "null (x#xs) = False"

primrec
  list_inter :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "list_inter [] bs = []"
  | "list_inter (a#as) bs =
     (if a \<in> set bs then a # list_inter as bs else list_inter as bs)"

primrec
  list_all :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"
where
  "list_all P [] = True"
  | "list_all P (x#xs) = (P x \<and> list_all P xs)"

primrec
  list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "list_ex P [] = False"
  | "list_ex P (x#xs) = (P x \<or> list_ex P xs)"

primrec
  filtermap :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "filtermap f [] = []"
  | "filtermap f (x#xs) =
     (case f x of None \<Rightarrow> filtermap f xs
      | Some y \<Rightarrow> y # filtermap f xs)"

primrec
  map_filter :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "map_filter f P [] = []"
  | "map_filter f P (x#xs) =
     (if P x then f x # map_filter f P xs else map_filter f P xs)"

primrec
  length_unique :: "'a list \<Rightarrow> nat"
where
  "length_unique [] = 0"
  | "length_unique (x#xs) =
      (if x \<in> set xs then length_unique xs else Suc (length_unique xs))"

text {*
  Only use @{text mem} for generating executable code.  Otherwise use
  @{prop "x : set xs"} instead --- it is much easier to reason about.
  The same is true for @{const list_all} and @{const list_ex}: write
  @{text "\<forall>x\<in>set xs"} and @{text "\<exists>x\<in>set xs"} instead because the HOL
  quantifiers are aleady known to the automatic provers. In fact, the
  declarations in the code subsection make sure that @{text "\<in>"},
  @{text "\<forall>x\<in>set xs"} and @{text "\<exists>x\<in>set xs"} are implemented
  efficiently.

  Efficient emptyness check is implemented by @{const null}.

  The functions @{const filtermap} and @{const map_filter} are just
  there to generate efficient code. Do not use
  them for modelling and proving.
*}

lemma rev_foldl_cons [code]:
  "rev xs = foldl (\<lambda>xs x. x # xs) [] xs"
proof (induct xs)
  case Nil then show ?case by simp
next
  case Cons
  {
    fix x xs ys
    have "foldl (\<lambda>xs x. x # xs) ys xs @ [x]
      = foldl (\<lambda>xs x. x # xs) (ys @ [x]) xs"
    by (induct xs arbitrary: ys) auto
  }
  note aux = this
  show ?case by (induct xs) (auto simp add: Cons aux)
qed

lemma mem_iff [code post]:
  "x mem xs \<longleftrightarrow> x \<in> set xs"
by (induct xs) auto

lemmas in_set_code [code unfold] = mem_iff [symmetric]

lemma empty_null [code inline]:
  "xs = [] \<longleftrightarrow> null xs"
by (cases xs) simp_all

lemmas null_empty [code post] =
  empty_null [symmetric]

lemma list_inter_conv:
  "set (list_inter xs ys) = set xs \<inter> set ys"
by (induct xs) auto

lemma list_all_iff [code post]:
  "list_all P xs \<longleftrightarrow> (\<forall>x \<in> set xs. P x)"
by (induct xs) auto

lemmas list_ball_code [code unfold] = list_all_iff [symmetric]

lemma list_all_append [simp]:
  "list_all P (xs @ ys) \<longleftrightarrow> (list_all P xs \<and> list_all P ys)"
by (induct xs) auto

lemma list_all_rev [simp]:
  "list_all P (rev xs) \<longleftrightarrow> list_all P xs"
by (simp add: list_all_iff)

lemma list_all_length:
  "list_all P xs \<longleftrightarrow> (\<forall>n < length xs. P (xs ! n))"
  unfolding list_all_iff by (auto intro: all_nth_imp_all_set)

lemma list_ex_iff [code post]:
  "list_ex P xs \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
by (induct xs) simp_all

lemmas list_bex_code [code unfold] =
  list_ex_iff [symmetric]

lemma list_ex_length:
  "list_ex P xs \<longleftrightarrow> (\<exists>n < length xs. P (xs ! n))"
  unfolding list_ex_iff set_conv_nth by auto

lemma filtermap_conv:
   "filtermap f xs = map (\<lambda>x. the (f x)) (filter (\<lambda>x. f x \<noteq> None) xs)"
by (induct xs) (simp_all split: option.split) 

lemma map_filter_conv [simp]:
  "map_filter f P xs = map f (filter P xs)"
by (induct xs) auto

lemma length_remdups_length_unique [code inline]:
  "length (remdups xs) = length_unique xs"
  by (induct xs) simp_all

hide (open) const length_unique


text {* Code for bounded quantification and summation over nats. *}

lemma atMost_upto [code unfold]:
  "{..n} = set [0..<Suc n]"
by auto

lemma atLeast_upt [code unfold]:
  "{..<n} = set [0..<n]"
by auto

lemma greaterThanLessThan_upt [code unfold]:
  "{n<..<m} = set [Suc n..<m]"
by auto

lemma atLeastLessThan_upt [code unfold]:
  "{n..<m} = set [n..<m]"
by auto

lemma greaterThanAtMost_upt [code unfold]:
  "{n<..m} = set [Suc n..<Suc m]"
by auto

lemma atLeastAtMost_upt [code unfold]:
  "{n..m} = set [n..<Suc m]"
by auto

lemma all_nat_less_eq [code unfold]:
  "(\<forall>m<n\<Colon>nat. P m) \<longleftrightarrow> (\<forall>m \<in> {0..<n}. P m)"
by auto

lemma ex_nat_less_eq [code unfold]:
  "(\<exists>m<n\<Colon>nat. P m) \<longleftrightarrow> (\<exists>m \<in> {0..<n}. P m)"
by auto

lemma all_nat_less [code unfold]:
  "(\<forall>m\<le>n\<Colon>nat. P m) \<longleftrightarrow> (\<forall>m \<in> {0..n}. P m)"
by auto

lemma ex_nat_less [code unfold]:
  "(\<exists>m\<le>n\<Colon>nat. P m) \<longleftrightarrow> (\<exists>m \<in> {0..n}. P m)"
by auto

lemma setsum_set_distinct_conv_listsum:
  "distinct xs \<Longrightarrow> setsum f (set xs) = listsum (map f xs)"
by (induct xs) simp_all

lemma setsum_set_upt_conv_listsum [code unfold]:
  "setsum f (set [m..<n]) = listsum (map f [m..<n])"
by (rule setsum_set_distinct_conv_listsum) simp


text {* Code for summation over ints. *}

lemma greaterThanLessThan_upto [code unfold]:
  "{i<..<j::int} = set [i+1..j - 1]"
by auto

lemma atLeastLessThan_upto [code unfold]:
  "{i..<j::int} = set [i..j - 1]"
by auto

lemma greaterThanAtMost_upto [code unfold]:
  "{i<..j::int} = set [i+1..j]"
by auto

lemma atLeastAtMost_upto [code unfold]:
  "{i..j::int} = set [i..j]"
by auto

lemma setsum_set_upto_conv_listsum [code unfold]:
  "setsum f (set [i..j::int]) = listsum (map f [i..j])"
by (rule setsum_set_distinct_conv_listsum) simp

end
