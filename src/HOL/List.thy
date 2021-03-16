(*  Title:      HOL/List.thy
    Author:     Tobias Nipkow; proofs tidied by LCP
*)

section \<open>The datatype of finite lists\<close>

theory List
imports Sledgehammer Code_Numeral Lifting_Set
begin

datatype (set: 'a) list =
    Nil  ("[]")
  | Cons (hd: 'a) (tl: "'a list")  (infixr "#" 65)
for
  map: map
  rel: list_all2
  pred: list_all
where
  "tl [] = []"

datatype_compat list

lemma [case_names Nil Cons, cases type: list]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "(y = [] \<Longrightarrow> P) \<Longrightarrow> (\<And>a list. y = a # list \<Longrightarrow> P) \<Longrightarrow> P"
by (rule list.exhaust)

lemma [case_names Nil Cons, induct type: list]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "P [] \<Longrightarrow> (\<And>a list. P list \<Longrightarrow> P (a # list)) \<Longrightarrow> P list"
by (rule list.induct)

text \<open>Compatibility:\<close>

setup \<open>Sign.mandatory_path "list"\<close>

lemmas inducts = list.induct
lemmas recs = list.rec
lemmas cases = list.case

setup \<open>Sign.parent_path\<close>

lemmas set_simps = list.set (* legacy *)

syntax
  \<comment> \<open>list Enumeration\<close>
  "_list" :: "args => 'a list"    ("[(_)]")

translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"


subsection \<open>Basic list processing functions\<close>

primrec (nonexhaustive) last :: "'a list \<Rightarrow> 'a" where
"last (x # xs) = (if xs = [] then x else last xs)"

primrec butlast :: "'a list \<Rightarrow> 'a list" where
"butlast [] = []" |
"butlast (x # xs) = (if xs = [] then [] else x # butlast xs)"

lemma set_rec: "set xs = rec_list {} (\<lambda>x _. insert x) xs"
  by (induct xs) auto

definition coset :: "'a list \<Rightarrow> 'a set" where
[simp]: "coset xs = - set xs"

primrec append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65) where
append_Nil: "[] @ ys = ys" |
append_Cons: "(x#xs) @ ys = x # xs @ ys"

primrec rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = rev xs @ [x]"

primrec filter:: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"filter P [] = []" |
"filter P (x # xs) = (if P x then x # filter P xs else filter P xs)"

text \<open>Special input syntax for filter:\<close>
syntax (ASCII)
  "_filter" :: "[pttrn, 'a list, bool] => 'a list"  ("(1[_<-_./ _])")
syntax
  "_filter" :: "[pttrn, 'a list, bool] => 'a list"  ("(1[_\<leftarrow>_ ./ _])")
translations
  "[x<-xs . P]" \<rightharpoonup> "CONST filter (\<lambda>x. P) xs"

primrec fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
fold_Nil:  "fold f [] = id" |
fold_Cons: "fold f (x # xs) = fold f xs \<circ> f x"

primrec foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
foldr_Nil:  "foldr f [] = id" |
foldr_Cons: "foldr f (x # xs) = f x \<circ> foldr f xs"

primrec foldl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b" where
foldl_Nil:  "foldl f a [] = a" |
foldl_Cons: "foldl f a (x # xs) = foldl f (f a x) xs"

primrec concat:: "'a list list \<Rightarrow> 'a list" where
"concat [] = []" |
"concat (x # xs) = x @ concat xs"

primrec drop:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
drop_Nil: "drop n [] = []" |
drop_Cons: "drop n (x # xs) = (case n of 0 \<Rightarrow> x # xs | Suc m \<Rightarrow> drop m xs)"
  \<comment> \<open>Warning: simpset does not contain this definition, but separate
       theorems for \<open>n = 0\<close> and \<open>n = Suc k\<close>\<close>

primrec take:: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
take_Nil:"take n [] = []" |
take_Cons: "take n (x # xs) = (case n of 0 \<Rightarrow> [] | Suc m \<Rightarrow> x # take m xs)"
  \<comment> \<open>Warning: simpset does not contain this definition, but separate
       theorems for \<open>n = 0\<close> and \<open>n = Suc k\<close>\<close>

primrec (nonexhaustive) nth :: "'a list => nat => 'a" (infixl "!" 100) where
nth_Cons: "(x # xs) ! n = (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> xs ! k)"
  \<comment> \<open>Warning: simpset does not contain this definition, but separate
       theorems for \<open>n = 0\<close> and \<open>n = Suc k\<close>\<close>

primrec list_update :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_update [] i v = []" |
"list_update (x # xs) i v =
  (case i of 0 \<Rightarrow> v # xs | Suc j \<Rightarrow> x # list_update xs j v)"

nonterminal lupdbinds and lupdbind

syntax
  "_lupdbind":: "['a, 'a] => lupdbind"    ("(2_ :=/ _)")
  "" :: "lupdbind => lupdbinds"    ("_")
  "_lupdbinds" :: "[lupdbind, lupdbinds] => lupdbinds"    ("_,/ _")
  "_LUpdate" :: "['a, lupdbinds] => 'a"    ("_/[(_)]" [1000,0] 900)

translations
  "_LUpdate xs (_lupdbinds b bs)" == "_LUpdate (_LUpdate xs b) bs"
  "xs[i:=x]" == "CONST list_update xs i x"

primrec takeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"takeWhile P [] = []" |
"takeWhile P (x # xs) = (if P x then x # takeWhile P xs else [])"

primrec dropWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"dropWhile P [] = []" |
"dropWhile P (x # xs) = (if P x then dropWhile P xs else x # xs)"

primrec zip :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"zip xs [] = []" |
zip_Cons: "zip xs (y # ys) =
  (case xs of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z, y) # zip zs ys)"
  \<comment> \<open>Warning: simpset does not contain this definition, but separate
       theorems for \<open>xs = []\<close> and \<open>xs = z # zs\<close>\<close>

abbreviation map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"map2 f xs ys \<equiv> map (\<lambda>(x,y). f x y) (zip xs ys)"

primrec product :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where
"product [] _ = []" |
"product (x#xs) ys = map (Pair x) ys @ product xs ys"

hide_const (open) product

primrec product_lists :: "'a list list \<Rightarrow> 'a list list" where
"product_lists [] = [[]]" |
"product_lists (xs # xss) = concat (map (\<lambda>x. map (Cons x) (product_lists xss)) xs)"

primrec upt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" ("(1[_..</_'])") where
upt_0: "[i..<0] = []" |
upt_Suc: "[i..<(Suc j)] = (if i \<le> j then [i..<j] @ [j] else [])"

definition insert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insert x xs = (if x \<in> set xs then xs else x # xs)"

definition union :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"union = fold insert"

hide_const (open) insert union
hide_fact (open) insert_def union_def

primrec find :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
"find _ [] = None" |
"find P (x#xs) = (if P x then Some x else find P xs)"

text \<open>In the context of multisets, \<open>count_list\<close> is equivalent to
  \<^term>\<open>count \<circ> mset\<close> and it it advisable to use the latter.\<close>
primrec count_list :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count_list [] y = 0" |
"count_list (x#xs) y = (if x=y then count_list xs y + 1 else count_list xs y)"

definition
   "extract" :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list * 'a * 'a list) option"
where "extract P xs =
  (case dropWhile (Not \<circ> P) xs of
     [] \<Rightarrow> None |
     y#ys \<Rightarrow> Some(takeWhile (Not \<circ> P) xs, y, ys))"

hide_const (open) "extract"

primrec those :: "'a option list \<Rightarrow> 'a list option"
where
"those [] = Some []" |
"those (x # xs) = (case x of
  None \<Rightarrow> None
| Some y \<Rightarrow> map_option (Cons y) (those xs))"

primrec remove1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove1 x [] = []" |
"remove1 x (y # xs) = (if x = y then xs else y # remove1 x xs)"

primrec removeAll :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"removeAll x [] = []" |
"removeAll x (y # xs) = (if x = y then removeAll x xs else y # removeAll x xs)"

primrec distinct :: "'a list \<Rightarrow> bool" where
"distinct [] \<longleftrightarrow> True" |
"distinct (x # xs) \<longleftrightarrow> x \<notin> set xs \<and> distinct xs"

fun successively :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"successively P []  = True" |
"successively P [x] = True" |
"successively P (x # y # xs) = (P x y \<and> successively P (y#xs))"

definition distinct_adj where
"distinct_adj = successively (\<noteq>)"

primrec remdups :: "'a list \<Rightarrow> 'a list" where
"remdups [] = []" |
"remdups (x # xs) = (if x \<in> set xs then remdups xs else x # remdups xs)"

fun remdups_adj :: "'a list \<Rightarrow> 'a list" where
"remdups_adj [] = []" |
"remdups_adj [x] = [x]" |
"remdups_adj (x # y # xs) = (if x = y then remdups_adj (x # xs) else x # remdups_adj (y # xs))"

primrec replicate :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
replicate_0: "replicate 0 x = []" |
replicate_Suc: "replicate (Suc n) x = x # replicate n x"

text \<open>
  Function \<open>size\<close> is overloaded for all datatypes. Users may
  refer to the list version as \<open>length\<close>.\<close>

abbreviation length :: "'a list \<Rightarrow> nat" where
"length \<equiv> size"

definition enumerate :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> 'a) list" where
enumerate_eq_zip: "enumerate n xs = zip [n..<n + length xs] xs"

primrec rotate1 :: "'a list \<Rightarrow> 'a list" where
"rotate1 [] = []" |
"rotate1 (x # xs) = xs @ [x]"

definition rotate :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"rotate n = rotate1 ^^ n"

definition nths :: "'a list => nat set => 'a list" where
"nths xs A = map fst (filter (\<lambda>p. snd p \<in> A) (zip xs [0..<size xs]))"

primrec subseqs :: "'a list \<Rightarrow> 'a list list" where
"subseqs [] = [[]]" |
"subseqs (x#xs) = (let xss = subseqs xs in map (Cons x) xss @ xss)"

primrec n_lists :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
"n_lists 0 xs = [[]]" |
"n_lists (Suc n) xs = concat (map (\<lambda>ys. map (\<lambda>y. y # ys) xs) (n_lists n xs))"

hide_const (open) n_lists

function splice :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"splice [] ys = ys" |
"splice (x#xs) ys = x # splice ys xs"
by pat_completeness auto

termination
by(relation "measure(\<lambda>(xs,ys). size xs + size ys)") auto

function shuffles where
  "shuffles [] ys = {ys}"
| "shuffles xs [] = {xs}"
| "shuffles (x # xs) (y # ys) = (#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys"
  by pat_completeness simp_all
termination by lexicographic_order

text\<open>Use only if you cannot use \<^const>\<open>Min\<close> instead:\<close>
fun min_list :: "'a::ord list \<Rightarrow> 'a" where
"min_list (x # xs) = (case xs of [] \<Rightarrow> x | _ \<Rightarrow> min x (min_list xs))"

text\<open>Returns first minimum:\<close>
fun arg_min_list :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"arg_min_list f [x] = x" |
"arg_min_list f (x#y#zs) = (let m = arg_min_list f (y#zs) in if f x \<le> f m then x else m)"

text\<open>
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
@{lemma "fold f [a,b,c] x = f c (f b (f a x))" by simp}\\
@{lemma "foldr f [a,b,c] x = f a (f b (f c x))" by simp}\\
@{lemma "foldl f x [a,b,c] = f (f (f x a) b) c" by simp}\\
@{lemma "successively (\<noteq>) [True,False,True,False]" by simp}\\
@{lemma "zip [a,b,c] [x,y,z] = [(a,x),(b,y),(c,z)]" by simp}\\
@{lemma "zip [a,b] [x,y,z] = [(a,x),(b,y)]" by simp}\\
@{lemma "enumerate 3 [a,b,c] = [(3,a),(4,b),(5,c)]" by normalization}\\
@{lemma "List.product [a,b] [c,d] = [(a, c), (a, d), (b, c), (b, d)]" by simp}\\
@{lemma "product_lists [[a,b], [c], [d,e]] = [[a,c,d], [a,c,e], [b,c,d], [b,c,e]]" by simp}\\
@{lemma "splice [a,b,c] [x,y,z] = [a,x,b,y,c,z]" by simp}\\
@{lemma "splice [a,b,c,d] [x,y] = [a,x,b,y,c,d]" by simp}\\
@{lemma "shuffles [a,b] [c,d] =  {[a,b,c,d],[a,c,b,d],[a,c,d,b],[c,a,b,d],[c,a,d,b],[c,d,a,b]}"
    by (simp add: insert_commute)}\\
@{lemma "take 2 [a,b,c,d] = [a,b]" by simp}\\
@{lemma "take 6 [a,b,c,d] = [a,b,c,d]" by simp}\\
@{lemma "drop 2 [a,b,c,d] = [c,d]" by simp}\\
@{lemma "drop 6 [a,b,c,d] = []" by simp}\\
@{lemma "takeWhile (%n::nat. n<3) [1,2,3,0] = [1,2]" by simp}\\
@{lemma "dropWhile (%n::nat. n<3) [1,2,3,0] = [3,0]" by simp}\\
@{lemma "distinct [2,0,1::nat]" by simp}\\
@{lemma "remdups [2,0,2,1::nat,2] = [0,1,2]" by simp}\\
@{lemma "remdups_adj [2,2,3,1,1::nat,2,1] = [2,3,1,2,1]" by simp}\\
@{lemma "List.insert 2 [0::nat,1,2] = [0,1,2]" by (simp add: List.insert_def)}\\
@{lemma "List.insert 3 [0::nat,1,2] = [3,0,1,2]" by (simp add: List.insert_def)}\\
@{lemma "List.union [2,3,4] [0::int,1,2] = [4,3,0,1,2]" by (simp add: List.insert_def List.union_def)}\\
@{lemma "List.find (%i::int. i>0) [0,0] = None" by simp}\\
@{lemma "List.find (%i::int. i>0) [0,1,0,2] = Some 1" by simp}\\
@{lemma "count_list [0,1,0,2::int] 0 = 2" by (simp)}\\
@{lemma "List.extract (%i::int. i>0) [0,0] = None" by(simp add: extract_def)}\\
@{lemma "List.extract (%i::int. i>0) [0,1,0,2] = Some([0], 1, [0,2])" by(simp add: extract_def)}\\
@{lemma "remove1 2 [2,0,2,1::nat,2] = [0,2,1,2]" by simp}\\
@{lemma "removeAll 2 [2,0,2,1::nat,2] = [0,1]" by simp}\\
@{lemma "nth [a,b,c,d] 2 = c" by simp}\\
@{lemma "[a,b,c,d][2 := x] = [a,b,x,d]" by simp}\\
@{lemma "nths [a,b,c,d,e] {0,2,3} = [a,c,d]" by (simp add:nths_def)}\\
@{lemma "subseqs [a,b] = [[a, b], [a], [b], []]" by simp}\\
@{lemma "List.n_lists 2 [a,b,c] = [[a, a], [b, a], [c, a], [a, b], [b, b], [c, b], [a, c], [b, c], [c, c]]" by (simp add: eval_nat_numeral)}\\
@{lemma "rotate1 [a,b,c,d] = [b,c,d,a]" by simp}\\
@{lemma "rotate 3 [a,b,c,d] = [d,a,b,c]" by (simp add:rotate_def eval_nat_numeral)}\\
@{lemma "replicate 4 a = [a,a,a,a]" by (simp add:eval_nat_numeral)}\\
@{lemma "[2..<5] = [2,3,4]" by (simp add:eval_nat_numeral)}\\
@{lemma "min_list [3,1,-2::int] = -2" by (simp)}\\
@{lemma "arg_min_list (\<lambda>i. i*i) [3,-1,1,-2::int] = -1" by (simp)}
\end{tabular}}
\caption{Characteristic examples}
\label{fig:Characteristic}
\end{figure}
Figure~\ref{fig:Characteristic} shows characteristic examples
that should give an intuitive understanding of the above functions.
\<close>

text\<open>The following simple sort(ed) functions are intended for proofs,
not for efficient implementations.\<close>

text \<open>A sorted predicate w.r.t. a relation:\<close>

fun sorted_wrt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
"sorted_wrt P [] = True" |
"sorted_wrt P (x # ys) = ((\<forall>y \<in> set ys. P x y) \<and> sorted_wrt P ys)"

text \<open>A class-based sorted predicate:\<close>

context linorder
begin

fun sorted :: "'a list \<Rightarrow> bool" where
"sorted [] = True" |
"sorted (x # ys) = ((\<forall>y \<in> set ys. x \<le> y) \<and> sorted ys)"

fun strict_sorted :: "'a list \<Rightarrow> bool" where
"strict_sorted [] = True" |
"strict_sorted (x # ys) = ((\<forall>y \<in> List.set ys. x < y) \<and> strict_sorted ys)"

lemma sorted_sorted_wrt: "sorted = sorted_wrt (\<le>)"
proof (rule ext)
  fix xs show "sorted xs = sorted_wrt (\<le>) xs"
    by(induction xs rule: sorted.induct) auto
qed

lemma strict_sorted_sorted_wrt: "strict_sorted = sorted_wrt (<)"
proof (rule ext)
  fix xs show "strict_sorted xs = sorted_wrt (<) xs"
    by(induction xs rule: strict_sorted.induct) auto
qed

primrec insort_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "insort_key f x [] = [x]" |
  "insort_key f x (y#ys) =
  (if f x \<le> f y then (x#y#ys) else y#(insort_key f x ys))"

definition sort_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "sort_key f xs = foldr (insort_key f) xs []"

definition insort_insert_key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "insort_insert_key f x xs =
  (if f x \<in> f ` set xs then xs else insort_key f x xs)"

abbreviation "sort \<equiv> sort_key (\<lambda>x. x)"
abbreviation "insort \<equiv> insort_key (\<lambda>x. x)"
abbreviation "insort_insert \<equiv> insort_insert_key (\<lambda>x. x)"

definition stable_sort_key :: "(('b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'b list) \<Rightarrow> bool" where
  "stable_sort_key sk =
   (\<forall>f xs k. filter (\<lambda>y. f y = k) (sk f xs) = filter (\<lambda>y. f y = k) xs)"

lemma strict_sorted_iff: "strict_sorted l \<longleftrightarrow> sorted l \<and> distinct l"
  by (induction l) (auto iff: antisym_conv1)

lemma strict_sorted_imp_sorted: "strict_sorted xs \<Longrightarrow> sorted xs"
  by (auto simp: strict_sorted_iff)

end


subsubsection \<open>List comprehension\<close>

text\<open>Input syntax for Haskell-like list comprehension notation.
Typical example: \<open>[(x,y). x \<leftarrow> xs, y \<leftarrow> ys, x \<noteq> y]\<close>,
the list of all pairs of distinct elements from \<open>xs\<close> and \<open>ys\<close>.
The syntax is as in Haskell, except that \<open>|\<close> becomes a dot
(like in Isabelle's set comprehension): \<open>[e. x \<leftarrow> xs, \<dots>]\<close> rather than
\verb![e| x <- xs, ...]!.

The qualifiers after the dot are
\begin{description}
\item[generators] \<open>p \<leftarrow> xs\<close>,
 where \<open>p\<close> is a pattern and \<open>xs\<close> an expression of list type, or
\item[guards] \<open>b\<close>, where \<open>b\<close> is a boolean expression.
%\item[local bindings] @ {text"let x = e"}.
\end{description}

Just like in Haskell, list comprehension is just a shorthand. To avoid
misunderstandings, the translation into desugared form is not reversed
upon output. Note that the translation of \<open>[e. x \<leftarrow> xs]\<close> is
optmized to \<^term>\<open>map (%x. e) xs\<close>.

It is easy to write short list comprehensions which stand for complex
expressions. During proofs, they may become unreadable (and
mangled). In such cases it can be advisable to introduce separate
definitions for the list comprehensions in question.\<close>

nonterminal lc_qual and lc_quals

syntax
  "_listcompr" :: "'a \<Rightarrow> lc_qual \<Rightarrow> lc_quals \<Rightarrow> 'a list"  ("[_ . __")
  "_lc_gen" :: "'a \<Rightarrow> 'a list \<Rightarrow> lc_qual"  ("_ \<leftarrow> _")
  "_lc_test" :: "bool \<Rightarrow> lc_qual" ("_")
  (*"_lc_let" :: "letbinds => lc_qual"  ("let _")*)
  "_lc_end" :: "lc_quals" ("]")
  "_lc_quals" :: "lc_qual \<Rightarrow> lc_quals \<Rightarrow> lc_quals"  (", __")

syntax (ASCII)
  "_lc_gen" :: "'a \<Rightarrow> 'a list \<Rightarrow> lc_qual"  ("_ <- _")

parse_translation \<open>
let
  val NilC = Syntax.const \<^const_syntax>\<open>Nil\<close>;
  val ConsC = Syntax.const \<^const_syntax>\<open>Cons\<close>;
  val mapC = Syntax.const \<^const_syntax>\<open>map\<close>;
  val concatC = Syntax.const \<^const_syntax>\<open>concat\<close>;
  val IfC = Syntax.const \<^const_syntax>\<open>If\<close>;
  val dummyC = Syntax.const \<^const_syntax>\<open>Pure.dummy_pattern\<close>

  fun single x = ConsC $ x $ NilC;

  fun pat_tr ctxt p e opti = (* %x. case x of p => e | _ => [] *)
    let
      (* FIXME proper name context!? *)
      val x =
        Free (singleton (Name.variant_list (fold Term.add_free_names [p, e] [])) "x", dummyT);
      val e = if opti then single e else e;
      val case1 = Syntax.const \<^syntax_const>\<open>_case1\<close> $ p $ e;
      val case2 =
        Syntax.const \<^syntax_const>\<open>_case1\<close> $ dummyC $ NilC;
      val cs = Syntax.const \<^syntax_const>\<open>_case2\<close> $ case1 $ case2;
    in Syntax_Trans.abs_tr [x, Case_Translation.case_tr false ctxt [x, cs]] end;

  fun pair_pat_tr (x as Free _) e = Syntax_Trans.abs_tr [x, e]
    | pair_pat_tr (_ $ p1 $ p2) e =
        Syntax.const \<^const_syntax>\<open>case_prod\<close> $ pair_pat_tr p1 (pair_pat_tr p2 e)
    | pair_pat_tr dummy e = Syntax_Trans.abs_tr [Syntax.const "_idtdummy", e]

  fun pair_pat ctxt (Const (\<^const_syntax>\<open>Pair\<close>,_) $ s $ t) =
        pair_pat ctxt s andalso pair_pat ctxt t
    | pair_pat ctxt (Free (s,_)) =
        let
          val thy = Proof_Context.theory_of ctxt;
          val s' = Proof_Context.intern_const ctxt s;
        in not (Sign.declared_const thy s') end
    | pair_pat _ t = (t = dummyC);

  fun abs_tr ctxt p e opti =
    let val p = Term_Position.strip_positions p
    in if pair_pat ctxt p
       then (pair_pat_tr p e, true)
       else (pat_tr ctxt p e opti, false)
    end

  fun lc_tr ctxt [e, Const (\<^syntax_const>\<open>_lc_test\<close>, _) $ b, qs] =
    let
      val res =
        (case qs of
           Const (\<^syntax_const>\<open>_lc_end\<close>, _) => single e
         | Const (\<^syntax_const>\<open>_lc_quals\<close>, _) $ q $ qs => lc_tr ctxt [e, q, qs]);
    in IfC $ b $ res $ NilC end
  | lc_tr ctxt
      [e, Const (\<^syntax_const>\<open>_lc_gen\<close>, _) $ p $ es,
          Const(\<^syntax_const>\<open>_lc_end\<close>, _)] =
      (case abs_tr ctxt p e true of
         (f, true) => mapC $ f $ es
       | (f, false) => concatC $ (mapC $ f $ es))
  | lc_tr ctxt
      [e, Const (\<^syntax_const>\<open>_lc_gen\<close>, _) $ p $ es,
          Const (\<^syntax_const>\<open>_lc_quals\<close>, _) $ q $ qs] =
      let val e' = lc_tr ctxt [e, q, qs];
      in concatC $ (mapC $ (fst (abs_tr ctxt p e' false)) $ es) end;

in [(\<^syntax_const>\<open>_listcompr\<close>, lc_tr)] end
\<close>

ML_val \<open>
  let
    val read = Syntax.read_term \<^context> o Syntax.implode_input;
    fun check s1 s2 =
      read s1 aconv read s2 orelse
        error ("Check failed: " ^
          quote (#1 (Input.source_content s1)) ^ Position.here_list [Input.pos_of s1, Input.pos_of s2]);
  in
    check \<open>[(x,y,z). b]\<close> \<open>if b then [(x, y, z)] else []\<close>;
    check \<open>[(x,y,z). (x,_,y)\<leftarrow>xs]\<close> \<open>map (\<lambda>(x,_,y). (x, y, z)) xs\<close>;
    check \<open>[e x y. (x,_)\<leftarrow>xs, y\<leftarrow>ys]\<close> \<open>concat (map (\<lambda>(x,_). map (\<lambda>y. e x y) ys) xs)\<close>;
    check \<open>[(x,y,z). x<a, x>b]\<close> \<open>if x < a then if b < x then [(x, y, z)] else [] else []\<close>;
    check \<open>[(x,y,z). x\<leftarrow>xs, x>b]\<close> \<open>concat (map (\<lambda>x. if b < x then [(x, y, z)] else []) xs)\<close>;
    check \<open>[(x,y,z). x<a, x\<leftarrow>xs]\<close> \<open>if x < a then map (\<lambda>x. (x, y, z)) xs else []\<close>;
    check \<open>[(x,y). Cons True x \<leftarrow> xs]\<close>
      \<open>concat (map (\<lambda>xa. case xa of [] \<Rightarrow> [] | True # x \<Rightarrow> [(x, y)] | False # x \<Rightarrow> []) xs)\<close>;
    check \<open>[(x,y,z). Cons x [] \<leftarrow> xs]\<close>
      \<open>concat (map (\<lambda>xa. case xa of [] \<Rightarrow> [] | [x] \<Rightarrow> [(x, y, z)] | x # aa # lista \<Rightarrow> []) xs)\<close>;
    check \<open>[(x,y,z). x<a, x>b, x=d]\<close>
      \<open>if x < a then if b < x then if x = d then [(x, y, z)] else [] else [] else []\<close>;
    check \<open>[(x,y,z). x<a, x>b, y\<leftarrow>ys]\<close>
      \<open>if x < a then if b < x then map (\<lambda>y. (x, y, z)) ys else [] else []\<close>;
    check \<open>[(x,y,z). x<a, (_,x)\<leftarrow>xs,y>b]\<close>
      \<open>if x < a then concat (map (\<lambda>(_,x). if b < y then [(x, y, z)] else []) xs) else []\<close>;
    check \<open>[(x,y,z). x<a, x\<leftarrow>xs, y\<leftarrow>ys]\<close>
      \<open>if x < a then concat (map (\<lambda>x. map (\<lambda>y. (x, y, z)) ys) xs) else []\<close>;
    check \<open>[(x,y,z). x\<leftarrow>xs, x>b, y<a]\<close>
      \<open>concat (map (\<lambda>x. if b < x then if y < a then [(x, y, z)] else [] else []) xs)\<close>;
    check \<open>[(x,y,z). x\<leftarrow>xs, x>b, y\<leftarrow>ys]\<close>
      \<open>concat (map (\<lambda>x. if b < x then map (\<lambda>y. (x, y, z)) ys else []) xs)\<close>;
    check \<open>[(x,y,z). x\<leftarrow>xs, (y,_)\<leftarrow>ys,y>x]\<close>
      \<open>concat (map (\<lambda>x. concat (map (\<lambda>(y,_). if x < y then [(x, y, z)] else []) ys)) xs)\<close>;
    check \<open>[(x,y,z). x\<leftarrow>xs, y\<leftarrow>ys,z\<leftarrow>zs]\<close>
      \<open>concat (map (\<lambda>x. concat (map (\<lambda>y. map (\<lambda>z. (x, y, z)) zs) ys)) xs)\<close>
  end;
\<close>

ML \<open>
(* Simproc for rewriting list comprehensions applied to List.set to set
   comprehension. *)

signature LIST_TO_SET_COMPREHENSION =
sig
  val simproc : Proof.context -> cterm -> thm option
end

structure List_to_Set_Comprehension : LIST_TO_SET_COMPREHENSION =
struct

(* conversion *)

fun all_exists_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Ex\<close>, _) $ Abs _ =>
      Conv.arg_conv (Conv.abs_conv (all_exists_conv cv o #2) ctxt) ct
  | _ => cv ctxt ct)

fun all_but_last_exists_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, Const (\<^const_name>\<open>Ex\<close>, _) $ _) =>
      Conv.arg_conv (Conv.abs_conv (all_but_last_exists_conv cv o #2) ctxt) ct
  | _ => cv ctxt ct)

fun Collect_conv cv ctxt ct =
  (case Thm.term_of ct of
    Const (\<^const_name>\<open>Collect\<close>, _) $ Abs _ => Conv.arg_conv (Conv.abs_conv cv ctxt) ct
  | _ => raise CTERM ("Collect_conv", [ct]))

fun rewr_conv' th = Conv.rewr_conv (mk_meta_eq th)

fun conjunct_assoc_conv ct =
  Conv.try_conv
    (rewr_conv' @{thm conj_assoc} then_conv HOLogic.conj_conv Conv.all_conv conjunct_assoc_conv) ct

fun right_hand_set_comprehension_conv conv ctxt =
  HOLogic.Trueprop_conv (HOLogic.eq_conv Conv.all_conv
    (Collect_conv (all_exists_conv conv o #2) ctxt))


(* term abstraction of list comprehension patterns *)

datatype termlets = If | Case of typ * int

local

val set_Nil_I = @{lemma "set [] = {x. False}" by (simp add: empty_def [symmetric])}
val set_singleton = @{lemma "set [a] = {x. x = a}" by simp}
val inst_Collect_mem_eq = @{lemma "set A = {x. x \<in> set A}" by simp}
val del_refl_eq = @{lemma "(t = t \<and> P) \<equiv> P" by simp}

fun mk_set T = Const (\<^const_name>\<open>set\<close>, HOLogic.listT T --> HOLogic.mk_setT T)
fun dest_set (Const (\<^const_name>\<open>set\<close>, _) $ xs) = xs

fun dest_singleton_list (Const (\<^const_name>\<open>Cons\<close>, _) $ t $ (Const (\<^const_name>\<open>Nil\<close>, _))) = t
  | dest_singleton_list t = raise TERM ("dest_singleton_list", [t])

(*We check that one case returns a singleton list and all other cases
  return [], and return the index of the one singleton list case.*)
fun possible_index_of_singleton_case cases =
  let
    fun check (i, case_t) s =
      (case strip_abs_body case_t of
        (Const (\<^const_name>\<open>Nil\<close>, _)) => s
      | _ => (case s of SOME NONE => SOME (SOME i) | _ => NONE))
  in
    fold_index check cases (SOME NONE) |> the_default NONE
  end

(*returns condition continuing term option*)
fun dest_if (Const (\<^const_name>\<open>If\<close>, _) $ cond $ then_t $ Const (\<^const_name>\<open>Nil\<close>, _)) =
      SOME (cond, then_t)
  | dest_if _ = NONE

(*returns (case_expr type index chosen_case constr_name) option*)
fun dest_case ctxt case_term =
  let
    val (case_const, args) = strip_comb case_term
  in
    (case try dest_Const case_const of
      SOME (c, T) =>
        (case Ctr_Sugar.ctr_sugar_of_case ctxt c of
          SOME {ctrs, ...} =>
            (case possible_index_of_singleton_case (fst (split_last args)) of
              SOME i =>
                let
                  val constr_names = map (fst o dest_Const) ctrs
                  val (Ts, _) = strip_type T
                  val T' = List.last Ts
                in SOME (List.last args, T', i, nth args i, nth constr_names i) end
            | NONE => NONE)
        | NONE => NONE)
    | NONE => NONE)
  end

fun tac ctxt [] =
      resolve_tac ctxt [set_singleton] 1 ORELSE
      resolve_tac ctxt [inst_Collect_mem_eq] 1
  | tac ctxt (If :: cont) =
      Splitter.split_tac ctxt @{thms if_split} 1
      THEN resolve_tac ctxt @{thms conjI} 1
      THEN resolve_tac ctxt @{thms impI} 1
      THEN Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
        CONVERSION (right_hand_set_comprehension_conv (K
          (HOLogic.conj_conv (Conv.rewr_conv (List.last prems RS @{thm Eq_TrueI})) Conv.all_conv
           then_conv
           rewr_conv' @{lemma "(True \<and> P) = P" by simp})) ctxt') 1) ctxt 1
      THEN tac ctxt cont
      THEN resolve_tac ctxt @{thms impI} 1
      THEN Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
          CONVERSION (right_hand_set_comprehension_conv (K
            (HOLogic.conj_conv (Conv.rewr_conv (List.last prems RS @{thm Eq_FalseI})) Conv.all_conv
             then_conv rewr_conv' @{lemma "(False \<and> P) = False" by simp})) ctxt') 1) ctxt 1
      THEN resolve_tac ctxt [set_Nil_I] 1
  | tac ctxt (Case (T, i) :: cont) =
      let
        val SOME {injects, distincts, case_thms, split, ...} =
          Ctr_Sugar.ctr_sugar_of ctxt (fst (dest_Type T))
      in
        (* do case distinction *)
        Splitter.split_tac ctxt [split] 1
        THEN EVERY (map_index (fn (i', _) =>
          (if i' < length case_thms - 1 then resolve_tac ctxt @{thms conjI} 1 else all_tac)
          THEN REPEAT_DETERM (resolve_tac ctxt @{thms allI} 1)
          THEN resolve_tac ctxt @{thms impI} 1
          THEN (if i' = i then
            (* continue recursively *)
            Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
              CONVERSION (Thm.eta_conversion then_conv right_hand_set_comprehension_conv (K
                  ((HOLogic.conj_conv
                    (HOLogic.eq_conv Conv.all_conv (rewr_conv' (List.last prems)) then_conv
                      (Conv.try_conv (Conv.rewrs_conv (map mk_meta_eq injects))))
                    Conv.all_conv)
                    then_conv (Conv.try_conv (Conv.rewr_conv del_refl_eq))
                    then_conv conjunct_assoc_conv)) ctxt'
                then_conv
                  (HOLogic.Trueprop_conv
                    (HOLogic.eq_conv Conv.all_conv (Collect_conv (fn (_, ctxt'') =>
                      Conv.repeat_conv
                        (all_but_last_exists_conv
                          (K (rewr_conv'
                            @{lemma "(\<exists>x. x = t \<and> P x) = P t" by simp})) ctxt'')) ctxt')))) 1) ctxt 1
            THEN tac ctxt cont
          else
            Subgoal.FOCUS (fn {prems, context = ctxt', ...} =>
              CONVERSION
                (right_hand_set_comprehension_conv (K
                  (HOLogic.conj_conv
                    ((HOLogic.eq_conv Conv.all_conv
                      (rewr_conv' (List.last prems))) then_conv
                      (Conv.rewrs_conv (map (fn th => th RS @{thm Eq_FalseI}) distincts)))
                    Conv.all_conv then_conv
                    (rewr_conv' @{lemma "(False \<and> P) = False" by simp}))) ctxt' then_conv
                  HOLogic.Trueprop_conv
                    (HOLogic.eq_conv Conv.all_conv
                      (Collect_conv (fn (_, ctxt'') =>
                        Conv.repeat_conv
                          (Conv.bottom_conv
                            (K (rewr_conv' @{lemma "(\<exists>x. P) = P" by simp})) ctxt'')) ctxt'))) 1) ctxt 1
            THEN resolve_tac ctxt [set_Nil_I] 1)) case_thms)
      end

in

fun simproc ctxt redex =
  let
    fun make_inner_eqs bound_vs Tis eqs t =
      (case dest_case ctxt t of
        SOME (x, T, i, cont, constr_name) =>
          let
            val (vs, body) = strip_abs (Envir.eta_long (map snd bound_vs) cont)
            val x' = incr_boundvars (length vs) x
            val eqs' = map (incr_boundvars (length vs)) eqs
            val constr_t =
              list_comb
                (Const (constr_name, map snd vs ---> T), map Bound (((length vs) - 1) downto 0))
            val constr_eq = Const (\<^const_name>\<open>HOL.eq\<close>, T --> T --> \<^typ>\<open>bool\<close>) $ constr_t $ x'
          in
            make_inner_eqs (rev vs @ bound_vs) (Case (T, i) :: Tis) (constr_eq :: eqs') body
          end
      | NONE =>
          (case dest_if t of
            SOME (condition, cont) => make_inner_eqs bound_vs (If :: Tis) (condition :: eqs) cont
          | NONE =>
            if null eqs then NONE (*no rewriting, nothing to be done*)
            else
              let
                val Type (\<^type_name>\<open>list\<close>, [rT]) = fastype_of1 (map snd bound_vs, t)
                val pat_eq =
                  (case try dest_singleton_list t of
                    SOME t' =>
                      Const (\<^const_name>\<open>HOL.eq\<close>, rT --> rT --> \<^typ>\<open>bool\<close>) $
                        Bound (length bound_vs) $ t'
                  | NONE =>
                      Const (\<^const_name>\<open>Set.member\<close>, rT --> HOLogic.mk_setT rT --> \<^typ>\<open>bool\<close>) $
                        Bound (length bound_vs) $ (mk_set rT $ t))
                val reverse_bounds = curry subst_bounds
                  ((map Bound ((length bound_vs - 1) downto 0)) @ [Bound (length bound_vs)])
                val eqs' = map reverse_bounds eqs
                val pat_eq' = reverse_bounds pat_eq
                val inner_t =
                  fold (fn (_, T) => fn t => HOLogic.exists_const T $ absdummy T t)
                    (rev bound_vs) (fold (curry HOLogic.mk_conj) eqs' pat_eq')
                val lhs = Thm.term_of redex
                val rhs = HOLogic.mk_Collect ("x", rT, inner_t)
                val rewrite_rule_t = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))
              in
                SOME
                  ((Goal.prove ctxt [] [] rewrite_rule_t
                    (fn {context = ctxt', ...} => tac ctxt' (rev Tis))) RS @{thm eq_reflection})
              end))
  in
    make_inner_eqs [] [] [] (dest_set (Thm.term_of redex))
  end

end

end
\<close>

simproc_setup list_to_set_comprehension ("set xs") =
  \<open>K List_to_Set_Comprehension.simproc\<close>

code_datatype set coset
hide_const (open) coset


subsubsection \<open>\<^const>\<open>Nil\<close> and \<^const>\<open>Cons\<close>\<close>

lemma not_Cons_self [simp]:
  "xs \<noteq> x # xs"
by (induct xs) auto

lemma not_Cons_self2 [simp]: "x # xs \<noteq> xs"
by (rule not_Cons_self [symmetric])

lemma neq_Nil_conv: "(xs \<noteq> []) = (\<exists>y ys. xs = y # ys)"
by (induct xs) auto

lemma tl_Nil: "tl xs = [] \<longleftrightarrow> xs = [] \<or> (\<exists>x. xs = [x])"
by (cases xs) auto

lemma Nil_tl: "[] = tl xs \<longleftrightarrow> xs = [] \<or> (\<exists>x. xs = [x])"
by (cases xs) auto

lemma length_induct:
  "(\<And>xs. \<forall>ys. length ys < length xs \<longrightarrow> P ys \<Longrightarrow> P xs) \<Longrightarrow> P xs"
by (fact measure_induct)

lemma induct_list012:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. \<lbrakk> P zs; P (y # zs) \<rbrakk> \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
by induction_schema (pat_completeness, lexicographic_order)

lemma list_nonempty_induct [consumes 1, case_names single cons]:
  "\<lbrakk> xs \<noteq> []; \<And>x. P [x]; \<And>x xs. xs \<noteq> [] \<Longrightarrow> P xs \<Longrightarrow> P (x # xs)\<rbrakk> \<Longrightarrow> P xs"
by(induction xs rule: induct_list012) auto

lemma inj_split_Cons: "inj_on (\<lambda>(xs, n). n#xs) X"
  by (auto intro!: inj_onI)

lemma inj_on_Cons1 [simp]: "inj_on ((#) x) A"
by(simp add: inj_on_def)


subsubsection \<open>\<^const>\<open>length\<close>\<close>

text \<open>
  Needs to come before \<open>@\<close> because of theorem \<open>append_eq_append_conv\<close>.
\<close>

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

lemma length_pos_if_in_set: "x \<in> set xs \<Longrightarrow> length xs > 0"
by auto

lemma length_Suc_conv: "(length xs = Suc n) = (\<exists>y ys. xs = y # ys \<and> length ys = n)"
by (induct xs) auto

lemma Suc_length_conv:
  "(Suc n = length xs) = (\<exists>y ys. xs = y # ys \<and> length ys = n)"
by (induct xs; simp; blast)

lemma Suc_le_length_iff:
  "(Suc n \<le> length xs) = (\<exists>x ys. xs = x # ys \<and> n \<le> length ys)"
by (metis Suc_le_D[of n] Suc_le_mono[of n] Suc_length_conv[of _ xs])

lemma impossible_Cons: "length xs \<le> length ys \<Longrightarrow> xs = x # ys = False"
by (induct xs) auto

lemma list_induct2 [consumes 1, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (x#xs) (y#ys))
   \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys) then show ?case by (cases ys) simp_all
qed simp

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

lemma list_induct4 [consumes 3, case_names Nil Cons]:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow>
   P [] [] [] [] \<Longrightarrow> (\<And>x xs y ys z zs w ws. length xs = length ys \<Longrightarrow>
   length ys = length zs \<Longrightarrow> length zs = length ws \<Longrightarrow> P xs ys zs ws \<Longrightarrow>
   P (x#xs) (y#ys) (z#zs) (w#ws)) \<Longrightarrow> P xs ys zs ws"
proof (induct xs arbitrary: ys zs ws)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs ws) then show ?case by ((cases ys, simp_all), (cases zs,simp_all)) (cases ws, simp_all)
qed

lemma list_induct2':
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
by (induct xs arbitrary: ys) (case_tac x, auto)+

lemma list_all2_iff:
  "list_all2 P xs ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>(x, y) \<in> set (zip xs ys). P x y)"
by (induct xs ys rule: list_induct2') auto

lemma neq_if_length_neq: "length xs \<noteq> length ys \<Longrightarrow> (xs = ys) == False"
by (rule Eq_FalseI) auto


subsubsection \<open>\<open>@\<close> -- append\<close>

global_interpretation append: monoid append Nil
proof
  fix xs ys zs :: "'a list"
  show "(xs @ ys) @ zs = xs @ (ys @ zs)"
    by (induct xs) simp_all
  show "xs @ [] = xs"
    by (induct xs) simp_all
qed simp

lemma append_assoc [simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by (fact append.assoc)

lemma append_Nil2: "xs @ [] = xs"
  by (fact append.right_neutral)

lemma append_is_Nil_conv [iff]: "(xs @ ys = []) = (xs = [] \<and> ys = [])"
by (induct xs) auto

lemma Nil_is_append_conv [iff]: "([] = xs @ ys) = (xs = [] \<and> ys = [])"
by (induct xs) auto

lemma append_self_conv [iff]: "(xs @ ys = xs) = (ys = [])"
by (induct xs) auto

lemma self_append_conv [iff]: "(xs = xs @ ys) = (ys = [])"
by (induct xs) auto

lemma append_eq_append_conv [simp]:
  "length xs = length ys \<or> length us = length vs
  \<Longrightarrow> (xs@us = ys@vs) = (xs=ys \<and> us=vs)"
  by (induct xs arbitrary: ys; case_tac ys; force)

lemma append_eq_append_conv2: "(xs @ ys = zs @ ts) =
  (\<exists>us. xs = zs @ us \<and> us @ ys = ts \<or> xs @ us = zs \<and> ys = us @ ts)"
proof (induct xs arbitrary: ys zs ts)
  case (Cons x xs)
  then show ?case
    by (cases zs) auto
qed fastforce

lemma same_append_eq [iff, induct_simp]: "(xs @ ys = xs @ zs) = (ys = zs)"
by simp

lemma append1_eq_conv [iff]: "(xs @ [x] = ys @ [y]) = (xs = ys \<and> x = y)"
by simp

lemma append_same_eq [iff, induct_simp]: "(ys @ xs = zs @ xs) = (ys = zs)"
by simp

lemma append_self_conv2 [iff]: "(xs @ ys = ys) = (xs = [])"
using append_same_eq [of _ _ "[]"] by auto

lemma self_append_conv2 [iff]: "(ys = xs @ ys) = (xs = [])"
using append_same_eq [of "[]"] by auto

lemma hd_Cons_tl: "xs \<noteq> [] \<Longrightarrow> hd xs # tl xs = xs"
  by (fact list.collapse)

lemma hd_append: "hd (xs @ ys) = (if xs = [] then hd ys else hd xs)"
by (induct xs) auto

lemma hd_append2 [simp]: "xs \<noteq> [] \<Longrightarrow> hd (xs @ ys) = hd xs"
by (simp add: hd_append split: list.split)

lemma tl_append: "tl (xs @ ys) = (case xs of [] \<Rightarrow> tl ys | z#zs \<Rightarrow> zs @ ys)"
by (simp split: list.split)

lemma tl_append2 [simp]: "xs \<noteq> [] \<Longrightarrow> tl (xs @ ys) = tl xs @ ys"
by (simp add: tl_append split: list.split)


lemma Cons_eq_append_conv: "x#xs = ys@zs =
 (ys = [] \<and> x#xs = zs \<or> (\<exists>ys'. x#ys' = ys \<and> xs = ys'@zs))"
by(cases ys) auto

lemma append_eq_Cons_conv: "(ys@zs = x#xs) =
 (ys = [] \<and> zs = x#xs \<or> (\<exists>ys'. ys = x#ys' \<and> ys'@zs = xs))"
by(cases ys) auto

lemma longest_common_prefix:
  "\<exists>ps xs' ys'. xs = ps @ xs' \<and> ys = ps @ ys'
       \<and> (xs' = [] \<or> ys' = [] \<or> hd xs' \<noteq> hd ys')"
by (induct xs ys rule: list_induct2')
   (blast, blast, blast,
    metis (no_types, hide_lams) append_Cons append_Nil list.sel(1))

text \<open>Trivial rules for solving \<open>@\<close>-equations automatically.\<close>

lemma eq_Nil_appendI: "xs = ys \<Longrightarrow> xs = [] @ ys"
  by simp

lemma Cons_eq_appendI: "\<lbrakk>x # xs1 = ys; xs = xs1 @ zs\<rbrakk> \<Longrightarrow> x # xs = ys @ zs"
  by auto

lemma append_eq_appendI: "\<lbrakk>xs @ xs1 = zs; ys = xs1 @ us\<rbrakk> \<Longrightarrow> xs @ ys = zs @ us"
  by auto


text \<open>
Simplification procedure for all list equalities.
Currently only tries to rearrange \<open>@\<close> to see if
- both lists end in a singleton list,
- or both lists end in the same list.
\<close>

simproc_setup list_eq ("(xs::'a list) = ys")  = \<open>
  let
    fun last (cons as Const (\<^const_name>\<open>Cons\<close>, _) $ _ $ xs) =
          (case xs of Const (\<^const_name>\<open>Nil\<close>, _) => cons | _ => last xs)
      | last (Const(\<^const_name>\<open>append\<close>,_) $ _ $ ys) = last ys
      | last t = t;

    fun list1 (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ Const(\<^const_name>\<open>Nil\<close>,_)) = true
      | list1 _ = false;

    fun butlast ((cons as Const(\<^const_name>\<open>Cons\<close>,_) $ x) $ xs) =
          (case xs of Const (\<^const_name>\<open>Nil\<close>, _) => xs | _ => cons $ butlast xs)
      | butlast ((app as Const (\<^const_name>\<open>append\<close>, _) $ xs) $ ys) = app $ butlast ys
      | butlast xs = Const(\<^const_name>\<open>Nil\<close>, fastype_of xs);

    val rearr_ss =
      simpset_of (put_simpset HOL_basic_ss \<^context>
        addsimps [@{thm append_assoc}, @{thm append_Nil}, @{thm append_Cons}]);

    fun list_eq ctxt (F as (eq as Const(_,eqT)) $ lhs $ rhs) =
      let
        val lastl = last lhs and lastr = last rhs;
        fun rearr conv =
          let
            val lhs1 = butlast lhs and rhs1 = butlast rhs;
            val Type(_,listT::_) = eqT
            val appT = [listT,listT] ---> listT
            val app = Const(\<^const_name>\<open>append\<close>,appT)
            val F2 = eq $ (app$lhs1$lastl) $ (app$rhs1$lastr)
            val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (F,F2));
            val thm = Goal.prove ctxt [] [] eq
              (K (simp_tac (put_simpset rearr_ss ctxt) 1));
          in SOME ((conv RS (thm RS trans)) RS eq_reflection) end;
      in
        if list1 lastl andalso list1 lastr then rearr @{thm append1_eq_conv}
        else if lastl aconv lastr then rearr @{thm append_same_eq}
        else NONE
      end;
  in fn _ => fn ctxt => fn ct => list_eq ctxt (Thm.term_of ct) end
\<close>


subsubsection \<open>\<^const>\<open>map\<close>\<close>

lemma hd_map: "xs \<noteq> [] \<Longrightarrow> hd (map f xs) = f (hd xs)"
by (cases xs) simp_all

lemma map_tl: "map f (tl xs) = tl (map f xs)"
by (cases xs) simp_all

lemma map_ext: "(\<And>x. x \<in> set xs \<longrightarrow> f x = g x) \<Longrightarrow> map f xs = map g xs"
by (induct xs) simp_all

lemma map_ident [simp]: "map (\<lambda>x. x) = (\<lambda>xs. xs)"
by (rule ext, induct_tac xs) auto

lemma map_append [simp]: "map f (xs @ ys) = map f xs @ map f ys"
by (induct xs) auto

lemma map_map [simp]: "map f (map g xs) = map (f \<circ> g) xs"
by (induct xs) auto

lemma map_comp_map[simp]: "((map f) \<circ> (map g)) = map(f \<circ> g)"
by (rule ext) simp

lemma rev_map: "rev (map f xs) = map f (rev xs)"
by (induct xs) auto

lemma map_eq_conv[simp]: "(map f xs = map g xs) = (\<forall>x \<in> set xs. f x = g x)"
by (induct xs) auto

lemma map_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> map f xs = map g ys"
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
  "(\<exists>xs. ys = map f xs) = (\<forall>y \<in> set ys. \<exists>x. y = f x)"
by(induct ys, auto simp add: Cons_eq_map_conv)

lemma map_eq_imp_length_eq:
  assumes "map f xs = map g ys"
  shows "length xs = length ys"
  using assms
proof (induct ys arbitrary: xs)
  case Nil then show ?case by simp
next
  case (Cons y ys) then obtain z zs where xs: "xs = z # zs" by auto
  from Cons xs have "map f zs = map g ys" by simp
  with Cons have "length zs = length ys" by blast
  with xs show ?case by simp
qed

lemma map_inj_on:
  assumes map: "map f xs = map f ys" and inj: "inj_on f (set xs Un set ys)"
  shows "xs = ys"
  using map_eq_imp_length_eq [OF map] assms
proof (induct rule: list_induct2)
  case (Cons x xs y ys)
  then show ?case
    by (auto intro: sym)
qed auto

lemma inj_on_map_eq_map:
  "inj_on f (set xs Un set ys) \<Longrightarrow> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_inj_on)

lemma map_injective:
  "map f xs = map f ys \<Longrightarrow> inj f \<Longrightarrow> xs = ys"
by (induct ys arbitrary: xs) (auto dest!:injD)

lemma inj_map_eq_map[simp]: "inj f \<Longrightarrow> (map f xs = map f ys) = (xs = ys)"
by(blast dest:map_injective)

lemma inj_mapI: "inj f \<Longrightarrow> inj (map f)"
by (iprover dest: map_injective injD intro: inj_onI)

lemma inj_mapD: "inj (map f) \<Longrightarrow> inj f"
  by (metis (no_types, hide_lams) injI list.inject list.simps(9) the_inv_f_f)

lemma inj_map[iff]: "inj (map f) = inj f"
by (blast dest: inj_mapD intro: inj_mapI)

lemma inj_on_mapI: "inj_on f (\<Union>(set ` A)) \<Longrightarrow> inj_on (map f) A"
  by (blast intro:inj_onI dest:inj_onD map_inj_on)

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

lemma map_fst_zip_take:
  "map fst (zip xs ys) = take (min (length xs) (length ys)) xs"
by (induct xs ys rule: list_induct2') simp_all

lemma map_snd_zip_take:
  "map snd (zip xs ys) = take (min (length xs) (length ys)) ys"
by (induct xs ys rule: list_induct2') simp_all

lemma map2_map_map: "map2 h (map f xs) (map g xs) = map (\<lambda>x. h (f x) (g x)) xs"
by (induction xs) (auto)

functor map: map
by (simp_all add: id_def)

declare map.id [simp]


subsubsection \<open>\<^const>\<open>rev\<close>\<close>

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
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by force
next
  case Cons
  then show ?case by (cases ys) auto
qed

lemma inj_on_rev[iff]: "inj_on rev A"
by(simp add:inj_on_def)

lemma rev_induct [case_names Nil snoc]:
  assumes "P []" and "\<And>x xs. P xs \<Longrightarrow> P (xs @ [x])"
  shows "P xs"
proof -
  have "P (rev (rev xs))"
    by (rule_tac list = "rev xs" in list.induct, simp_all add: assms)
  then show ?thesis by simp
qed

lemma rev_exhaust [case_names Nil snoc]:
  "(xs = [] \<Longrightarrow> P) \<Longrightarrow>(\<And>ys y. xs = ys @ [y] \<Longrightarrow> P) \<Longrightarrow> P"
by (induct xs rule: rev_induct) auto

lemmas rev_cases = rev_exhaust

lemma rev_nonempty_induct [consumes 1, case_names single snoc]:
  assumes "xs \<noteq> []"
  and single: "\<And>x. P [x]"
  and snoc': "\<And>x xs. xs \<noteq> [] \<Longrightarrow> P xs \<Longrightarrow> P (xs@[x])"
  shows "P xs"
using \<open>xs \<noteq> []\<close> proof (induct xs rule: rev_induct)
  case (snoc x xs) then show ?case
  proof (cases xs)
    case Nil thus ?thesis by (simp add: single)
  next
    case Cons with snoc show ?thesis by (fastforce intro!: snoc')
  qed
qed simp

lemma rev_eq_Cons_iff[iff]: "(rev xs = y#ys) = (xs = rev ys @ [y])"
by(rule rev_cases[of xs]) auto


subsubsection \<open>\<^const>\<open>set\<close>\<close>

declare list.set[code_post]  \<comment> \<open>pretty output\<close>

lemma finite_set [iff]: "finite (set xs)"
by (induct xs) auto

lemma set_append [simp]: "set (xs @ ys) = (set xs \<union> set ys)"
by (induct xs) auto

lemma hd_in_set[simp]: "xs \<noteq> [] \<Longrightarrow> hd xs \<in> set xs"
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

lemma set_filter [simp]: "set (filter P xs) = {x. x \<in> set xs \<and> P x}"
by (induct xs) auto

lemma set_upt [simp]: "set[i..<j] = {i..<j}"
by (induct j) auto


lemma split_list: "x \<in> set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case Cons thus ?case by (auto intro: Cons_eq_appendI)
qed

lemma in_set_conv_decomp: "x \<in> set xs \<longleftrightarrow> (\<exists>ys zs. xs = ys @ x # zs)"
  by (auto elim: split_list)

lemma split_list_first: "x \<in> set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  show ?case
  proof cases
    assume "x = a" thus ?case using Cons by fastforce
  next
    assume "x \<noteq> a" thus ?case using Cons by(fastforce intro!: Cons_eq_appendI)
  qed
qed

lemma in_set_conv_decomp_first:
  "(x \<in> set xs) = (\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set ys)"
  by (auto dest!: split_list_first)

lemma split_list_last: "x \<in> set xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set zs"
proof (induct xs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a xs)
  show ?case
  proof cases
    assume "x = a" thus ?case using snoc by (auto intro!: exI)
  next
    assume "x \<noteq> a" thus ?case using snoc by fastforce
  qed
qed

lemma in_set_conv_decomp_last:
  "(x \<in> set xs) = (\<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> set zs)"
  by (auto dest!: split_list_last)

lemma split_list_prop: "\<exists>x \<in> set xs. P x \<Longrightarrow> \<exists>ys x zs. xs = ys @ x # zs \<and> P x"
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
    hence "x # xs = [] @ x # xs \<and> P x \<and> (\<forall>y\<in>set []. \<not> P y)" by simp
    thus ?thesis by fast
  next
    assume "\<not> P x"
    hence "\<exists>x\<in>set xs. P x" using Cons(2) by simp
    thus ?thesis using \<open>\<not> P x\<close> Cons(1) by (metis append_Cons set_ConsD)
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
    assume "P x" thus ?thesis by (auto intro!: exI)
  next
    assume "\<not> P x"
    hence "\<exists>x\<in>set xs. P x" using snoc(2) by simp
    thus ?thesis using \<open>\<not> P x\<close> snoc(1) by fastforce
  qed
qed

lemma split_list_last_propE:
  assumes "\<exists>x \<in> set xs. P x"
  obtains ys x zs where "xs = ys @ x # zs" and "P x" and "\<forall>z \<in> set zs. \<not> P z"
using split_list_last_prop [OF assms] by blast

lemma split_list_last_prop_iff:
  "(\<exists>x \<in> set xs. P x) \<longleftrightarrow>
   (\<exists>ys x zs. xs = ys@x#zs \<and> P x \<and> (\<forall>z \<in> set zs. \<not> P z))"
  by rule (erule split_list_last_prop, auto)


lemma finite_list: "finite A \<Longrightarrow> \<exists>xs. set xs = A"
  by (erule finite_induct) (auto simp add: list.set(2)[symmetric] simp del: list.set(2))

lemma card_length: "card (set xs) \<le> length xs"
by (induct xs) (auto simp add: card_insert_if)

lemma set_minus_filter_out:
  "set xs - {y} = set (filter (\<lambda>x. \<not> (x = y)) xs)"
  by (induct xs) auto

lemma append_Cons_eq_iff:
  "\<lbrakk> x \<notin> set xs; x \<notin> set ys \<rbrakk> \<Longrightarrow>
   xs @ x # ys = xs' @ x # ys' \<longleftrightarrow> (xs = xs' \<and> ys = ys')"
by(auto simp: append_eq_Cons_conv Cons_eq_append_conv append_eq_append_conv2)


subsubsection \<open>\<^const>\<open>concat\<close>\<close>

lemma concat_append [simp]: "concat (xs @ ys) = concat xs @ concat ys"
  by (induct xs) auto

lemma concat_eq_Nil_conv [simp]: "(concat xss = []) = (\<forall>xs \<in> set xss. xs = [])"
  by (induct xss) auto

lemma Nil_eq_concat_conv [simp]: "([] = concat xss) = (\<forall>xs \<in> set xss. xs = [])"
  by (induct xss) auto

lemma set_concat [simp]: "set (concat xs) = (\<Union>x\<in>set xs. set x)"
  by (induct xs) auto

lemma concat_map_singleton[simp]: "concat(map (%x. [f x]) xs) = map f xs"
  by (induct xs) auto

lemma map_concat: "map f (concat xs) = concat (map (map f) xs)"
  by (induct xs) auto

lemma rev_concat: "rev (concat xs) = concat (map rev (rev xs))"
  by (induct xs) auto

lemma length_concat_rev[simp]: "length (concat (rev xs)) = length (concat xs)"
by (induction xs) auto

lemma concat_eq_concat_iff: "\<forall>(x, y) \<in> set (zip xs ys). length x = length y \<Longrightarrow> length xs = length ys \<Longrightarrow> (concat xs = concat ys) = (xs = ys)"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)
  thus ?case by (cases ys) auto
qed (auto)

lemma concat_injective: "concat xs = concat ys \<Longrightarrow> length xs = length ys \<Longrightarrow> \<forall>(x, y) \<in> set (zip xs ys). length x = length y \<Longrightarrow> xs = ys"
  by (simp add: concat_eq_concat_iff)

lemma concat_eq_appendD:
  assumes "concat xss = ys @ zs" "xss \<noteq> []"
  shows "\<exists>xss1 xs xs' xss2. xss = xss1 @ (xs @ xs') # xss2 \<and> ys = concat xss1 @ xs \<and> zs = xs' @ concat xss2"
  using assms
proof(induction xss arbitrary: ys)
  case (Cons xs xss)
  from Cons.prems consider
    us where "xs @ us = ys" "concat xss = us @ zs" |
    us where "xs = ys @ us" "us @ concat xss = zs"
    by(auto simp add: append_eq_append_conv2)
  then show ?case
  proof cases
    case 1
    then show ?thesis using Cons.IH[OF 1(2)]
      by(cases xss)(auto intro: exI[where x="[]"], metis append.assoc append_Cons concat.simps(2))
  qed(auto intro: exI[where x="[]"])
qed simp

lemma concat_eq_append_conv:
  "concat xss = ys @ zs \<longleftrightarrow>
  (if xss = [] then ys = [] \<and> zs = []
   else \<exists>xss1 xs xs' xss2. xss = xss1 @ (xs @ xs') # xss2 \<and> ys = concat xss1 @ xs \<and> zs = xs' @ concat xss2)"
  by(auto dest: concat_eq_appendD)

lemma hd_concat: "\<lbrakk>xs \<noteq> []; hd xs \<noteq> []\<rbrakk> \<Longrightarrow> hd (concat xs) = hd (hd xs)"
  by (metis concat.simps(2) hd_Cons_tl hd_append2)


simproc_setup list_neq ("(xs::'a list) = ys") = \<open>
(*
Reduces xs=ys to False if xs and ys cannot be of the same length.
This is the case if the atomic sublists of one are a submultiset
of those of the other list and there are fewer Cons's in one than the other.
*)

let

fun len (Const(\<^const_name>\<open>Nil\<close>,_)) acc = acc
  | len (Const(\<^const_name>\<open>Cons\<close>,_) $ _ $ xs) (ts,n) = len xs (ts,n+1)
  | len (Const(\<^const_name>\<open>append\<close>,_) $ xs $ ys) acc = len xs (len ys acc)
  | len (Const(\<^const_name>\<open>rev\<close>,_) $ xs) acc = len xs acc
  | len (Const(\<^const_name>\<open>map\<close>,_) $ _ $ xs) acc = len xs acc
  | len (Const(\<^const_name>\<open>concat\<close>,T) $ (Const(\<^const_name>\<open>rev\<close>,_) $ xss)) acc
    = len (Const(\<^const_name>\<open>concat\<close>,T) $ xss) acc 
  | len t (ts,n) = (t::ts,n);

val ss = simpset_of \<^context>;

fun list_neq ctxt ct =
  let
    val (Const(_,eqT) $ lhs $ rhs) = Thm.term_of ct;
    val (ls,m) = len lhs ([],0) and (rs,n) = len rhs ([],0);
    fun prove_neq() =
      let
        val Type(_,listT::_) = eqT;
        val size = HOLogic.size_const listT;
        val eq_len = HOLogic.mk_eq (size $ lhs, size $ rhs);
        val neq_len = HOLogic.mk_Trueprop (HOLogic.Not $ eq_len);
        val thm = Goal.prove ctxt [] [] neq_len
          (K (simp_tac (put_simpset ss ctxt) 1));
      in SOME (thm RS @{thm neq_if_length_neq}) end
  in
    if m < n andalso submultiset (op aconv) (ls,rs) orelse
       n < m andalso submultiset (op aconv) (rs,ls)
    then prove_neq() else NONE
  end;
in K list_neq end
\<close>

subsubsection \<open>\<^const>\<open>filter\<close>\<close>

lemma filter_append [simp]: "filter P (xs @ ys) = filter P xs @ filter P ys"
by (induct xs) auto

lemma rev_filter: "rev (filter P xs) = filter P (rev xs)"
by (induct xs) simp_all

lemma filter_filter [simp]: "filter P (filter Q xs) = filter (\<lambda>x. Q x \<and> P x) xs"
by (induct xs) auto

lemma filter_concat: "filter p (concat xs) = concat (map (filter p) xs)"
by (induct xs) auto

lemma length_filter_le [simp]: "length (filter P xs) \<le> length xs"
by (induct xs) (auto simp add: le_SucI)

lemma sum_length_filter_compl:
  "length(filter P xs) + length(filter (\<lambda>x. \<not>P x) xs) = length xs"
by(induct xs) simp_all

lemma filter_True [simp]: "\<forall>x \<in> set xs. P x \<Longrightarrow> filter P xs = xs"
by (induct xs) auto

lemma filter_False [simp]: "\<forall>x \<in> set xs. \<not> P x \<Longrightarrow> filter P xs = []"
by (induct xs) auto

lemma filter_empty_conv: "(filter P xs = []) = (\<forall>x\<in>set xs. \<not> P x)"
by (induct xs) simp_all

lemma filter_id_conv: "(filter P xs = xs) = (\<forall>x\<in>set xs. P x)"
proof (induct xs)
  case (Cons x xs)
  then show ?case
    using length_filter_le
    by (simp add: impossible_Cons)
qed auto

lemma filter_map: "filter P (map f xs) = map f (filter (P \<circ> f) xs)"
by (induct xs) simp_all

lemma length_filter_map[simp]:
  "length (filter P (map f xs)) = length(filter (P \<circ> f) xs)"
by (simp add:filter_map)

lemma filter_is_subset [simp]: "set (filter P xs) \<le> set xs"
by auto

lemma length_filter_less:
  "\<lbrakk> x \<in> set xs; \<not> P x \<rbrakk> \<Longrightarrow> length(filter P xs) < length xs"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case
    using Suc_le_eq by fastforce
qed

lemma length_filter_conv_card:
  "length(filter p xs) = card{i. i < length xs \<and> p(xs!i)}"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  let ?S = "{i. i < length xs \<and> p(xs!i)}"
  have fin: "finite ?S" by(fast intro: bounded_nat_set_is_finite)
  show ?case (is "?l = card ?S'")
  proof (cases)
    assume "p x"
    hence eq: "?S' = insert 0 (Suc ` ?S)"
      by(auto simp: image_def split:nat.split dest:gr0_implies_Suc)
    have "length (filter p (x # xs)) = Suc(card ?S)"
      using Cons \<open>p x\<close> by simp
    also have "\<dots> = Suc(card(Suc ` ?S))" using fin
      by (simp add: card_image)
    also have "\<dots> = card ?S'" using eq fin
      by (simp add:card_insert_if)
    finally show ?thesis .
  next
    assume "\<not> p x"
    hence eq: "?S' = Suc ` ?S"
      by(auto simp add: image_def split:nat.split elim:lessE)
    have "length (filter p (x # xs)) = card ?S"
      using Cons \<open>\<not> p x\<close> by simp
    also have "\<dots> = card(Suc ` ?S)" using fin
      by (simp add: card_image)
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
    with Cons obtain us vs where "?P (y#ys) (y#us) vs" by fastforce
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

lemma inj_on_filter_key_eq:
  assumes "inj_on f (insert y (set xs))"
  shows "filter (\<lambda>x. f y = f x) xs = filter (HOL.eq y) xs"
  using assms by (induct xs) auto

lemma filter_cong[fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> P x = Q x) \<Longrightarrow> filter P xs = filter Q ys"
  by (induct ys arbitrary: xs) auto


subsubsection \<open>List partitioning\<close>

primrec partition :: "('a \<Rightarrow> bool) \<Rightarrow>'a list \<Rightarrow> 'a list \<times> 'a list" where
  "partition P [] = ([], [])" |
  "partition P (x # xs) =
  (let (yes, no) = partition P xs
   in if P x then (x # yes, no) else (yes, x # no))"

lemma partition_filter1: "fst (partition P xs) = filter P xs"
  by (induct xs) (auto simp add: Let_def split_def)

lemma partition_filter2: "snd (partition P xs) = filter (Not \<circ> P) xs"
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

lemma partition_filter_conv[simp]:
  "partition f xs = (filter f xs,filter (Not \<circ> f) xs)"
  unfolding partition_filter2[symmetric]
  unfolding partition_filter1[symmetric] by simp

declare partition.simps[simp del]


subsubsection \<open>\<^const>\<open>nth\<close>\<close>

lemma nth_Cons_0 [simp, code]: "(x # xs)!0 = x"
  by auto

lemma nth_Cons_Suc [simp, code]: "(x # xs)!(Suc n) = xs!n"
  by auto

declare nth.simps [simp del]

lemma nth_Cons_pos[simp]: "0 < n \<Longrightarrow> (x#xs) ! n = xs ! (n - 1)"
  by(auto simp: Nat.gr0_conv_Suc)

lemma nth_append:
  "(xs @ ys)!n = (if n < length xs then xs!n else ys!(n - length xs))"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  then show ?case
    using less_Suc_eq_0_disj by auto
qed simp

lemma nth_append_length [simp]: "(xs @ x # ys) ! length xs = x"
  by (induct xs) auto

lemma nth_append_length_plus[simp]: "(xs @ ys) ! (length xs + n) = ys ! n"
  by (induct xs) auto

lemma nth_map [simp]: "n < length xs \<Longrightarrow> (map f xs)!n = f(xs!n)"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  then show ?case
    using less_Suc_eq_0_disj by auto
qed simp

lemma nth_tl: "n < length (tl xs) \<Longrightarrow> tl xs ! n = xs ! Suc n"
  by (induction xs) auto

lemma hd_conv_nth: "xs \<noteq> [] \<Longrightarrow> hd xs = xs!0"
  by(cases xs) simp_all


lemma list_eq_iff_nth_eq:
  "(xs = ys) = (length xs = length ys \<and> (\<forall>i<length xs. xs!i = ys!i))"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)
  show ?case
  proof (cases ys)
    case (Cons y ys)
    then show ?thesis
      using Cons.hyps by fastforce
  qed simp
qed force

lemma set_conv_nth: "set xs = {xs!i | i. i < length xs}"
proof (induct xs)
  case (Cons x xs)
  have "insert x {xs ! i |i. i < length xs} = {(x # xs) ! i |i. i < Suc (length xs)}" (is "?L=?R")
  proof
    show "?L \<subseteq> ?R"
      by force
    show "?R \<subseteq> ?L"
      using less_Suc_eq_0_disj by auto
  qed
  with Cons show ?case
    by simp
qed simp

lemma in_set_conv_nth: "(x \<in> set xs) = (\<exists>i < length xs. xs!i = x)"
  by(auto simp:set_conv_nth)

lemma nth_equal_first_eq:
  assumes "x \<notin> set xs"
  assumes "n \<le> length xs"
  shows "(x # xs) ! n = x \<longleftrightarrow> n = 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  show ?rhs
  proof (rule ccontr)
    assume "n \<noteq> 0"
    then have "n > 0" by simp
    with \<open>?lhs\<close> have "xs ! (n - 1) = x" by simp
    moreover from \<open>n > 0\<close> \<open>n \<le> length xs\<close> have "n - 1 < length xs" by simp
    ultimately have "\<exists>i<length xs. xs ! i = x" by auto
    with \<open>x \<notin> set xs\<close> in_set_conv_nth [of x xs] show False by simp
  qed
next
  assume ?rhs then show ?lhs by simp
qed

lemma nth_non_equal_first_eq:
  assumes "x \<noteq> y"
  shows "(x # xs) ! n = y \<longleftrightarrow> xs ! (n - 1) = y \<and> n > 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs" with assms have "n > 0" by (cases n) simp_all
  with \<open>?lhs\<close> show ?rhs by simp
next
  assume "?rhs" then show "?lhs" by simp
qed

lemma list_ball_nth: "\<lbrakk>n < length xs; \<forall>x \<in> set xs. P x\<rbrakk> \<Longrightarrow> P(xs!n)"
  by (auto simp add: set_conv_nth)

lemma nth_mem [simp]: "n < length xs \<Longrightarrow> xs!n \<in> set xs"
  by (auto simp add: set_conv_nth)

lemma all_nth_imp_all_set:
  "\<lbrakk>\<forall>i < length xs. P(xs!i); x \<in> set xs\<rbrakk> \<Longrightarrow> P x"
  by (auto simp add: set_conv_nth)

lemma all_set_conv_all_nth:
  "(\<forall>x \<in> set xs. P x) = (\<forall>i. i < length xs \<longrightarrow> P (xs ! i))"
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
    with n obtain n' where n': "length xs - n = Suc n'"
      by (cases "length xs - n", auto)
    moreover
    from n' have "length xs - Suc n = n'" by simp
    ultimately
    have "xs ! (length xs - Suc n) = (x # xs) ! (length xs - n)" by simp
  }
  ultimately
  show ?case by (clarsimp simp add: Cons nth_append)
qed

lemma Skolem_list_nth:
  "(\<forall>i<k. \<exists>x. P i x) = (\<exists>xs. size xs = k \<and> (\<forall>i<k. P i (xs!i)))"
  (is "_ = (\<exists>xs. ?P k xs)")
proof(induct k)
  case 0 show ?case by simp
next
  case (Suc k)
  show ?case (is "?L = ?R" is "_ = (\<exists>xs. ?P' xs)")
  proof
    assume "?R" thus "?L" using Suc by auto
  next
    assume "?L"
    with Suc obtain x xs where "?P k xs \<and> P k x" by (metis less_Suc_eq)
    hence "?P'(xs@[x])" by(simp add:nth_append less_Suc_eq)
    thus "?R" ..
  qed
qed


subsubsection \<open>\<^const>\<open>list_update\<close>\<close>

lemma length_list_update [simp]: "length(xs[i:=x]) = length xs"
  by (induct xs arbitrary: i) (auto split: nat.split)

lemma nth_list_update:
  "i < length xs\<Longrightarrow> (xs[i:=x])!j = (if i = j then x else xs!j)"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma nth_list_update_eq [simp]: "i < length xs \<Longrightarrow> (xs[i:=x])!i = x"
  by (simp add: nth_list_update)

lemma nth_list_update_neq [simp]: "i \<noteq> j \<Longrightarrow> xs[i:=x]!j = xs!j"
  by (induct xs arbitrary: i j) (auto simp add: nth_Cons split: nat.split)

lemma list_update_id[simp]: "xs[i := xs!i] = xs"
  by (induct xs arbitrary: i) (simp_all split:nat.splits)

lemma list_update_beyond[simp]: "length xs \<le> i \<Longrightarrow> xs[i:=x] = xs"
proof (induct xs arbitrary: i)
  case (Cons x xs i)
  then show ?case
    by (metis leD length_list_update list_eq_iff_nth_eq nth_list_update_neq)
qed simp

lemma list_update_nonempty[simp]: "xs[k:=x] = [] \<longleftrightarrow> xs=[]"
  by (simp only: length_0_conv[symmetric] length_list_update)

lemma list_update_same_conv:
  "i < length xs \<Longrightarrow> (xs[i := x] = xs) = (xs!i = x)"
  by (induct xs arbitrary: i) (auto split: nat.split)

lemma list_update_append1:
  "i < size xs \<Longrightarrow> (xs @ ys)[i:=x] = xs[i:=x] @ ys"
  by (induct xs arbitrary: i)(auto split:nat.split)

lemma list_update_append:
  "(xs @ ys) [n:= x] =
  (if n < length xs then xs[n:= x] @ ys else xs @ (ys [n-length xs:= x]))"
  by (induct xs arbitrary: n) (auto split:nat.splits)

lemma list_update_length [simp]:
  "(xs @ x # ys)[length xs := y] = (xs @ y # ys)"
  by (induct xs, auto)

lemma map_update: "map f (xs[k:= y]) = (map f xs)[k := f y]"
  by(induct xs arbitrary: k)(auto split:nat.splits)

lemma rev_update:
  "k < length xs \<Longrightarrow> rev (xs[k:= y]) = (rev xs)[length xs - k - 1 := y]"
  by (induct xs arbitrary: k) (auto simp: list_update_append split:nat.splits)

lemma update_zip:
  "(zip xs ys)[i:=xy] = zip (xs[i:=fst xy]) (ys[i:=snd xy])"
  by (induct ys arbitrary: i xy xs) (auto, case_tac xs, auto split: nat.split)

lemma set_update_subset_insert: "set(xs[i:=x]) \<le> insert x (set xs)"
  by (induct xs arbitrary: i) (auto split: nat.split)

lemma set_update_subsetI: "\<lbrakk>set xs \<subseteq> A; x \<in> A\<rbrakk> \<Longrightarrow> set(xs[i := x]) \<subseteq> A"
  by (blast dest!: set_update_subset_insert [THEN subsetD])

lemma set_update_memI: "n < length xs \<Longrightarrow> x \<in> set (xs[n := x])"
  by (induct xs arbitrary: n) (auto split:nat.splits)

lemma list_update_overwrite[simp]:
  "xs [i := x, i := y] = xs [i := y]"
  by (induct xs arbitrary: i) (simp_all split: nat.split)

lemma list_update_swap:
  "i \<noteq> i' \<Longrightarrow> xs [i := x, i' := x'] = xs [i' := x', i := x]"
  by (induct xs arbitrary: i i') (simp_all split: nat.split)

lemma list_update_code [code]:
  "[][i := y] = []"
  "(x # xs)[0 := y] = y # xs"
  "(x # xs)[Suc i := y] = x # xs[i := y]"
  by simp_all


subsubsection \<open>\<^const>\<open>last\<close> and \<^const>\<open>butlast\<close>\<close>

lemma last_snoc [simp]: "last (xs @ [x]) = x"
  by (induct xs) auto

lemma butlast_snoc [simp]: "butlast (xs @ [x]) = xs"
  by (induct xs) auto

lemma last_ConsL: "xs = [] \<Longrightarrow> last(x#xs) = x"
  by simp

lemma last_ConsR: "xs \<noteq> [] \<Longrightarrow> last(x#xs) = last xs"
  by simp

lemma last_append: "last(xs @ ys) = (if ys = [] then last xs else last ys)"
  by (induct xs) (auto)

lemma last_appendL[simp]: "ys = [] \<Longrightarrow> last(xs @ ys) = last xs"
  by(simp add:last_append)

lemma last_appendR[simp]: "ys \<noteq> [] \<Longrightarrow> last(xs @ ys) = last ys"
  by(simp add:last_append)

lemma last_tl: "xs = [] \<or> tl xs \<noteq> [] \<Longrightarrow>last (tl xs) = last xs"
  by (induct xs) simp_all

lemma butlast_tl: "butlast (tl xs) = tl (butlast xs)"
  by (induct xs) simp_all

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
  "xs \<noteq> [] \<Longrightarrow> butlast xs @ [last xs] = xs"
  by (induct xs) auto

lemma in_set_butlastD: "x \<in> set (butlast xs) \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma in_set_butlast_appendI:
  "x \<in> set (butlast xs) \<or> x \<in> set (butlast ys) \<Longrightarrow> x \<in> set (butlast (xs @ ys))"
  by (auto dest: in_set_butlastD simp add: butlast_append)

lemma last_drop[simp]: "n < length xs \<Longrightarrow> last (drop n xs) = last xs"
  by (induct xs arbitrary: n)(auto split:nat.split)

lemma nth_butlast:
  assumes "n < length (butlast xs)" shows "butlast xs ! n = xs ! n"
proof (cases xs)
  case (Cons y ys)
  moreover from assms have "butlast xs ! n = (butlast xs @ [last xs]) ! n"
    by (simp add: nth_append)
  ultimately show ?thesis using append_butlast_last_id by simp
qed simp

lemma last_conv_nth: "xs\<noteq>[] \<Longrightarrow> last xs = xs!(length xs - 1)"
  by(induct xs)(auto simp:neq_Nil_conv)

lemma butlast_conv_take: "butlast xs = take (length xs - 1) xs"
  by (induction xs rule: induct_list012) simp_all

lemma last_list_update:
  "xs \<noteq> [] \<Longrightarrow> last(xs[k:=x]) = (if k = size xs - 1 then x else last xs)"
  by (auto simp: last_conv_nth)

lemma butlast_list_update:
  "butlast(xs[k:=x]) =
  (if k = size xs - 1 then butlast xs else (butlast xs)[k:=x])"
  by(cases xs rule:rev_cases)(auto simp: list_update_append split: nat.splits)

lemma last_map: "xs \<noteq> [] \<Longrightarrow> last (map f xs) = f (last xs)"
  by (cases xs rule: rev_cases) simp_all

lemma map_butlast: "map f (butlast xs) = butlast (map f xs)"
  by (induct xs) simp_all

lemma snoc_eq_iff_butlast:
  "xs @ [x] = ys \<longleftrightarrow> (ys \<noteq> [] \<and> butlast ys = xs \<and> last ys = x)"
  by fastforce

corollary longest_common_suffix:
  "\<exists>ss xs' ys'. xs = xs' @ ss \<and> ys = ys' @ ss
       \<and> (xs' = [] \<or> ys' = [] \<or> last xs' \<noteq> last ys')"
  using longest_common_prefix[of "rev xs" "rev ys"]
  unfolding rev_swap rev_append by (metis last_rev rev_is_Nil_conv)

lemma butlast_rev [simp]: "butlast (rev xs) = rev (tl xs)"
  by (cases xs) simp_all


subsubsection \<open>\<^const>\<open>take\<close> and \<^const>\<open>drop\<close>\<close>

lemma take_0: "take 0 xs = []"
  by (induct xs) auto

lemma drop_0: "drop 0 xs = xs"
  by (induct xs) auto

lemma take0[simp]: "take 0 = (\<lambda>xs. [])"
  by(rule ext) (rule take_0)

lemma drop0[simp]: "drop 0 = (\<lambda>x. x)"
  by(rule ext) (rule drop_0)

lemma take_Suc_Cons [simp]: "take (Suc n) (x # xs) = x # take n xs"
  by simp

lemma drop_Suc_Cons [simp]: "drop (Suc n) (x # xs) = drop n xs"
  by simp

declare take_Cons [simp del] and drop_Cons [simp del]

lemma take_Suc: "xs \<noteq> [] \<Longrightarrow> take (Suc n) xs = hd xs # take n (tl xs)"
  by(clarsimp simp add:neq_Nil_conv)

lemma drop_Suc: "drop (Suc n) xs = drop n (tl xs)"
  by(cases xs, simp_all)

lemma hd_take[simp]: "j > 0 \<Longrightarrow> hd (take j xs) = hd xs"
  by (metis gr0_conv_Suc list.sel(1) take.simps(1) take_Suc)

lemma take_tl: "take n (tl xs) = tl (take (Suc n) xs)"
  by (induct xs arbitrary: n) simp_all

lemma drop_tl: "drop n (tl xs) = tl(drop n xs)"
  by(induct xs arbitrary: n, simp_all add:drop_Cons drop_Suc split:nat.split)

lemma tl_take: "tl (take n xs) = take (n - 1) (tl xs)"
  by (cases n, simp, cases xs, auto)

lemma tl_drop: "tl (drop n xs) = drop n (tl xs)"
  by (simp only: drop_tl)

lemma nth_via_drop: "drop n xs = y#ys \<Longrightarrow> xs!n = y"
  by (induct xs arbitrary: n, simp)(auto simp: drop_Cons nth_Cons split: nat.splits)

lemma take_Suc_conv_app_nth:
  "i < length xs \<Longrightarrow> take (Suc i) xs = take i xs @ [xs!i]"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases i) auto
qed

lemma Cons_nth_drop_Suc:
  "i < length xs \<Longrightarrow> (xs!i) # (drop (Suc i) xs) = drop i xs"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases i) auto
qed

lemma length_take [simp]: "length (take n xs) = min (length xs) n"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma length_drop [simp]: "length (drop n xs) = (length xs - n)"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_all [simp]: "length xs \<le> n \<Longrightarrow> take n xs = xs"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma drop_all [simp]: "length xs \<le> n \<Longrightarrow> drop n xs = []"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_all_iff [simp]: "take n xs = xs \<longleftrightarrow> length xs \<le> n"
by (metis length_take min.order_iff take_all)

lemma drop_all_iff [simp]: "drop n xs = [] \<longleftrightarrow> length xs \<le> n"
by (metis diff_is_0_eq drop_all length_drop list.size(3))

lemma take_append [simp]:
  "take n (xs @ ys) = (take n xs @ take (n - length xs) ys)"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma drop_append [simp]:
  "drop n (xs @ ys) = drop n xs @ drop (n - length xs) ys"
  by (induct n arbitrary: xs) (auto, case_tac xs, auto)

lemma take_take [simp]: "take n (take m xs) = take (min n m) xs"
proof (induct m arbitrary: xs n)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs; cases n) simp_all
qed

lemma drop_drop [simp]: "drop n (drop m xs) = drop (n + m) xs"
proof (induct m arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed

lemma take_drop: "take n (drop m xs) = drop m (take (n + m) xs)"
proof (induct m arbitrary: xs n)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs; cases n) simp_all
qed

lemma drop_take: "drop n (take m xs) = take (m-n) (drop n xs)"
  by(induct xs arbitrary: m n)(auto simp: take_Cons drop_Cons split: nat.split)

lemma append_take_drop_id [simp]: "take n xs @ drop n xs = xs"
proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed

lemma take_eq_Nil[simp]: "(take n xs = []) = (n = 0 \<or> xs = [])"
  by(induct xs arbitrary: n)(auto simp: take_Cons split:nat.split)

lemma drop_eq_Nil[simp]: "(drop n xs = []) = (length xs \<le> n)"
  by (induct xs arbitrary: n) (auto simp: drop_Cons split:nat.split)

lemma take_map: "take n (map f xs) = map f (take n xs)"
proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed

lemma drop_map: "drop n (map f xs) = map f (drop n xs)"
proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed

lemma rev_take: "rev (take i xs) = drop (length xs - i) (rev xs)"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases i) auto
qed

lemma rev_drop: "rev (drop i xs) = take (length xs - i) (rev xs)"
proof (induct xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases i) auto
qed

lemma drop_rev: "drop n (rev xs) = rev (take (length xs - n) xs)"
  by (cases "length xs < n") (auto simp: rev_take)

lemma take_rev: "take n (rev xs) = rev (drop (length xs - n) xs)"
  by (cases "length xs < n") (auto simp: rev_drop)

lemma nth_take [simp]: "i < n \<Longrightarrow> (take n xs)!i = xs!i"
proof (induct xs arbitrary: i n)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases n; cases i) simp_all
qed

lemma nth_drop [simp]:
  "n \<le> length xs \<Longrightarrow> (drop n xs)!i = xs!(n + i)"
proof (induct n arbitrary: xs)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs) simp_all
qed

lemma butlast_take:
  "n \<le> length xs \<Longrightarrow> butlast (take n xs) = take (n - 1) xs"
  by (simp add: butlast_conv_take min.absorb1 min.absorb2)

lemma butlast_drop: "butlast (drop n xs) = drop n (butlast xs)"
  by (simp add: butlast_conv_take drop_take ac_simps)

lemma take_butlast: "n < length xs \<Longrightarrow> take n (butlast xs) = take n xs"
  by (simp add: butlast_conv_take min.absorb1)

lemma drop_butlast: "drop n (butlast xs) = butlast (drop n xs)"
  by (simp add: butlast_conv_take drop_take ac_simps)

lemma butlast_power: "(butlast ^^ n) xs = take (length xs - n) xs"
  by (induct n) (auto simp: butlast_take)

lemma hd_drop_conv_nth: "n < length xs \<Longrightarrow> hd(drop n xs) = xs!n"
  by(simp add: hd_conv_nth)

lemma set_take_subset_set_take:
  "m \<le> n \<Longrightarrow> set(take m xs) \<le> set(take n xs)"
proof (induct xs arbitrary: m n)
  case (Cons x xs m n) then show ?case
    by (cases n) (auto simp: take_Cons)
qed simp

lemma set_take_subset: "set(take n xs) \<subseteq> set xs"
  by(induct xs arbitrary: n)(auto simp:take_Cons split:nat.split)

lemma set_drop_subset: "set(drop n xs) \<subseteq> set xs"
  by(induct xs arbitrary: n)(auto simp:drop_Cons split:nat.split)

lemma set_drop_subset_set_drop:
  "m \<ge> n \<Longrightarrow> set(drop m xs) \<le> set(drop n xs)"
proof (induct xs arbitrary: m n)
  case (Cons x xs m n)
  then show ?case
    by (clarsimp simp: drop_Cons split: nat.split) (metis set_drop_subset subset_iff)
qed simp

lemma in_set_takeD: "x \<in> set(take n xs) \<Longrightarrow> x \<in> set xs"
  using set_take_subset by fast

lemma in_set_dropD: "x \<in> set(drop n xs) \<Longrightarrow> x \<in> set xs"
  using set_drop_subset by fast

lemma append_eq_conv_conj:
  "(xs @ ys = zs) = (xs = take (length xs) zs \<and> ys = drop (length xs) zs)"
proof (induct xs arbitrary: zs)
  case (Cons x xs zs) then show ?case
    by (cases zs, auto)
qed auto

lemma map_eq_append_conv:
  "map f xs = ys @ zs \<longleftrightarrow> (\<exists>us vs. xs = us @ vs \<and> ys = map f us \<and> zs = map f vs)"
proof -
  have "map f xs \<noteq> ys @ zs \<and> map f xs \<noteq> ys @ zs \<or> map f xs \<noteq> ys @ zs \<or> map f xs = ys @ zs \<and>
    (\<exists>bs bsa. xs = bs @ bsa \<and> ys = map f bs \<and> zs = map f bsa)"
    by (metis append_eq_conv_conj append_take_drop_id drop_map take_map)
  then show ?thesis
    using map_append by blast
qed

lemma append_eq_map_conv:
  "ys @ zs = map f xs \<longleftrightarrow> (\<exists>us vs. xs = us @ vs \<and> ys = map f us \<and> zs = map f vs)"
by (metis map_eq_append_conv)

lemma take_add:  "take (i+j) xs = take i xs @ take j (drop i xs)"
proof (induct xs arbitrary: i)
  case (Cons x xs i) then show ?case
    by (cases i, auto)
qed auto

lemma append_eq_append_conv_if:
  "(xs\<^sub>1 @ xs\<^sub>2 = ys\<^sub>1 @ ys\<^sub>2) =
  (if size xs\<^sub>1 \<le> size ys\<^sub>1
   then xs\<^sub>1 = take (size xs\<^sub>1) ys\<^sub>1 \<and> xs\<^sub>2 = drop (size xs\<^sub>1) ys\<^sub>1 @ ys\<^sub>2
   else take (size ys\<^sub>1) xs\<^sub>1 = ys\<^sub>1 \<and> drop (size ys\<^sub>1) xs\<^sub>1 @ xs\<^sub>2 = ys\<^sub>2)"
proof (induct xs\<^sub>1 arbitrary: ys\<^sub>1)
  case (Cons a xs\<^sub>1 ys\<^sub>1) then show ?case
    by (cases ys\<^sub>1, auto)
qed auto

lemma take_hd_drop:
  "n < length xs \<Longrightarrow> take n xs @ [hd (drop n xs)] = take (Suc n) xs"
  by (induct xs arbitrary: n) (simp_all add:drop_Cons split:nat.split)

lemma id_take_nth_drop:
  "i < length xs \<Longrightarrow> xs = take i xs @ xs!i # drop (Suc i) xs"
proof -
  assume si: "i < length xs"
  hence "xs = take (Suc i) xs @ drop (Suc i) xs" by auto
  moreover
  from si have "take (Suc i) xs = take i xs @ [xs!i]"
    using take_Suc_conv_app_nth by blast
  ultimately show ?thesis by auto
qed

lemma take_update_cancel[simp]: "n \<le> m \<Longrightarrow> take n (xs[m := y]) = take n xs"
  by(simp add: list_eq_iff_nth_eq)

lemma drop_update_cancel[simp]: "n < m \<Longrightarrow> drop m (xs[n := x]) = drop m xs"
  by(simp add: list_eq_iff_nth_eq)

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

lemma take_update_swap: "take m (xs[n := x]) = (take m xs)[n := x]"
proof (cases "n \<ge> length xs")
  case False
  then show ?thesis
    by (simp add: upd_conv_take_nth_drop take_Cons drop_take min_def diff_Suc split: nat.split)
qed auto

lemma drop_update_swap:
  assumes "m \<le> n" shows "drop m (xs[n := x]) = (drop m xs)[n-m := x]"
proof (cases "n \<ge> length xs")
  case False
  with assms show ?thesis
    by (simp add: upd_conv_take_nth_drop drop_take)
qed auto

lemma nth_image: "l \<le> size xs \<Longrightarrow> nth xs ` {0..<l} = set(take l xs)"
  by(auto simp: set_conv_nth image_def) (metis Suc_le_eq nth_take order_trans)


subsubsection \<open>\<^const>\<open>takeWhile\<close> and \<^const>\<open>dropWhile\<close>\<close>

lemma length_takeWhile_le: "length (takeWhile P xs) \<le> length xs"
  by (induct xs) auto

lemma takeWhile_dropWhile_id [simp]: "takeWhile P xs @ dropWhile P xs = xs"
  by (induct xs) auto

lemma takeWhile_append1 [simp]:
  "\<lbrakk>x \<in> set xs; \<not>P(x)\<rbrakk> \<Longrightarrow> takeWhile P (xs @ ys) = takeWhile P xs"
  by (induct xs) auto

lemma takeWhile_append2 [simp]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> takeWhile P (xs @ ys) = xs @ takeWhile P ys"
  by (induct xs) auto

lemma takeWhile_append:
  "takeWhile P (xs @ ys) = (if \<forall>x\<in>set xs. P x then xs @ takeWhile P ys else takeWhile P xs)"
using takeWhile_append1[of _ xs P ys] takeWhile_append2[of xs P ys] by auto

lemma takeWhile_tail: "\<not> P x \<Longrightarrow> takeWhile P (xs @ (x#l)) = takeWhile P xs"
  by (induct xs) auto

lemma takeWhile_eq_Nil_iff: "takeWhile P xs = [] \<longleftrightarrow> xs = [] \<or> \<not>P (hd xs)"
by (cases xs) auto

lemma takeWhile_nth: "j < length (takeWhile P xs) \<Longrightarrow> takeWhile P xs ! j = xs ! j"
  by (metis nth_append takeWhile_dropWhile_id)

lemma dropWhile_nth: "j < length (dropWhile P xs) \<Longrightarrow>
  dropWhile P xs ! j = xs ! (j + length (takeWhile P xs))"
  by (metis add.commute nth_append_length_plus takeWhile_dropWhile_id)

lemma length_dropWhile_le: "length (dropWhile P xs) \<le> length xs"
  by (induct xs) auto

lemma dropWhile_append1 [simp]:
  "\<lbrakk>x \<in> set xs; \<not>P(x)\<rbrakk> \<Longrightarrow> dropWhile P (xs @ ys) = (dropWhile P xs)@ys"
  by (induct xs) auto

lemma dropWhile_append2 [simp]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P(x)) \<Longrightarrow> dropWhile P (xs @ ys) = dropWhile P ys"
  by (induct xs) auto

lemma dropWhile_append3:
  "\<not> P y \<Longrightarrow>dropWhile P (xs @ y # ys) = dropWhile P xs @ y # ys"
  by (induct xs) auto

lemma dropWhile_append:
  "dropWhile P (xs @ ys) = (if \<forall>x\<in>set xs. P x then dropWhile P ys else dropWhile P xs @ ys)"
using dropWhile_append1[of _ xs P ys] dropWhile_append2[of xs P ys] by auto

lemma dropWhile_last:
  "x \<in> set xs \<Longrightarrow> \<not> P x \<Longrightarrow> last (dropWhile P xs) = last xs"
  by (auto simp add: dropWhile_append3 in_set_conv_decomp)

lemma set_dropWhileD: "x \<in> set (dropWhile P xs) \<Longrightarrow> x \<in> set xs"
  by (induct xs) (auto split: if_split_asm)

lemma set_takeWhileD: "x \<in> set (takeWhile P xs) \<Longrightarrow> x \<in> set xs \<and> P x"
  by (induct xs) (auto split: if_split_asm)

lemma takeWhile_eq_all_conv[simp]:
  "(takeWhile P xs = xs) = (\<forall>x \<in> set xs. P x)"
  by(induct xs, auto)

lemma dropWhile_eq_Nil_conv[simp]:
  "(dropWhile P xs = []) = (\<forall>x \<in> set xs. P x)"
  by(induct xs, auto)

lemma dropWhile_eq_Cons_conv:
  "(dropWhile P xs = y#ys) = (xs = takeWhile P xs @ y # ys \<and> \<not> P y)"
  by(induct xs, auto)

lemma dropWhile_eq_self_iff: "dropWhile P xs = xs \<longleftrightarrow> xs = [] \<or> \<not>P (hd xs)"
by (cases xs) (auto simp: dropWhile_eq_Cons_conv)

lemma distinct_takeWhile[simp]: "distinct xs \<Longrightarrow> distinct (takeWhile P xs)"
  by (induct xs) (auto dest: set_takeWhileD)

lemma distinct_dropWhile[simp]: "distinct xs \<Longrightarrow> distinct (dropWhile P xs)"
  by (induct xs) auto

lemma takeWhile_map: "takeWhile P (map f xs) = map f (takeWhile (P \<circ> f) xs)"
  by (induct xs) auto

lemma dropWhile_map: "dropWhile P (map f xs) = map f (dropWhile (P \<circ> f) xs)"
  by (induct xs) auto

lemma takeWhile_eq_take: "takeWhile P xs = take (length (takeWhile P xs)) xs"
  by (induct xs) auto

lemma dropWhile_eq_drop: "dropWhile P xs = drop (length (takeWhile P xs)) xs"
  by (induct xs) auto

lemma hd_dropWhile: "dropWhile P xs \<noteq> [] \<Longrightarrow> \<not> P (hd (dropWhile P xs))"
  by (induct xs) auto

lemma takeWhile_eq_filter:
  assumes "\<And> x. x \<in> set (dropWhile P xs) \<Longrightarrow> \<not> P x"
  shows "takeWhile P xs = filter P xs"
proof -
  have A: "filter P xs = filter P (takeWhile P xs @ dropWhile P xs)"
    by simp
  have B: "filter P (dropWhile P xs) = []"
    unfolding filter_empty_conv using assms by blast
  have "filter P xs = takeWhile P xs"
    unfolding A filter_append B
    by (auto simp add: filter_id_conv dest: set_takeWhileD)
  thus ?thesis ..
qed

lemma takeWhile_eq_take_P_nth:
  "\<lbrakk> \<And> i. \<lbrakk> i < n ; i < length xs \<rbrakk> \<Longrightarrow> P (xs ! i) ; n < length xs \<Longrightarrow> \<not> P (xs ! n) \<rbrakk> \<Longrightarrow>
  takeWhile P xs = take n xs"
proof (induct xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases n)
    case 0
    with Cons show ?thesis by simp
  next
    case [simp]: (Suc n')
    have "P x" using Cons.prems(1)[of 0] by simp
    moreover have "takeWhile P xs = take n' xs"
    proof (rule Cons.hyps)
      fix i
      assume "i < n'" "i < length xs"
      thus "P (xs ! i)" using Cons.prems(1)[of "Suc i"] by simp
    next
      assume "n' < length xs"
      thus "\<not> P (xs ! n')" using Cons by auto
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma nth_length_takeWhile:
  "length (takeWhile P xs) < length xs \<Longrightarrow> \<not> P (xs ! length (takeWhile P xs))"
  by (induct xs) auto

lemma length_takeWhile_less_P_nth:
  assumes all: "\<And> i. i < j \<Longrightarrow> P (xs ! i)" and "j \<le> length xs"
  shows "j \<le> length (takeWhile P xs)"
proof (rule classical)
  assume "\<not> ?thesis"
  hence "length (takeWhile P xs) < length xs" using assms by simp
  thus ?thesis using all \<open>\<not> ?thesis\<close> nth_length_takeWhile[of P xs] by auto
qed

lemma takeWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  takeWhile (\<lambda>y. y \<noteq> x) (rev xs) = rev (tl (dropWhile (\<lambda>y. y \<noteq> x) xs))"
  by(induct xs) (auto simp: takeWhile_tail[where l="[]"])

lemma dropWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  dropWhile (\<lambda>y. y \<noteq> x) (rev xs) = x # rev (takeWhile (\<lambda>y. y \<noteq> x) xs)"
proof (induct xs)
  case (Cons a xs)
  then show ?case
    by(auto, subst dropWhile_append2, auto)
qed simp

lemma takeWhile_not_last:
  "distinct xs \<Longrightarrow> takeWhile (\<lambda>y. y \<noteq> last xs) xs = butlast xs"
  by(induction xs rule: induct_list012) auto

lemma takeWhile_cong [fundef_cong]:
  "\<lbrakk>l = k; \<And>x. x \<in> set l \<Longrightarrow> P x = Q x\<rbrakk>
  \<Longrightarrow> takeWhile P l = takeWhile Q k"
  by (induct k arbitrary: l) (simp_all)

lemma dropWhile_cong [fundef_cong]:
  "\<lbrakk>l = k; \<And>x. x \<in> set l \<Longrightarrow> P x = Q x\<rbrakk>
  \<Longrightarrow> dropWhile P l = dropWhile Q k"
  by (induct k arbitrary: l, simp_all)

lemma takeWhile_idem [simp]:
  "takeWhile P (takeWhile P xs) = takeWhile P xs"
  by (induct xs) auto

lemma dropWhile_idem [simp]:
  "dropWhile P (dropWhile P xs) = dropWhile P xs"
  by (induct xs) auto


subsubsection \<open>\<^const>\<open>zip\<close>\<close>

lemma zip_Nil [simp]: "zip [] ys = []"
  by (induct ys) auto

lemma zip_Cons_Cons [simp]: "zip (x # xs) (y # ys) = (x, y) # zip xs ys"
  by simp

declare zip_Cons [simp del]

lemma [code]:
  "zip [] ys = []"
  "zip xs [] = []"
  "zip (x # xs) (y # ys) = (x, y) # zip xs ys"
  by (fact zip_Nil zip.simps(1) zip_Cons_Cons)+

lemma zip_Cons1:
  "zip (x#xs) ys = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (x,y)#zip xs ys)"
  by(auto split:list.split)

lemma length_zip [simp]:
  "length (zip xs ys) = min (length xs) (length ys)"
  by (induct xs ys rule:list_induct2') auto

lemma zip_obtain_same_length:
  assumes "\<And>zs ws n. length zs = length ws \<Longrightarrow> n = min (length xs) (length ys)
    \<Longrightarrow> zs = take n xs \<Longrightarrow> ws = take n ys \<Longrightarrow> P (zip zs ws)"
  shows "P (zip xs ys)"
proof -
  let ?n = "min (length xs) (length ys)"
  have "P (zip (take ?n xs) (take ?n ys))"
    by (rule assms) simp_all
  moreover have "zip xs ys = zip (take ?n xs) (take ?n ys)"
  proof (induct xs arbitrary: ys)
    case Nil then show ?case by simp
  next
    case (Cons x xs) then show ?case by (cases ys) simp_all
  qed
  ultimately show ?thesis by simp
qed

lemma zip_append1:
  "zip (xs @ ys) zs =
  zip xs (take (length xs) zs) @ zip ys (drop (length xs) zs)"
  by (induct xs zs rule:list_induct2') auto

lemma zip_append2:
  "zip xs (ys @ zs) =
  zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs"
  by (induct xs ys rule:list_induct2') auto

lemma zip_append [simp]:
  "\<lbrakk>length xs = length us\<rbrakk> \<Longrightarrow>
  zip (xs@ys) (us@vs) = zip xs us @ zip ys vs"
  by (simp add: zip_append1)

lemma zip_rev:
  "length xs = length ys \<Longrightarrow> zip (rev xs) (rev ys) = rev (zip xs ys)"
  by (induct rule:list_induct2, simp_all)

lemma zip_map_map:
  "zip (map f xs) (map g ys) = map (\<lambda> (x, y). (f x, g y)) (zip xs ys)"
proof (induct xs arbitrary: ys)
  case (Cons x xs) note Cons_x_xs = Cons.hyps
  show ?case
  proof (cases ys)
    case (Cons y ys')
    show ?thesis unfolding Cons using Cons_x_xs by simp
  qed simp
qed simp

lemma zip_map1:
  "zip (map f xs) ys = map (\<lambda>(x, y). (f x, y)) (zip xs ys)"
  using zip_map_map[of f xs "\<lambda>x. x" ys] by simp

lemma zip_map2:
  "zip xs (map f ys) = map (\<lambda>(x, y). (x, f y)) (zip xs ys)"
  using zip_map_map[of "\<lambda>x. x" xs f ys] by simp

lemma map_zip_map:
  "map f (zip (map g xs) ys) = map (%(x,y). f(g x, y)) (zip xs ys)"
  by (auto simp: zip_map1)

lemma map_zip_map2:
  "map f (zip xs (map g ys)) = map (%(x,y). f(x, g y)) (zip xs ys)"
  by (auto simp: zip_map2)

text\<open>Courtesy of Andreas Lochbihler:\<close>
lemma zip_same_conv_map: "zip xs xs = map (\<lambda>x. (x, x)) xs"
  by(induct xs) auto

lemma nth_zip [simp]:
  "\<lbrakk>i < length xs; i < length ys\<rbrakk> \<Longrightarrow> (zip xs ys)!i = (xs!i, ys!i)"
proof (induct ys arbitrary: i xs)
  case (Cons y ys)
  then show ?case
    by (cases xs) (simp_all add: nth.simps split: nat.split)
qed auto

lemma set_zip:
  "set (zip xs ys) = {(xs!i, ys!i) | i. i < min (length xs) (length ys)}"
  by(simp add: set_conv_nth cong: rev_conj_cong)

lemma zip_same: "((a,b) \<in> set (zip xs xs)) = (a \<in> set xs \<and> a = b)"
  by(induct xs) auto

lemma zip_update: "zip (xs[i:=x]) (ys[i:=y]) = (zip xs ys)[i:=(x,y)]"
  by (simp add: update_zip)

lemma zip_replicate [simp]:
  "zip (replicate i x) (replicate j y) = replicate (min i j) (x,y)"
proof (induct i arbitrary: j)
  case (Suc i)
  then show ?case
    by (cases j, auto)
qed auto

lemma zip_replicate1: "zip (replicate n x) ys = map (Pair x) (take n ys)"
  by(induction ys arbitrary: n)(case_tac [2] n, simp_all)

lemma take_zip: "take n (zip xs ys) = zip (take n xs) (take n ys)"
proof (induct n arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs; cases ys) simp_all
qed

lemma drop_zip: "drop n (zip xs ys) = zip (drop n xs) (drop n ys)"
proof (induct n arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by (cases xs; cases ys) simp_all
qed

lemma zip_takeWhile_fst: "zip (takeWhile P xs) ys = takeWhile (P \<circ> fst) (zip xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases ys) auto
qed

lemma zip_takeWhile_snd: "zip xs (takeWhile P ys) = takeWhile (P \<circ> snd) (zip xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (cases ys) auto
qed

lemma set_zip_leftD: "(x,y)\<in> set (zip xs ys) \<Longrightarrow> x \<in> set xs"
  by (induct xs ys rule:list_induct2') auto

lemma set_zip_rightD: "(x,y)\<in> set (zip xs ys) \<Longrightarrow> y \<in> set ys"
  by (induct xs ys rule:list_induct2') auto

lemma in_set_zipE:
  "(x,y) \<in> set(zip xs ys) \<Longrightarrow> (\<lbrakk> x \<in> set xs; y \<in> set ys \<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  by(blast dest: set_zip_leftD set_zip_rightD)

lemma zip_map_fst_snd: "zip (map fst zs) (map snd zs) = zs"
  by (induct zs) simp_all

lemma zip_eq_conv:
  "length xs = length ys \<Longrightarrow> zip xs ys = zs \<longleftrightarrow> map fst zs = xs \<and> map snd zs = ys"
  by (auto simp add: zip_map_fst_snd)

lemma in_set_zip:
  "p \<in> set (zip xs ys) \<longleftrightarrow> (\<exists>n. xs ! n = fst p \<and> ys ! n = snd p
  \<and> n < length xs \<and> n < length ys)"
  by (cases p) (auto simp add: set_zip)

lemma in_set_impl_in_set_zip1:
  assumes "length xs = length ys"
  assumes "x \<in> set xs"
  obtains y where "(x, y) \<in> set (zip xs ys)"
proof -
  from assms have "x \<in> set (map fst (zip xs ys))" by simp
  from this that show ?thesis by fastforce
qed

lemma in_set_impl_in_set_zip2:
  assumes "length xs = length ys"
  assumes "y \<in> set ys"
  obtains x where "(x, y) \<in> set (zip xs ys)"
proof -
  from assms have "y \<in> set (map snd (zip xs ys))" by simp
  from this that show ?thesis by fastforce
qed

lemma zip_eq_Nil_iff:
  "zip xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
  by (cases xs; cases ys) simp_all

lemma zip_eq_ConsE:
  assumes "zip xs ys = xy # xys"
  obtains x xs' y ys' where "xs = x # xs'"
    and "ys = y # ys'" and "xy = (x, y)"
    and "xys = zip xs' ys'"
proof -
  from assms have "xs \<noteq> []" and "ys \<noteq> []"
    using zip_eq_Nil_iff [of xs ys] by simp_all
  then obtain x xs' y ys'  where xs: "xs = x # xs'"
    and ys: "ys = y # ys'"
    by (cases xs; cases ys) auto
  with assms have "xy = (x, y)" and "xys = zip xs' ys'"
    by simp_all
  with xs ys show ?thesis ..
qed

lemma semilattice_map2:
  "semilattice (map2 (\<^bold>*))" if "semilattice (\<^bold>*)"
    for f (infixl "\<^bold>*" 70)
proof -
  from that interpret semilattice f .
  show ?thesis
  proof
    show "map2 (\<^bold>*) (map2 (\<^bold>*) xs ys) zs = map2 (\<^bold>*) xs (map2 (\<^bold>*) ys zs)"
      for xs ys zs :: "'a list"
    proof (induction "zip xs (zip ys zs)" arbitrary: xs ys zs)
      case Nil
      from Nil [symmetric] show ?case
        by (auto simp add: zip_eq_Nil_iff)
    next
      case (Cons xyz xyzs)
      from Cons.hyps(2) [symmetric] show ?case
        by (rule zip_eq_ConsE) (erule zip_eq_ConsE,
          auto intro: Cons.hyps(1) simp add: ac_simps)
    qed
    show "map2 (\<^bold>*) xs ys = map2 (\<^bold>*) ys xs"
      for xs ys :: "'a list"
    proof (induction "zip xs ys" arbitrary: xs ys)
      case Nil
      then show ?case
        by (auto simp add: zip_eq_Nil_iff dest: sym)
    next
      case (Cons xy xys)
      from Cons.hyps(2) [symmetric] show ?case
        by (rule zip_eq_ConsE) (auto intro: Cons.hyps(1) simp add: ac_simps)
    qed
    show "map2 (\<^bold>*) xs xs = xs"
      for xs :: "'a list"
      by (induction xs) simp_all
  qed
qed

lemma pair_list_eqI:
  assumes "map fst xs = map fst ys" and "map snd xs = map snd ys"
  shows "xs = ys"
proof -
  from assms(1) have "length xs = length ys" by (rule map_eq_imp_length_eq)
  from this assms show ?thesis
    by (induct xs ys rule: list_induct2) (simp_all add: prod_eqI)
qed

lemma hd_zip:
  \<open>hd (zip xs ys) = (hd xs, hd ys)\<close> if \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
  using that by (cases xs; cases ys) simp_all

lemma last_zip:
  \<open>last (zip xs ys) = (last xs, last ys)\<close> if \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
    and \<open>length xs = length ys\<close>
  using that by (cases xs rule: rev_cases; cases ys rule: rev_cases) simp_all


subsubsection \<open>\<^const>\<open>list_all2\<close>\<close>

lemma list_all2_lengthD [intro?]:
  "list_all2 P xs ys \<Longrightarrow> length xs = length ys"
  by (simp add: list_all2_iff)

lemma list_all2_Nil [iff, code]: "list_all2 P [] ys = (ys = [])"
  by (simp add: list_all2_iff)

lemma list_all2_Nil2 [iff, code]: "list_all2 P xs [] = (xs = [])"
  by (simp add: list_all2_iff)

lemma list_all2_Cons [iff, code]:
  "list_all2 P (x # xs) (y # ys) = (P x y \<and> list_all2 P xs ys)"
  by (auto simp add: list_all2_iff)

lemma list_all2_Cons1:
  "list_all2 P (x # xs) ys = (\<exists>z zs. ys = z # zs \<and> P x z \<and> list_all2 P xs zs)"
  by (cases ys) auto

lemma list_all2_Cons2:
  "list_all2 P xs (y # ys) = (\<exists>z zs. xs = z # zs \<and> P z y \<and> list_all2 P zs ys)"
  by (cases xs) auto

lemma list_all2_induct
  [consumes 1, case_names Nil Cons, induct set: list_all2]:
  assumes P: "list_all2 P xs ys"
  assumes Nil: "R [] []"
  assumes Cons: "\<And>x xs y ys.
    \<lbrakk>P x y; list_all2 P xs ys; R xs ys\<rbrakk> \<Longrightarrow> R (x # xs) (y # ys)"
  shows "R xs ys"
  using P
  by (induct xs arbitrary: ys) (auto simp add: list_all2_Cons1 Nil Cons)

lemma list_all2_rev [iff]:
  "list_all2 P (rev xs) (rev ys) = list_all2 P xs ys"
  by (simp add: list_all2_iff zip_rev cong: conj_cong)

lemma list_all2_rev1:
  "list_all2 P (rev xs) ys = list_all2 P xs (rev ys)"
  by (subst list_all2_rev [symmetric]) simp

lemma list_all2_append1:
  "list_all2 P (xs @ ys) zs =
  (\<exists>us vs. zs = us @ vs \<and> length us = length xs \<and> length vs = length ys \<and>
    list_all2 P xs us \<and> list_all2 P ys vs)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (rule_tac x = "take (length xs) zs" in exI)
    apply (rule_tac x = "drop (length xs) zs" in exI)
    apply (force split: nat_diff_split simp add: list_all2_iff zip_append1)
    done
next
  assume ?rhs
  then show ?lhs
    by (auto simp add: list_all2_iff)
qed

lemma list_all2_append2:
  "list_all2 P xs (ys @ zs) =
  (\<exists>us vs. xs = us @ vs \<and> length us = length ys \<and> length vs = length zs \<and>
    list_all2 P us ys \<and> list_all2 P vs zs)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (rule_tac x = "take (length ys) xs" in exI)
    apply (rule_tac x = "drop (length ys) xs" in exI)
    apply (force split: nat_diff_split simp add: list_all2_iff zip_append2)
    done
next
  assume ?rhs
  then show ?lhs
    by (auto simp add: list_all2_iff)
qed

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
  by (force simp add: list_all2_iff set_zip)

lemma list_all2_trans:
  assumes tr: "!!a b c. P1 a b \<Longrightarrow> P2 b c \<Longrightarrow> P3 a c"
  shows "!!bs cs. list_all2 P1 as bs \<Longrightarrow> list_all2 P2 bs cs \<Longrightarrow> list_all2 P3 as cs"
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
  "\<forall>x \<in> set (zip a b). case_prod P x \<Longrightarrow> length a = length b \<Longrightarrow> list_all2 P a b"
  by (simp add: list_all2_iff)

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
  "\<lbrakk> list_all2 P xs ys; P x y \<rbrakk> \<Longrightarrow> list_all2 P (xs[i:=x]) (ys[i:=y])"
  by (cases "i < length ys") (auto simp add: list_all2_conv_all_nth nth_list_update)

lemma list_all2_takeI [simp,intro?]:
  "list_all2 P xs ys \<Longrightarrow> list_all2 P (take n xs) (take n ys)"
proof (induct xs arbitrary: n ys)
  case (Cons x xs)
  then show ?case
    by (cases n) (auto simp: list_all2_Cons1)
qed auto

lemma list_all2_dropI [simp,intro?]:
  "list_all2 P xs ys \<Longrightarrow> list_all2 P (drop n xs) (drop n ys)"
proof (induct xs arbitrary: n ys)
  case (Cons x xs)
  then show ?case
    by (cases n) (auto simp: list_all2_Cons1)
qed auto

lemma list_all2_mono [intro?]:
  "list_all2 P xs ys \<Longrightarrow> (\<And>xs ys. P xs ys \<Longrightarrow> Q xs ys) \<Longrightarrow> list_all2 Q xs ys"
  by (rule list.rel_mono_strong)

lemma list_all2_eq:
  "xs = ys \<longleftrightarrow> list_all2 (=) xs ys"
  by (induct xs ys rule: list_induct2') auto

lemma list_eq_iff_zip_eq:
  "xs = ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>(x,y) \<in> set (zip xs ys). x = y)"
  by(auto simp add: set_zip list_all2_eq list_all2_conv_all_nth cong: conj_cong)

lemma list_all2_same: "list_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x x)"
  by(auto simp add: list_all2_conv_all_nth set_conv_nth)

lemma zip_assoc:
  "zip xs (zip ys zs) = map (\<lambda>((x, y), z). (x, y, z)) (zip (zip xs ys) zs)"
  by(rule list_all2_all_nthI[where P="(=)", unfolded list.rel_eq]) simp_all

lemma zip_commute: "zip xs ys = map (\<lambda>(x, y). (y, x)) (zip ys xs)"
  by(rule list_all2_all_nthI[where P="(=)", unfolded list.rel_eq]) simp_all

lemma zip_left_commute:
  "zip xs (zip ys zs) = map (\<lambda>(y, (x, z)). (x, y, z)) (zip ys (zip xs zs))"
  by(rule list_all2_all_nthI[where P="(=)", unfolded list.rel_eq]) simp_all

lemma zip_replicate2: "zip xs (replicate n y) = map (\<lambda>x. (x, y)) (take n xs)"
  by(subst zip_commute)(simp add: zip_replicate1)

subsubsection \<open>\<^const>\<open>List.product\<close> and \<^const>\<open>product_lists\<close>\<close>

lemma product_concat_map:
  "List.product xs ys = concat (map (\<lambda>x. map (\<lambda>y. (x,y)) ys) xs)"
  by(induction xs) (simp)+

lemma set_product[simp]: "set (List.product xs ys) = set xs \<times> set ys"
  by (induct xs) auto

lemma length_product [simp]:
  "length (List.product xs ys) = length xs * length ys"
  by (induct xs) simp_all

lemma product_nth:
  assumes "n < length xs * length ys"
  shows "List.product xs ys ! n = (xs ! (n div length ys), ys ! (n mod length ys))"
  using assms proof (induct xs arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons x xs n)
  then have "length ys > 0" by auto
  with Cons show ?case
    by (auto simp add: nth_append not_less le_mod_geq le_div_geq)
qed

lemma in_set_product_lists_length:
  "xs \<in> set (product_lists xss) \<Longrightarrow> length xs = length xss"
  by (induct xss arbitrary: xs) auto

lemma product_lists_set:
  "set (product_lists xss) = {xs. list_all2 (\<lambda>x ys. x \<in> set ys) xs xss}" (is "?L = Collect ?R")
proof (intro equalityI subsetI, unfold mem_Collect_eq)
  fix xs assume "xs \<in> ?L"
  then have "length xs = length xss" by (rule in_set_product_lists_length)
  from this \<open>xs \<in> ?L\<close> show "?R xs" by (induct xs xss rule: list_induct2) auto
next
  fix xs assume "?R xs"
  then show "xs \<in> ?L" by induct auto
qed


subsubsection \<open>\<^const>\<open>fold\<close> with natural argument order\<close>

lemma fold_simps [code]: \<comment> \<open>eta-expanded variant for generated code -- enables tail-recursion optimisation in Scala\<close>
  "fold f [] s = s"
  "fold f (x # xs) s = fold f xs (f x s)"
  by simp_all

lemma fold_remove1_split:
  "\<lbrakk> \<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f x \<circ> f y = f y \<circ> f x;
    x \<in> set xs \<rbrakk>
  \<Longrightarrow> fold f xs = fold f (remove1 x xs) \<circ> f x"
  by (induct xs) (auto simp add: comp_assoc)

lemma fold_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> fold f xs a = fold g ys b"
  by (induct ys arbitrary: a b xs) simp_all

lemma fold_id: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = id) \<Longrightarrow> fold f xs = id"
  by (induct xs) simp_all

lemma fold_commute:
  "(\<And>x. x \<in> set xs \<Longrightarrow> h \<circ> g x = f x \<circ> h) \<Longrightarrow> h \<circ> fold g xs = fold f xs \<circ> h"
  by (induct xs) (simp_all add: fun_eq_iff)

lemma fold_commute_apply:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> h \<circ> g x = f x \<circ> h"
  shows "h (fold g xs s) = fold f xs (h s)"
proof -
  from assms have "h \<circ> fold g xs = fold f xs \<circ> h" by (rule fold_commute)
  then show ?thesis by (simp add: fun_eq_iff)
qed

lemma fold_invariant:
  "\<lbrakk> \<And>x. x \<in> set xs \<Longrightarrow> Q x;  P s;  \<And>x s. Q x \<Longrightarrow> P s \<Longrightarrow> P (f x s) \<rbrakk>
  \<Longrightarrow> P (fold f xs s)"
  by (induct xs arbitrary: s) simp_all

lemma fold_append [simp]: "fold f (xs @ ys) = fold f ys \<circ> fold f xs"
  by (induct xs) simp_all

lemma fold_map [code_unfold]: "fold g (map f xs) = fold (g \<circ> f) xs"
  by (induct xs) simp_all

lemma fold_filter:
  "fold f (filter P xs) = fold (\<lambda>x. if P x then f x else id) xs"
  by (induct xs) simp_all

lemma fold_rev:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f y \<circ> f x = f x \<circ> f y)
  \<Longrightarrow> fold f (rev xs) = fold f xs"
  by (induct xs) (simp_all add: fold_commute_apply fun_eq_iff)

lemma fold_Cons_rev: "fold Cons xs = append (rev xs)"
  by (induct xs) simp_all

lemma rev_conv_fold [code]: "rev xs = fold Cons xs []"
  by (simp add: fold_Cons_rev)

lemma fold_append_concat_rev: "fold append xss = append (concat (rev xss))"
  by (induct xss) simp_all

text \<open>\<^const>\<open>Finite_Set.fold\<close> and \<^const>\<open>fold\<close>\<close>

lemma (in comp_fun_commute) fold_set_fold_remdups:
  "Finite_Set.fold f y (set xs) = fold f (remdups xs) y"
  by (rule sym, induct xs arbitrary: y) (simp_all add: fold_fun_left_comm insert_absorb)

lemma (in comp_fun_idem) fold_set_fold:
  "Finite_Set.fold f y (set xs) = fold f xs y"
  by (rule sym, induct xs arbitrary: y) (simp_all add: fold_fun_left_comm)

lemma union_set_fold [code]: "set xs \<union> A = fold Set.insert xs A"
proof -
  interpret comp_fun_idem Set.insert
    by (fact comp_fun_idem_insert)
  show ?thesis by (simp add: union_fold_insert fold_set_fold)
qed

lemma union_coset_filter [code]:
  "List.coset xs \<union> A = List.coset (List.filter (\<lambda>x. x \<notin> A) xs)"
  by auto

lemma minus_set_fold [code]: "A - set xs = fold Set.remove xs A"
proof -
  interpret comp_fun_idem Set.remove
    by (fact comp_fun_idem_remove)
  show ?thesis
    by (simp add: minus_fold_remove [of _ A] fold_set_fold)
qed

lemma minus_coset_filter [code]:
  "A - List.coset xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  by auto

lemma inter_set_filter [code]:
  "A \<inter> set xs = set (List.filter (\<lambda>x. x \<in> A) xs)"
  by auto

lemma inter_coset_fold [code]:
  "A \<inter> List.coset xs = fold Set.remove xs A"
  by (simp add: Diff_eq [symmetric] minus_set_fold)

lemma (in semilattice_set) set_eq_fold [code]:
  "F (set (x # xs)) = fold f xs x"
proof -
  interpret comp_fun_idem f
    by standard (simp_all add: fun_eq_iff left_commute)
  show ?thesis by (simp add: eq_fold fold_set_fold)
qed

lemma (in complete_lattice) Inf_set_fold:
  "Inf (set xs) = fold inf xs top"
proof -
  interpret comp_fun_idem "inf :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact comp_fun_idem_inf)
  show ?thesis by (simp add: Inf_fold_inf fold_set_fold inf_commute)
qed

declare Inf_set_fold [where 'a = "'a set", code]

lemma (in complete_lattice) Sup_set_fold:
  "Sup (set xs) = fold sup xs bot"
proof -
  interpret comp_fun_idem "sup :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    by (fact comp_fun_idem_sup)
  show ?thesis by (simp add: Sup_fold_sup fold_set_fold sup_commute)
qed

declare Sup_set_fold [where 'a = "'a set", code]

lemma (in complete_lattice) INF_set_fold:
  "\<Sqinter>(f ` set xs) = fold (inf \<circ> f) xs top"
  using Inf_set_fold [of "map f xs"] by (simp add: fold_map)

lemma (in complete_lattice) SUP_set_fold:
  "\<Squnion>(f ` set xs) = fold (sup \<circ> f) xs bot"
  using Sup_set_fold [of "map f xs"] by (simp add: fold_map)


subsubsection \<open>Fold variants: \<^const>\<open>foldr\<close> and \<^const>\<open>foldl\<close>\<close>

text \<open>Correspondence\<close>

lemma foldr_conv_fold [code_abbrev]: "foldr f xs = fold f (rev xs)"
  by (induct xs) simp_all

lemma foldl_conv_fold: "foldl f s xs = fold (\<lambda>x s. f s x) xs s"
  by (induct xs arbitrary: s) simp_all

lemma foldr_conv_foldl: \<comment> \<open>The ``Third Duality Theorem'' in Bird \& Wadler:\<close>
  "foldr f xs a = foldl (\<lambda>x y. f y x) a (rev xs)"
  by (simp add: foldr_conv_fold foldl_conv_fold)

lemma foldl_conv_foldr:
  "foldl f a xs = foldr (\<lambda>x y. f y x) (rev xs) a"
  by (simp add: foldr_conv_fold foldl_conv_fold)

lemma foldr_fold:
  "(\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> f y \<circ> f x = f x \<circ> f y)
  \<Longrightarrow> foldr f xs = fold f xs"
  unfolding foldr_conv_fold by (rule fold_rev)

lemma foldr_cong [fundef_cong]:
  "a = b \<Longrightarrow> l = k \<Longrightarrow> (\<And>a x. x \<in> set l \<Longrightarrow> f x a = g x a) \<Longrightarrow> foldr f l a = foldr g k b"
  by (auto simp add: foldr_conv_fold intro!: fold_cong)

lemma foldl_cong [fundef_cong]:
  "a = b \<Longrightarrow> l = k \<Longrightarrow> (\<And>a x. x \<in> set l \<Longrightarrow> f a x = g a x) \<Longrightarrow> foldl f a l = foldl g b k"
  by (auto simp add: foldl_conv_fold intro!: fold_cong)

lemma foldr_append [simp]: "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)"
  by (simp add: foldr_conv_fold)

lemma foldl_append [simp]: "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"
  by (simp add: foldl_conv_fold)

lemma foldr_map [code_unfold]: "foldr g (map f xs) a = foldr (g \<circ> f) xs a"
  by (simp add: foldr_conv_fold fold_map rev_map)

lemma foldr_filter:
  "foldr f (filter P xs) = foldr (\<lambda>x. if P x then f x else id) xs"
  by (simp add: foldr_conv_fold rev_filter fold_filter)

lemma foldl_map [code_unfold]:
  "foldl g a (map f xs) = foldl (\<lambda>a x. g a (f x)) a xs"
  by (simp add: foldl_conv_fold fold_map comp_def)

lemma concat_conv_foldr [code]:
  "concat xss = foldr append xss []"
  by (simp add: fold_append_concat_rev foldr_conv_fold)


subsubsection \<open>\<^const>\<open>upt\<close>\<close>

lemma upt_rec[code]: "[i..<j] = (if i<j then i#[Suc i..<j] else [])"
  \<comment> \<open>simp does not terminate!\<close>
  by (induct j) auto

lemmas upt_rec_numeral[simp] = upt_rec[of "numeral m" "numeral n"] for m n

lemma upt_conv_Nil [simp]: "j \<le> i \<Longrightarrow> [i..<j] = []"
  by (subst upt_rec) simp

lemma upt_eq_Nil_conv[simp]: "([i..<j] = []) = (j = 0 \<or> j \<le> i)"
  by(induct j)simp_all

lemma upt_eq_Cons_conv:
  "([i..<j] = x#xs) = (i < j \<and> i = x \<and> [i+1..<j] = xs)"
proof (induct j arbitrary: x xs)
  case (Suc j)
  then show ?case
    by (simp add: upt_rec)
qed simp

lemma upt_Suc_append: "i \<le> j \<Longrightarrow> [i..<(Suc j)] = [i..<j]@[j]"
  \<comment> \<open>Only needed if \<open>upt_Suc\<close> is deleted from the simpset.\<close>
  by simp

lemma upt_conv_Cons: "i < j \<Longrightarrow> [i..<j] = i # [Suc i..<j]"
  by (simp add: upt_rec)

lemma upt_conv_Cons_Cons: \<comment> \<open>no precondition\<close>
  "m # n # ns = [m..<q] \<longleftrightarrow> n # ns = [Suc m..<q]"
proof (cases "m < q")
  case False then show ?thesis by simp
next
  case True then show ?thesis by (simp add: upt_conv_Cons)
qed

lemma upt_add_eq_append: "i<=j \<Longrightarrow> [i..<j+k] = [i..<j]@[j..<j+k]"
  \<comment> \<open>LOOPS as a simprule, since \<open>j \<le> j\<close>.\<close>
  by (induct k) auto

lemma length_upt [simp]: "length [i..<j] = j - i"
  by (induct j) (auto simp add: Suc_diff_le)

lemma nth_upt [simp]: "i + k < j \<Longrightarrow> [i..<j] ! k = i + k"
  by (induct j) (auto simp add: less_Suc_eq nth_append split: nat_diff_split)

lemma hd_upt[simp]: "i < j \<Longrightarrow> hd[i..<j] = i"
  by(simp add:upt_conv_Cons)

lemma tl_upt [simp]: "tl [m..<n] = [Suc m..<n]"
  by (simp add: upt_rec)

lemma last_upt[simp]: "i < j \<Longrightarrow> last[i..<j] = j - 1"
  by(cases j)(auto simp: upt_Suc_append)

lemma take_upt [simp]: "i+m \<le> n \<Longrightarrow> take m [i..<n] = [i..<i+m]"
proof (induct m arbitrary: i)
  case (Suc m)
  then show ?case
    by (subst take_Suc_conv_app_nth) auto
qed simp

lemma drop_upt[simp]: "drop m [i..<j] = [i+m..<j]"
  by(induct j) auto

lemma map_Suc_upt: "map Suc [m..<n] = [Suc m..<Suc n]"
  by (induct n) auto

lemma map_add_upt: "map (\<lambda>i. i + n) [0..<m] = [n..<m + n]"
  by (induct m) simp_all

lemma nth_map_upt: "i < n-m \<Longrightarrow> (map f [m..<n]) ! i = f(m+i)"
proof (induct n m  arbitrary: i rule: diff_induct)
  case (3 x y)
  then show ?case
    by (metis add.commute length_upt less_diff_conv nth_map nth_upt)
qed auto

lemma map_decr_upt: "map (\<lambda>n. n - Suc 0) [Suc m..<Suc n] = [m..<n]"
  by (induct n) simp_all

lemma map_upt_Suc: "map f [0 ..< Suc n] = f 0 # map (\<lambda>i. f (Suc i)) [0 ..< n]"
  by (induct n arbitrary: f) auto

lemma nth_take_lemma:
  "k \<le> length xs \<Longrightarrow> k \<le> length ys \<Longrightarrow>
     (\<And>i. i < k \<longrightarrow> xs!i = ys!i) \<Longrightarrow> take k xs = take k ys"
proof (induct k arbitrary: xs ys)
  case (Suc k)
  then show ?case
    apply (simp add: less_Suc_eq_0_disj)
    by (simp add: Suc.prems(3) take_Suc_conv_app_nth)
qed simp

lemma nth_equalityI:
  "\<lbrakk>length xs = length ys; \<And>i. i < length xs \<Longrightarrow> xs!i = ys!i\<rbrakk> \<Longrightarrow> xs = ys"
  by (frule nth_take_lemma [OF le_refl eq_imp_le]) simp_all

lemma map_nth:
  "map (\<lambda>i. xs ! i) [0..<length xs] = xs"
  by (rule nth_equalityI, auto)

lemma list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>P x y; Q y x\<rbrakk> \<Longrightarrow> x = y); list_all2 P xs ys; list_all2 Q ys xs \<rbrakk>
  \<Longrightarrow> xs = ys"
  by (simp add: list_all2_conv_all_nth nth_equalityI)

lemma take_equalityI: "(\<forall>i. take i xs = take i ys) \<Longrightarrow> xs = ys"
\<comment> \<open>The famous take-lemma.\<close>
  by (metis length_take min.commute order_refl take_all)

lemma take_Cons':
  "take n (x # xs) = (if n = 0 then [] else x # take (n - 1) xs)"
by (cases n) simp_all

lemma drop_Cons':
  "drop n (x # xs) = (if n = 0 then x # xs else drop (n - 1) xs)"
by (cases n) simp_all

lemma nth_Cons': "(x # xs)!n = (if n = 0 then x else xs!(n - 1))"
by (cases n) simp_all

lemma take_Cons_numeral [simp]:
  "take (numeral v) (x # xs) = x # take (numeral v - 1) xs"
by (simp add: take_Cons')

lemma drop_Cons_numeral [simp]:
  "drop (numeral v) (x # xs) = drop (numeral v - 1) xs"
by (simp add: drop_Cons')

lemma nth_Cons_numeral [simp]:
  "(x # xs) ! numeral v = xs ! (numeral v - 1)"
  by (simp add: nth_Cons')

lemma map_upt_eqI:
  \<open>map f [m..<n] = xs\<close> if \<open>length xs = n - m\<close>
    \<open>\<And>i. i < length xs \<Longrightarrow> xs ! i = f (m + i)\<close>
proof (rule nth_equalityI)
  from \<open>length xs = n - m\<close> show \<open>length (map f [m..<n]) = length xs\<close>
    by simp
next
  fix i
  assume \<open>i < length (map f [m..<n])\<close>
  then have \<open>i < n - m\<close>
    by simp
  with that have \<open>xs ! i = f (m + i)\<close>
    by simp
  with \<open>i < n - m\<close> show \<open>map f [m..<n] ! i = xs ! i\<close>
    by simp
qed


subsubsection \<open>\<open>upto\<close>: interval-list on \<^typ>\<open>int\<close>\<close>

function upto :: "int \<Rightarrow> int \<Rightarrow> int list" ("(1[_../_])") where
  "upto i j = (if i \<le> j then i # [i+1..j] else [])"
by auto
termination
by(relation "measure(%(i::int,j). nat(j - i + 1))") auto

declare upto.simps[simp del]

lemmas upto_rec_numeral [simp] =
  upto.simps[of "numeral m" "numeral n"]
  upto.simps[of "numeral m" "- numeral n"]
  upto.simps[of "- numeral m" "numeral n"]
  upto.simps[of "- numeral m" "- numeral n"] for m n

lemma upto_empty[simp]: "j < i \<Longrightarrow> [i..j] = []"
by(simp add: upto.simps)

lemma upto_single[simp]: "[i..i] = [i]"
by(simp add: upto.simps)

lemma upto_Nil[simp]: "[i..j] = [] \<longleftrightarrow> j < i"
by (simp add: upto.simps)

lemma upto_Nil2[simp]: "[] = [i..j] \<longleftrightarrow> j < i"
by (simp add: upto.simps)

lemma upto_rec1: "i \<le> j \<Longrightarrow> [i..j] = i#[i+1..j]"
by(simp add: upto.simps)

lemma upto_rec2: "i \<le> j \<Longrightarrow> [i..j] = [i..j - 1]@[j]"
proof(induct "nat(j-i)" arbitrary: i j)
  case 0 thus ?case by(simp add: upto.simps)
next
  case (Suc n)
  hence "n = nat (j - (i + 1))" "i < j" by linarith+
  from this(2) Suc.hyps(1)[OF this(1)] Suc(2,3) upto_rec1 show ?case by simp
qed

lemma length_upto[simp]: "length [i..j] = nat(j - i + 1)"
by(induction i j rule: upto.induct) (auto simp: upto.simps)

lemma set_upto[simp]: "set[i..j] = {i..j}"
proof(induct i j rule:upto.induct)
  case (1 i j)
  from this show ?case
    unfolding upto.simps[of i j] by auto
qed

lemma nth_upto[simp]: "i + int k \<le> j \<Longrightarrow> [i..j] ! k = i + int k"
proof(induction i j arbitrary: k rule: upto.induct)
  case (1 i j)
  then show ?case
    by (auto simp add: upto_rec1 [of i j] nth_Cons')
qed

lemma upto_split1:
  "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..k] = [i..j-1] @ [j..k]"
proof (induction j rule: int_ge_induct)
  case base thus ?case by (simp add: upto_rec1)
next
  case step thus ?case using upto_rec1 upto_rec2 by simp
qed

lemma upto_split2:
  "i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> [i..k] = [i..j] @ [j+1..k]"
using upto_rec1 upto_rec2 upto_split1 by auto

lemma upto_split3: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> [i..k] = [i..j-1] @ j # [j+1..k]"
using upto_rec1 upto_split1 by auto

text\<open>Tail recursive version for code generation:\<close>

definition upto_aux :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "upto_aux i j js = [i..j] @ js"

lemma upto_aux_rec [code]:
  "upto_aux i j js = (if j<i then js else upto_aux i (j - 1) (j#js))"
by (simp add: upto_aux_def upto_rec2)

lemma upto_code[code]: "[i..j] = upto_aux i j []"
by(simp add: upto_aux_def)



subsubsection \<open>\<^const>\<open>successively\<close>\<close>

lemma successively_Cons:
  "successively P (x # xs) \<longleftrightarrow> xs = [] \<or> P x (hd xs) \<and> successively P xs"
by (cases xs) auto

lemma successively_cong [cong]:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P x y \<longleftrightarrow> Q x y" "xs = ys"
  shows   "successively P xs \<longleftrightarrow> successively Q ys"
  unfolding assms(2) [symmetric] using assms(1)
  by (induction xs) (auto simp: successively_Cons)


lemma successively_append_iff:
  "successively P (xs @ ys) \<longleftrightarrow>
     successively P xs \<and> successively P ys \<and> 
     (xs = [] \<or> ys = [] \<or> P (last xs) (hd ys))"
by (induction xs) (auto simp: successively_Cons)

lemma successively_if_sorted_wrt: "sorted_wrt P xs \<Longrightarrow> successively P xs"
by (induction xs rule: induct_list012) auto


lemma successively_iff_sorted_wrt_strong:
  assumes "\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> z \<in> set xs \<Longrightarrow>
                     P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows   "successively P xs \<longleftrightarrow> sorted_wrt P xs"
proof
  assume "successively P xs"
  from this and assms show "sorted_wrt P xs"
  proof (induction xs rule: induct_list012)
    case (3 x y xs)
    from "3.prems" have "P x y"
      by auto
    have IH: "sorted_wrt P (y # xs)"
      using "3.prems"
      by(intro "3.IH"(2) list.set_intros(2))(simp, blast intro: list.set_intros(2))
    have "P x z" if asm: "z \<in> set xs" for z
    proof -
      from IH and asm have "P y z"
        by auto
      with \<open>P x y\<close> show "P x z"
        using "3.prems" asm by auto
    qed
    with IH and \<open>P x y\<close> show ?case by auto
  qed auto
qed (use successively_if_sorted_wrt in blast)

lemma successively_conv_sorted_wrt:
  assumes "transp P"
  shows   "successively P xs \<longleftrightarrow> sorted_wrt P xs"
  using assms unfolding transp_def
  by (intro successively_iff_sorted_wrt_strong) blast

lemma successively_rev [simp]: "successively P (rev xs) \<longleftrightarrow> successively (\<lambda>x y. P y x) xs"
  by (induction xs rule: remdups_adj.induct)
     (auto simp: successively_append_iff successively_Cons)

lemma successively_map: "successively P (map f xs) \<longleftrightarrow> successively (\<lambda>x y. P (f x) (f y)) xs"
  by (induction xs rule: induct_list012) auto

lemma successively_mono:
  assumes "successively P xs"
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  shows   "successively Q xs"
  using assms by (induction Q xs rule: successively.induct) auto

lemma successively_altdef:
  "successively = (\<lambda>P. rec_list True (\<lambda>x xs b. case xs of [] \<Rightarrow> True | y # _ \<Rightarrow> P x y \<and> b))"
proof (intro ext)
  fix P and xs :: "'a list"
  show "successively P xs = rec_list True (\<lambda>x xs b. case xs of [] \<Rightarrow> True | y # _ \<Rightarrow> P x y \<and> b) xs"
    by (induction xs) (auto simp: successively_Cons split: list.splits)
qed


subsubsection \<open>\<^const>\<open>distinct\<close> and \<^const>\<open>remdups\<close> and \<^const>\<open>remdups_adj\<close>\<close>

lemma distinct_tl: "distinct xs \<Longrightarrow> distinct (tl xs)"
by (cases xs) simp_all

lemma distinct_append [simp]:
  "distinct (xs @ ys) = (distinct xs \<and> distinct ys \<and> set xs \<inter> set ys = {})"
by (induct xs) auto

lemma distinct_rev[simp]: "distinct(rev xs) = distinct xs"
by(induct xs) auto

lemma set_remdups [simp]: "set (remdups xs) = set xs"
by (induct xs) (auto simp add: insert_absorb)

lemma distinct_remdups [iff]: "distinct (remdups xs)"
by (induct xs) auto

lemma distinct_remdups_id: "distinct xs \<Longrightarrow> remdups xs = xs"
by (induct xs, auto)

lemma remdups_id_iff_distinct [simp]: "remdups xs = xs \<longleftrightarrow> distinct xs"
by (metis distinct_remdups distinct_remdups_id)

lemma finite_distinct_list: "finite A \<Longrightarrow> \<exists>xs. set xs = A \<and> distinct xs"
by (metis distinct_remdups finite_list set_remdups)

lemma remdups_eq_nil_iff [simp]: "(remdups x = []) = (x = [])"
by (induct x, auto)

lemma remdups_eq_nil_right_iff [simp]: "([] = remdups x) = (x = [])"
by (induct x, auto)

lemma length_remdups_leq[iff]: "length(remdups xs) \<le> length xs"
by (induct xs) auto

lemma length_remdups_eq[iff]:
  "(length (remdups xs) = length xs) = (remdups xs = xs)"
proof (induct xs)
  case (Cons a xs)
  then show ?case
    by simp (metis Suc_n_not_le_n impossible_Cons length_remdups_leq)
qed auto

lemma remdups_filter: "remdups(filter P xs) = filter P (remdups xs)"
by (induct xs) auto

lemma distinct_map:
  "distinct(map f xs) = (distinct xs \<and> inj_on f (set xs))"
by (induct xs) auto

lemma distinct_map_filter:
  "distinct (map f xs) \<Longrightarrow> distinct (map f (filter P xs))"
by (induct xs) auto

lemma distinct_filter [simp]: "distinct xs \<Longrightarrow> distinct (filter P xs)"
by (induct xs) auto

lemma distinct_upt[simp]: "distinct[i..<j]"
by (induct j) auto

lemma distinct_upto[simp]: "distinct[i..j]"
proof (induction i j rule: upto.induct)
  case (1 i j)
  then show ?case
    by (simp add: upto.simps [of i])
qed

lemma distinct_take[simp]: "distinct xs \<Longrightarrow> distinct (take i xs)"
proof (induct xs arbitrary: i)
  case (Cons a xs)
  then show ?case
    by (metis Cons.prems append_take_drop_id distinct_append)
qed auto

lemma distinct_drop[simp]: "distinct xs \<Longrightarrow> distinct (drop i xs)"
proof (induct xs arbitrary: i)
  case (Cons a xs)
  then show ?case
    by (metis Cons.prems append_take_drop_id distinct_append)
qed auto

lemma distinct_list_update:
  assumes d: "distinct xs" and a: "a \<notin> set xs - {xs!i}"
  shows "distinct (xs[i:=a])"
proof (cases "i < length xs")
  case True
  with a have anot: "a \<notin> set (take i xs @ xs ! i # drop (Suc i) xs) - {xs!i}"
    by simp (metis in_set_dropD in_set_takeD)
  show ?thesis
  proof (cases "a = xs!i")
    case True
    with d show ?thesis
      by auto
  next
    case False
    have "set (take i xs) \<inter> set (drop (Suc i) xs) = {}"
      by (metis True d disjoint_insert(1) distinct_append id_take_nth_drop list.set(2))
    then show ?thesis
      using d False anot \<open>i < length xs\<close> by (simp add: upd_conv_take_nth_drop)
  qed
next
  case False with d show ?thesis by auto
qed

lemma distinct_concat:
  "\<lbrakk> distinct xs;
     \<And> ys. ys \<in> set xs \<Longrightarrow> distinct ys;
     \<And> ys zs. \<lbrakk> ys \<in> set xs ; zs \<in> set xs ; ys \<noteq> zs \<rbrakk> \<Longrightarrow> set ys \<inter> set zs = {}
   \<rbrakk> \<Longrightarrow> distinct (concat xs)"
by (induct xs) auto

text \<open>An iff-version of @{thm distinct_concat} is available further down as \<open>distinct_concat_iff\<close>.\<close>

text \<open>It is best to avoid the following indexed version of distinct, but sometimes it is useful.\<close>

lemma distinct_conv_nth: "distinct xs = (\<forall>i < size xs. \<forall>j < size xs. i \<noteq> j \<longrightarrow> xs!i \<noteq> xs!j)"
proof (induct xs)
  case (Cons x xs)
  show ?case
    apply (auto simp add: Cons nth_Cons split: nat.split_asm)
    apply (metis Suc_less_eq2 in_set_conv_nth less_not_refl zero_less_Suc)+
    done
qed auto

lemma nth_eq_iff_index_eq:
  "\<lbrakk> distinct xs; i < length xs; j < length xs \<rbrakk> \<Longrightarrow> (xs!i = xs!j) = (i = j)"
by(auto simp: distinct_conv_nth)

lemma distinct_Ex1:
  "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> (\<exists>!i. i < length xs \<and> xs ! i = x)"
  by (auto simp: in_set_conv_nth nth_eq_iff_index_eq)

lemma inj_on_nth: "distinct xs \<Longrightarrow> \<forall>i \<in> I. i < length xs \<Longrightarrow> inj_on (nth xs) I"
by (rule inj_onI) (simp add: nth_eq_iff_index_eq)

lemma bij_betw_nth:
  assumes "distinct xs" "A = {..<length xs}" "B = set xs"
  shows   "bij_betw ((!) xs) A B"
  using assms unfolding bij_betw_def
  by (auto intro!: inj_on_nth simp: set_conv_nth)

lemma set_update_distinct: "\<lbrakk> distinct xs;  n < length xs \<rbrakk> \<Longrightarrow>
  set(xs[n := x]) = insert x (set xs - {xs!n})"
by(auto simp: set_eq_iff in_set_conv_nth nth_list_update nth_eq_iff_index_eq)

lemma distinct_swap[simp]: "\<lbrakk> i < size xs; j < size xs\<rbrakk> \<Longrightarrow>
  distinct(xs[i := xs!j, j := xs!i]) = distinct xs"
  apply (simp add: distinct_conv_nth nth_list_update)
  apply (safe; metis)
  done

lemma set_swap[simp]:
  "\<lbrakk> i < size xs; j < size xs \<rbrakk> \<Longrightarrow> set(xs[i := xs!j, j := xs!i]) = set xs"
by(simp add: set_conv_nth nth_list_update) metis

lemma distinct_card: "distinct xs \<Longrightarrow> card (set xs) = size xs"
by (induct xs) auto

lemma card_distinct: "card (set xs) = size xs \<Longrightarrow> distinct xs"
proof (induct xs)
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> set xs")
    case False with Cons show ?thesis by simp
  next
    case True with Cons.prems
    have "card (set xs) = Suc (length xs)"
      by (simp add: card_insert_if split: if_split_asm)
    moreover have "card (set xs) \<le> length xs" by (rule card_length)
    ultimately have False by simp
    thus ?thesis ..
  qed
qed simp

lemma distinct_length_filter: "distinct xs \<Longrightarrow> length (filter P xs) = card ({x. P x} Int set xs)"
by (induct xs) (auto)

lemma not_distinct_decomp: "\<not> distinct ws \<Longrightarrow> \<exists>xs ys zs y. ws = xs@[y]@ys@[y]@zs"
proof (induct n == "length ws" arbitrary:ws)
  case (Suc n ws)
  then show ?case
    using length_Suc_conv [of ws n]
    apply (auto simp: eq_commute)
     apply (metis append_Nil in_set_conv_decomp_first)
    by (metis append_Cons)
qed simp

lemma not_distinct_conv_prefix:
  defines "dec as xs y ys \<equiv> y \<in> set xs \<and> distinct xs \<and> as = xs @ y # ys"
  shows "\<not>distinct as \<longleftrightarrow> (\<exists>xs y ys. dec as xs y ys)" (is "?L = ?R")
proof
  assume "?L" then show "?R"
  proof (induct "length as" arbitrary: as rule: less_induct)
    case less
    obtain xs ys zs y where decomp: "as = (xs @ y # ys) @ y # zs"
      using not_distinct_decomp[OF less.prems] by auto
    show ?case
    proof (cases "distinct (xs @ y # ys)")
      case True
      with decomp have "dec as (xs @ y # ys) y zs" by (simp add: dec_def)
      then show ?thesis by blast
    next
      case False
      with less decomp obtain xs' y' ys' where "dec (xs @ y # ys) xs' y' ys'"
        by atomize_elim auto
      with decomp have "dec as xs' y' (ys' @ y # zs)" by (simp add: dec_def)
      then show ?thesis by blast
    qed
  qed
qed (auto simp: dec_def)

lemma distinct_product:
  "distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> distinct (List.product xs ys)"
by (induct xs) (auto intro: inj_onI simp add: distinct_map)

lemma distinct_product_lists:
  assumes "\<forall>xs \<in> set xss. distinct xs"
  shows "distinct (product_lists xss)"
using assms proof (induction xss)
  case (Cons xs xss) note * = this
  then show ?case
  proof (cases "product_lists xss")
    case Nil then show ?thesis by (induct xs) simp_all
  next
    case (Cons ps pss) with * show ?thesis
      by (auto intro!: inj_onI distinct_concat simp add: distinct_map)
  qed
qed simp

lemma length_remdups_concat:
  "length (remdups (concat xss)) = card (\<Union>xs\<in>set xss. set xs)"
by (simp add: distinct_card [symmetric])

lemma remdups_append2:
  "remdups (xs @ remdups ys) = remdups (xs @ ys)"
by(induction xs) auto

lemma length_remdups_card_conv: "length(remdups xs) = card(set xs)"
proof -
  have xs: "concat[xs] = xs" by simp
  from length_remdups_concat[of "[xs]"] show ?thesis unfolding xs by simp
qed

lemma remdups_remdups: "remdups (remdups xs) = remdups xs"
by (induct xs) simp_all

lemma distinct_butlast:
  assumes "distinct xs"
  shows "distinct (butlast xs)"
proof (cases "xs = []")
  case False
    from \<open>xs \<noteq> []\<close> obtain ys y where "xs = ys @ [y]" by (cases xs rule: rev_cases) auto
    with \<open>distinct xs\<close> show ?thesis by simp
qed (auto)

lemma remdups_map_remdups:
  "remdups (map f (remdups xs)) = remdups (map f xs)"
by (induct xs) simp_all

lemma distinct_zipI1:
  assumes "distinct xs"
  shows "distinct (zip xs ys)"
proof (rule zip_obtain_same_length)
  fix xs' :: "'a list" and ys' :: "'b list" and n
  assume "length xs' = length ys'"
  assume "xs' = take n xs"
  with assms have "distinct xs'" by simp
  with \<open>length xs' = length ys'\<close> show "distinct (zip xs' ys')"
    by (induct xs' ys' rule: list_induct2) (auto elim: in_set_zipE)
qed

lemma distinct_zipI2:
  assumes "distinct ys"
  shows "distinct (zip xs ys)"
proof (rule zip_obtain_same_length)
  fix xs' :: "'b list" and ys' :: "'a list" and n
  assume "length xs' = length ys'"
  assume "ys' = take n ys"
  with assms have "distinct ys'" by simp
  with \<open>length xs' = length ys'\<close> show "distinct (zip xs' ys')"
    by (induct xs' ys' rule: list_induct2) (auto elim: in_set_zipE)
qed

lemma set_take_disj_set_drop_if_distinct:
  "distinct vs \<Longrightarrow> i \<le> j \<Longrightarrow> set (take i vs) \<inter> set (drop j vs) = {}"
by (auto simp: in_set_conv_nth distinct_conv_nth)

(* The next two lemmas help Sledgehammer. *)

lemma distinct_singleton: "distinct [x]" by simp

lemma distinct_length_2_or_more:
  "distinct (a # b # xs) \<longleftrightarrow> (a \<noteq> b \<and> distinct (a # xs) \<and> distinct (b # xs))"
by force

lemma remdups_adj_altdef: "(remdups_adj xs = ys) \<longleftrightarrow>
  (\<exists>f::nat => nat. mono f \<and> f ` {0 ..< size xs} = {0 ..< size ys}
    \<and> (\<forall>i < size xs. xs!i = ys!(f i))
    \<and> (\<forall>i. i + 1 < size xs \<longrightarrow> (xs!i = xs!(i+1) \<longleftrightarrow> f i = f(i+1))))" (is "?L \<longleftrightarrow> (\<exists>f. ?p f xs ys)")
proof
  assume ?L
  then show "\<exists>f. ?p f xs ys"
  proof (induct xs arbitrary: ys rule: remdups_adj.induct)
    case (1 ys)
    thus ?case by (intro exI[of _ id]) (auto simp: mono_def)
  next
    case (2 x ys)
    thus ?case by (intro exI[of _ id]) (auto simp: mono_def)
  next
    case (3 x1 x2 xs ys)
    let ?xs = "x1 # x2 # xs"
    let ?cond = "x1 = x2"
    define zs where "zs = remdups_adj (x2 # xs)"
    from 3(1-2)[of zs]
    obtain f where p: "?p f (x2 # xs) zs" unfolding zs_def by (cases ?cond) auto
    then have f0: "f 0 = 0"
      by (intro mono_image_least[where f=f]) blast+
    from p have mono: "mono f" and f_xs_zs: "f ` {0..<length (x2 # xs)} = {0..<length zs}" by auto
    have ys: "ys = (if x1 = x2 then zs else x1 # zs)"
      unfolding 3(3)[symmetric] zs_def by auto
    have zs0: "zs ! 0 = x2" unfolding zs_def by (induct xs) auto
    have zsne: "zs \<noteq> []" unfolding zs_def by (induct xs) auto
    let ?Succ = "if ?cond then id else Suc"
    let ?x1 = "if ?cond then id else Cons x1"
    let ?f = "\<lambda> i. if i = 0 then 0 else ?Succ (f (i - 1))"
    have ys: "ys = ?x1 zs" unfolding ys by (cases ?cond, auto)
    have mono: "mono ?f" using \<open>mono f\<close> unfolding mono_def by auto
    show ?case unfolding ys
    proof (intro exI[of _ ?f] conjI allI impI)
      show "mono ?f" by fact
    next
      fix i assume i: "i < length ?xs"
      with p show "?xs ! i = ?x1 zs ! (?f i)" using zs0 by auto
    next
      fix i assume i: "i + 1 < length ?xs"
      with p show "(?xs ! i = ?xs ! (i + 1)) = (?f i = ?f (i + 1))"
        by (cases i) (auto simp: f0)
    next
      have id: "{0 ..< length (?x1 zs)} = insert 0 (?Succ ` {0 ..< length zs})"
        using zsne by (cases ?cond, auto)
      { fix i  assume "i < Suc (length xs)"
        hence "Suc i \<in> {0..<Suc (Suc (length xs))} \<inter> Collect ((<) 0)" by auto
        from imageI[OF this, of "\<lambda>i. ?Succ (f (i - Suc 0))"]
        have "?Succ (f i) \<in> (\<lambda>i. ?Succ (f (i - Suc 0))) ` ({0..<Suc (Suc (length xs))} \<inter> Collect ((<) 0))" by auto
      }
      then show "?f ` {0 ..< length ?xs} = {0 ..< length (?x1  zs)}"
        unfolding id f_xs_zs[symmetric] by auto
    qed
  qed
next
  assume "\<exists> f. ?p f xs ys"
  then show ?L
  proof (induct xs arbitrary: ys rule: remdups_adj.induct)
    case 1 then show ?case by auto
  next
    case (2 x) then obtain f where f_img: "f ` {0 ..< size [x]} = {0 ..< size ys}"
        and f_nth: "\<And>i. i < size [x] \<Longrightarrow> [x]!i = ys!(f i)"
      by blast

    have "length ys = card (f ` {0 ..< size [x]})"
      using f_img by auto
    then have *: "length ys = 1" by auto
    then have "f 0 = 0" using f_img by auto
    with * show ?case using f_nth by (cases ys) auto
  next
    case (3 x1 x2 xs)
    from "3.prems" obtain f where f_mono: "mono f"
      and f_img: "f ` {0..<length (x1 # x2 # xs)} = {0..<length ys}"
      and f_nth:
        "\<And>i. i < length (x1 # x2 # xs) \<Longrightarrow> (x1 # x2 # xs) ! i = ys ! f i"
        "\<And>i. i + 1 < length (x1 # x2 #xs) \<Longrightarrow>
          ((x1 # x2 # xs) ! i = (x1 # x2 # xs) ! (i + 1)) = (f i = f (i + 1))"
      by blast

    show ?case
    proof cases
      assume "x1 = x2"

      let ?f' = "f \<circ> Suc"

      have "remdups_adj (x1 # xs) = ys"
      proof (intro "3.hyps" exI conjI impI allI)
        show "mono ?f'"
          using f_mono by (simp add: mono_iff_le_Suc)
      next
        have "?f' ` {0 ..< length (x1 # xs)} = f ` {Suc 0 ..< length (x1 # x2 # xs)}"
          using less_Suc_eq_0_disj by auto
        also have "\<dots> = f ` {0 ..< length (x1 # x2 # xs)}"
        proof -
          have "f 0 = f (Suc 0)" using \<open>x1 = x2\<close> f_nth[of 0] by simp
          then show ?thesis
            using less_Suc_eq_0_disj by auto
        qed
        also have "\<dots> = {0 ..< length ys}" by fact
        finally show  "?f' ` {0 ..< length (x1 # xs)} = {0 ..< length ys}" .
      qed (insert f_nth[of "Suc i" for i], auto simp: \<open>x1 = x2\<close>)
      then show ?thesis using \<open>x1 = x2\<close> by simp
    next
      assume "x1 \<noteq> x2"

      have two: "Suc (Suc 0) \<le> length ys"
      proof -
        have "2 = card {f 0, f 1}" using \<open>x1 \<noteq> x2\<close> f_nth[of 0] by auto
        also have "\<dots> \<le> card (f ` {0..< length (x1 # x2 # xs)})"
          by (rule card_mono) auto
        finally show ?thesis using f_img by simp
      qed

      have "f 0 = 0" using f_mono f_img by (rule mono_image_least) simp

      have "f (Suc 0) = Suc 0"
      proof (rule ccontr)
        assume "f (Suc 0) \<noteq> Suc 0"
        then have "Suc 0 < f (Suc 0)" using f_nth[of 0] \<open>x1 \<noteq> x2\<close> \<open>f 0 = 0\<close> by auto
        then have "\<And>i. Suc 0 < f (Suc i)"
          using f_mono
          by (meson Suc_le_mono le0 less_le_trans monoD)
        then have "Suc 0 \<noteq> f i" for i using \<open>f 0 = 0\<close>
          by (cases i) fastforce+
        then have "Suc 0 \<notin> f ` {0 ..< length (x1 # x2 # xs)}" by auto
        then show False using f_img two by auto
      qed
      obtain ys' where "ys = x1 # x2 # ys'"
        using two f_nth[of 0] f_nth[of 1]
        by (auto simp: Suc_le_length_iff  \<open>f 0 = 0\<close> \<open>f (Suc 0) = Suc 0\<close>)

      have Suc0_le_f_Suc: "Suc 0 \<le> f (Suc i)" for i
        by (metis Suc_le_mono \<open>f (Suc 0) = Suc 0\<close> f_mono le0 mono_def)

      define f' where "f' x = f (Suc x) - 1" for x
      have f_Suc: "f (Suc i) = Suc (f' i)" for i
          using Suc0_le_f_Suc[of i] by (auto simp: f'_def)

      have "remdups_adj (x2 # xs) = (x2 # ys')"
      proof (intro "3.hyps" exI conjI impI allI)
        show "mono f'"
          using Suc0_le_f_Suc f_mono by (auto simp: f'_def mono_iff_le_Suc le_diff_iff)
      next
        have "f' ` {0 ..< length (x2 # xs)} = (\<lambda>x. f x - 1) ` {0 ..< length (x1 # x2 #xs)}"
          by (auto simp: f'_def \<open>f 0 = 0\<close> \<open>f (Suc 0) = Suc 0\<close> image_def Bex_def less_Suc_eq_0_disj)
        also have "\<dots> = (\<lambda>x. x - 1) ` f ` {0 ..< length (x1 # x2 #xs)}"
          by (auto simp: image_comp)
        also have "\<dots> = (\<lambda>x. x - 1) ` {0 ..< length ys}"
          by (simp only: f_img)
        also have "\<dots> = {0 ..< length (x2 # ys')}"
          using \<open>ys = _\<close> by (fastforce intro: rev_image_eqI)
        finally show  "f' ` {0 ..< length (x2 # xs)} = {0 ..< length (x2 # ys')}" .
      qed (insert f_nth[of "Suc i" for i] \<open>x1 \<noteq> x2\<close>, auto simp add: f_Suc \<open>ys = _\<close>)
      then show ?case using \<open>ys = _\<close> \<open>x1 \<noteq> x2\<close> by simp
    qed
  qed
qed

lemma hd_remdups_adj[simp]: "hd (remdups_adj xs) = hd xs"
  by (induction xs rule: remdups_adj.induct) simp_all

lemma remdups_adj_Cons: "remdups_adj (x # xs) =
  (case remdups_adj xs of [] \<Rightarrow> [x] | y # xs \<Rightarrow> if x = y then y # xs else x # y # xs)"
  by (induct xs arbitrary: x) (auto split: list.splits)

lemma remdups_adj_append_two:
  "remdups_adj (xs @ [x,y]) = remdups_adj (xs @ [x]) @ (if x = y then [] else [y])"
  by (induct xs rule: remdups_adj.induct, simp_all)

lemma remdups_adj_adjacent:
  "Suc i < length (remdups_adj xs) \<Longrightarrow> remdups_adj xs ! i \<noteq> remdups_adj xs ! Suc i"
proof (induction xs arbitrary: i rule: remdups_adj.induct)
  case (3 x y xs i)
  thus ?case by (cases i, cases "x = y") (simp, auto simp: hd_conv_nth[symmetric])
qed simp_all

lemma remdups_adj_rev[simp]: "remdups_adj (rev xs) = rev (remdups_adj xs)"
by (induct xs rule: remdups_adj.induct, simp_all add: remdups_adj_append_two)

lemma remdups_adj_length[simp]: "length (remdups_adj xs) \<le> length xs"
by (induct xs rule: remdups_adj.induct, auto)

lemma remdups_adj_length_ge1[simp]: "xs \<noteq> [] \<Longrightarrow> length (remdups_adj xs) \<ge> Suc 0"
by (induct xs rule: remdups_adj.induct, simp_all)

lemma remdups_adj_Nil_iff[simp]: "remdups_adj xs = [] \<longleftrightarrow> xs = []"
by (induct xs rule: remdups_adj.induct, simp_all)

lemma remdups_adj_set[simp]: "set (remdups_adj xs) = set xs"
by (induct xs rule: remdups_adj.induct, simp_all)

lemma last_remdups_adj [simp]: "last (remdups_adj xs) = last xs"
  by (induction xs rule: remdups_adj.induct) auto

lemma remdups_adj_Cons_alt[simp]: "x # tl (remdups_adj (x # xs)) = remdups_adj (x # xs)"
by (induct xs rule: remdups_adj.induct, auto)

lemma remdups_adj_distinct: "distinct xs \<Longrightarrow> remdups_adj xs = xs"
by (induct xs rule: remdups_adj.induct, simp_all)

lemma remdups_adj_append:
  "remdups_adj (xs\<^sub>1 @ x # xs\<^sub>2) = remdups_adj (xs\<^sub>1 @ [x]) @ tl (remdups_adj (x # xs\<^sub>2))"
by (induct xs\<^sub>1 rule: remdups_adj.induct, simp_all)

lemma remdups_adj_singleton:
  "remdups_adj xs = [x] \<Longrightarrow> xs = replicate (length xs) x"
by (induct xs rule: remdups_adj.induct, auto split: if_split_asm)

lemma remdups_adj_map_injective:
  assumes "inj f"
  shows "remdups_adj (map f xs) = map f (remdups_adj xs)"
by (induct xs rule: remdups_adj.induct) (auto simp add: injD[OF assms])

lemma remdups_adj_replicate:
  "remdups_adj (replicate n x) = (if n = 0 then [] else [x])"
  by (induction n) (auto simp: remdups_adj_Cons)

lemma remdups_upt [simp]: "remdups [m..<n] = [m..<n]"
proof (cases "m \<le> n")
  case False then show ?thesis by simp
next
  case True then obtain q where "n = m + q"
    by (auto simp add: le_iff_add)
  moreover have "remdups [m..<m + q] = [m..<m + q]"
    by (induct q) simp_all
  ultimately show ?thesis by simp
qed

lemma successively_remdups_adjI:
  "successively P xs \<Longrightarrow> successively P (remdups_adj xs)"
by (induction xs rule: remdups_adj.induct) (auto simp: successively_Cons)

lemma successively_remdups_adj_iff:
  "(\<And>x. x \<in> set xs \<Longrightarrow> P x x) \<Longrightarrow>
  successively P (remdups_adj xs) \<longleftrightarrow> successively P xs"
by (induction xs rule: remdups_adj.induct)(auto simp: successively_Cons)

lemma remdups_adj_Cons':
  "remdups_adj (x # xs) = x # remdups_adj (dropWhile (\<lambda>y. y = x) xs)"
by (induction xs) auto

lemma remdups_adj_singleton_iff:
  "length (remdups_adj xs) = Suc 0 \<longleftrightarrow> xs \<noteq> [] \<and> xs = replicate (length xs) (hd xs)"
proof safe
  assume *: "xs = replicate (length xs) (hd xs)" and [simp]: "xs \<noteq> []"
  show "length (remdups_adj xs) = Suc 0"
    by (subst *) (auto simp: remdups_adj_replicate)
next
  assume "length (remdups_adj xs) = Suc 0"
  thus "xs = replicate (length xs) (hd xs)"
    by (induction xs rule: remdups_adj.induct) (auto split: if_splits)
qed auto

lemma tl_remdups_adj:
  "ys \<noteq> [] \<Longrightarrow> tl (remdups_adj ys) = remdups_adj (dropWhile (\<lambda>x. x = hd ys) (tl ys))"
by (cases ys) (simp_all add: remdups_adj_Cons')

lemma remdups_adj_append_dropWhile:
  "remdups_adj (xs @ y # ys) = remdups_adj (xs @ [y]) @ remdups_adj (dropWhile (\<lambda>x. x = y) ys)"
by (subst remdups_adj_append) (simp add: tl_remdups_adj)

lemma remdups_adj_append':
  assumes "xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys"
  shows   "remdups_adj (xs @ ys) = remdups_adj xs @ remdups_adj ys"
proof -
  have ?thesis if [simp]: "xs \<noteq> []" "ys \<noteq> []" and "last xs \<noteq> hd ys"
  proof -
    obtain x xs' where xs: "xs = xs' @ [x]"
      by (cases xs rule: rev_cases) auto
    have "remdups_adj (xs' @ x # ys) = remdups_adj (xs' @ [x]) @ remdups_adj ys"
      using \<open>last xs \<noteq> hd ys\<close> unfolding xs
      by (metis (full_types) dropWhile_eq_self_iff last_snoc remdups_adj_append_dropWhile)
    thus ?thesis by (simp add: xs)
  qed
  thus ?thesis using assms 
    by (cases "xs = []"; cases "ys = []") auto
qed

lemma remdups_adj_append'': "xs \<noteq> []
  \<Longrightarrow> remdups_adj (xs @ ys) = remdups_adj xs @ remdups_adj (dropWhile (\<lambda>y. y = last xs) ys)"
by (induction xs rule: remdups_adj.induct) (auto simp: remdups_adj_Cons')


subsection \<open>@{const distinct_adj}\<close>

lemma distinct_adj_Nil [simp]: "distinct_adj []"
  and distinct_adj_singleton [simp]: "distinct_adj [x]"
  and distinct_adj_Cons_Cons [simp]: "distinct_adj (x # y # xs) \<longleftrightarrow> x \<noteq> y \<and> distinct_adj (y # xs)"
by (auto simp: distinct_adj_def)

lemma distinct_adj_Cons: "distinct_adj (x # xs) \<longleftrightarrow> xs = [] \<or> x \<noteq> hd xs \<and> distinct_adj xs"
by (cases xs) auto

lemma distinct_adj_ConsD: "distinct_adj (x # xs) \<Longrightarrow> distinct_adj xs"
by (cases xs) auto

lemma distinct_adj_remdups_adj[simp]: "distinct_adj (remdups_adj xs)"
by (induction xs rule: remdups_adj.induct) (auto simp: distinct_adj_Cons)

lemma distinct_adj_altdef: "distinct_adj xs \<longleftrightarrow> remdups_adj xs = xs"
proof
  assume "remdups_adj xs = xs"
  with distinct_adj_remdups_adj[of xs] show "distinct_adj xs"
    by simp
next
  assume "distinct_adj xs"
  thus "remdups_adj xs = xs"
    by (induction xs rule: induct_list012) auto
qed

lemma distinct_adj_rev [simp]: "distinct_adj (rev xs) \<longleftrightarrow> distinct_adj xs"
by (simp add: distinct_adj_def eq_commute)

lemma distinct_adj_append_iff:
  "distinct_adj (xs @ ys) \<longleftrightarrow>
     distinct_adj xs \<and> distinct_adj ys \<and> (xs = [] \<or> ys = [] \<or> last xs \<noteq> hd ys)"
by (auto simp: distinct_adj_def successively_append_iff)

lemma distinct_adj_appendD1 [dest]: "distinct_adj (xs @ ys) \<Longrightarrow> distinct_adj xs"
  and distinct_adj_appendD2 [dest]: "distinct_adj (xs @ ys) \<Longrightarrow> distinct_adj ys"
  by (auto simp: distinct_adj_append_iff)

lemma distinct_adj_mapI: "distinct_adj xs \<Longrightarrow> inj_on f (set xs) \<Longrightarrow> distinct_adj (map f xs)"
  unfolding distinct_adj_def successively_map
  by (erule successively_mono) (auto simp: inj_on_def)

lemma distinct_adj_mapD: "distinct_adj (map f xs) \<Longrightarrow> distinct_adj xs"
unfolding distinct_adj_def successively_map by (erule successively_mono) auto

lemma distinct_adj_map_iff: "inj_on f (set xs) \<Longrightarrow> distinct_adj (map f xs) \<longleftrightarrow> distinct_adj xs"
using distinct_adj_mapD distinct_adj_mapI by blast


subsubsection \<open>\<^const>\<open>insert\<close>\<close>

lemma in_set_insert [simp]:
  "x \<in> set xs \<Longrightarrow> List.insert x xs = xs"
by (simp add: List.insert_def)

lemma not_in_set_insert [simp]:
  "x \<notin> set xs \<Longrightarrow> List.insert x xs = x # xs"
by (simp add: List.insert_def)

lemma insert_Nil [simp]: "List.insert x [] = [x]"
by simp

lemma set_insert [simp]: "set (List.insert x xs) = insert x (set xs)"
by (auto simp add: List.insert_def)

lemma distinct_insert [simp]: "distinct (List.insert x xs) = distinct xs"
by (simp add: List.insert_def)

lemma insert_remdups:
  "List.insert x (remdups xs) = remdups (List.insert x xs)"
by (simp add: List.insert_def)


subsubsection \<open>\<^const>\<open>List.union\<close>\<close>

text\<open>This is all one should need to know about union:\<close>
lemma set_union[simp]: "set (List.union xs ys) = set xs \<union> set ys"
unfolding List.union_def
by(induct xs arbitrary: ys) simp_all

lemma distinct_union[simp]: "distinct(List.union xs ys) = distinct ys"
unfolding List.union_def
by(induct xs arbitrary: ys) simp_all


subsubsection \<open>\<^const>\<open>List.find\<close>\<close>

lemma find_None_iff: "List.find P xs = None \<longleftrightarrow> \<not> (\<exists>x. x \<in> set xs \<and> P x)"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case by (fastforce split: if_splits)
qed

lemma find_Some_iff:
  "List.find P xs = Some x \<longleftrightarrow>
  (\<exists>i<length xs. P (xs!i) \<and> x = xs!i \<and> (\<forall>j<i. \<not> P (xs!j)))"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons x xs) thus ?case
    apply(auto simp: nth_Cons' split: if_splits)
    using diff_Suc_1[unfolded One_nat_def] less_Suc_eq_0_disj by fastforce
qed

lemma find_cong[fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> P x = Q x"
  shows "List.find P xs = List.find Q ys"
proof (cases "List.find P xs")
  case None thus ?thesis by (metis find_None_iff assms)
next
  case (Some x)
  hence "List.find Q ys = Some x" using assms
    by (auto simp add: find_Some_iff)
  thus ?thesis using Some by auto
qed

lemma find_dropWhile:
  "List.find P xs = (case dropWhile (Not \<circ> P) xs
   of [] \<Rightarrow> None
    | x # _ \<Rightarrow> Some x)"
by (induct xs) simp_all


subsubsection \<open>\<^const>\<open>count_list\<close>\<close>

lemma count_notin[simp]: "x \<notin> set xs \<Longrightarrow> count_list xs x = 0"
by (induction xs) auto

lemma count_le_length: "count_list xs x \<le> length xs"
by (induction xs) auto

lemma sum_count_set:
  "set xs \<subseteq> X \<Longrightarrow> finite X \<Longrightarrow> sum (count_list xs) X = length xs"
proof (induction xs arbitrary: X)
  case (Cons x xs)
  then show ?case
    using sum.remove [of X x "count_list xs"]
    by (auto simp: sum.If_cases simp flip: diff_eq)
qed simp


subsubsection \<open>\<^const>\<open>List.extract\<close>\<close>

lemma extract_None_iff: "List.extract P xs = None \<longleftrightarrow> \<not> (\<exists> x\<in>set xs. P x)"
by(auto simp: extract_def dropWhile_eq_Cons_conv split: list.splits)
  (metis in_set_conv_decomp)

lemma extract_SomeE:
 "List.extract P xs = Some (ys, y, zs) \<Longrightarrow>
  xs = ys @ y # zs \<and> P y \<and> \<not> (\<exists> y \<in> set ys. P y)"
by(auto simp: extract_def dropWhile_eq_Cons_conv split: list.splits)

lemma extract_Some_iff:
  "List.extract P xs = Some (ys, y, zs) \<longleftrightarrow>
   xs = ys @ y # zs \<and> P y \<and> \<not> (\<exists> y \<in> set ys. P y)"
by(auto simp: extract_def dropWhile_eq_Cons_conv dest: set_takeWhileD split: list.splits)

lemma extract_Nil_code[code]: "List.extract P [] = None"
by(simp add: extract_def)

lemma extract_Cons_code[code]:
  "List.extract P (x # xs) = (if P x then Some ([], x, xs) else
   (case List.extract P xs of
      None \<Rightarrow> None |
      Some (ys, y, zs) \<Rightarrow> Some (x#ys, y, zs)))"
by(auto simp add: extract_def comp_def split: list.splits)
  (metis dropWhile_eq_Nil_conv list.distinct(1))


subsubsection \<open>\<^const>\<open>remove1\<close>\<close>

lemma remove1_append:
  "remove1 x (xs @ ys) =
  (if x \<in> set xs then remove1 x xs @ ys else xs @ remove1 x ys)"
by (induct xs) auto

lemma remove1_commute: "remove1 x (remove1 y zs) = remove1 y (remove1 x zs)"
by (induct zs) auto

lemma in_set_remove1[simp]:
  "a \<noteq> b \<Longrightarrow> a \<in> set(remove1 b xs) = (a \<in> set xs)"
  by (induct xs) auto

lemma set_remove1_subset: "set(remove1 x xs) \<subseteq> set xs"
  by (induct xs) auto

lemma set_remove1_eq [simp]: "distinct xs \<Longrightarrow> set(remove1 x xs) = set xs - {x}"
  by (induct xs) auto

lemma length_remove1:
  "length(remove1 x xs) = (if x \<in> set xs then length xs - 1 else length xs)"
by (induct xs) (auto dest!:length_pos_if_in_set)

lemma remove1_filter_not[simp]:
  "\<not> P x \<Longrightarrow> remove1 x (filter P xs) = filter P xs"
by(induct xs) auto

lemma filter_remove1:
  "filter Q (remove1 x xs) = remove1 x (filter Q xs)"
by (induct xs) auto

lemma notin_set_remove1[simp]: "x \<notin> set xs \<Longrightarrow> x \<notin> set(remove1 y xs)"
by(insert set_remove1_subset) fast

lemma distinct_remove1[simp]: "distinct xs \<Longrightarrow> distinct(remove1 x xs)"
by (induct xs) simp_all

lemma remove1_remdups:
  "distinct xs \<Longrightarrow> remove1 x (remdups xs) = remdups (remove1 x xs)"
by (induct xs) simp_all

lemma remove1_idem: "x \<notin> set xs \<Longrightarrow> remove1 x xs = xs"
by (induct xs) simp_all

lemma remove1_split:
  "a \<in> set xs \<Longrightarrow> remove1 a xs = ys \<longleftrightarrow> (\<exists>ls rs. xs = ls @ a # rs \<and> a \<notin> set ls \<and> ys = ls @ rs)"
by (metis remove1.simps(2) remove1_append split_list_first)


subsubsection \<open>\<^const>\<open>removeAll\<close>\<close>

lemma removeAll_filter_not_eq:
  "removeAll x = filter (\<lambda>y. x \<noteq> y)"
proof
  fix xs
  show "removeAll x xs = filter (\<lambda>y. x \<noteq> y) xs"
    by (induct xs) auto
qed

lemma removeAll_append[simp]:
  "removeAll x (xs @ ys) = removeAll x xs @ removeAll x ys"
by (induct xs) auto

lemma set_removeAll[simp]: "set(removeAll x xs) = set xs - {x}"
by (induct xs) auto

lemma removeAll_id[simp]: "x \<notin> set xs \<Longrightarrow> removeAll x xs = xs"
by (induct xs) auto

(* Needs count:: 'a \<Rightarrow> 'a list \<Rightarrow> nat
lemma length_removeAll:
  "length(removeAll x xs) = length xs - count x xs"
*)

lemma removeAll_filter_not[simp]:
  "\<not> P x \<Longrightarrow> removeAll x (filter P xs) = filter P xs"
by(induct xs) auto

lemma distinct_removeAll:
  "distinct xs \<Longrightarrow> distinct (removeAll x xs)"
by (simp add: removeAll_filter_not_eq)

lemma distinct_remove1_removeAll:
  "distinct xs \<Longrightarrow> remove1 x xs = removeAll x xs"
by (induct xs) simp_all

lemma map_removeAll_inj_on: "inj_on f (insert x (set xs)) \<Longrightarrow>
  map f (removeAll x xs) = removeAll (f x) (map f xs)"
by (induct xs) (simp_all add:inj_on_def)

lemma map_removeAll_inj: "inj f \<Longrightarrow>
  map f (removeAll x xs) = removeAll (f x) (map f xs)"
by (rule map_removeAll_inj_on, erule subset_inj_on, rule subset_UNIV)

lemma length_removeAll_less_eq [simp]:
  "length (removeAll x xs) \<le> length xs"
  by (simp add: removeAll_filter_not_eq)

lemma length_removeAll_less [termination_simp]:
  "x \<in> set xs \<Longrightarrow> length (removeAll x xs) < length xs"
  by (auto dest: length_filter_less simp add: removeAll_filter_not_eq)

lemma distinct_concat_iff: "distinct (concat xs) \<longleftrightarrow>
  distinct (removeAll [] xs) \<and> 
  (\<forall>ys. ys \<in> set xs \<longrightarrow> distinct ys) \<and>
  (\<forall>ys zs. ys \<in> set xs \<and> zs \<in> set xs \<and> ys \<noteq> zs \<longrightarrow> set ys \<inter> set zs = {})"
apply (induct xs)
 apply(simp_all, safe, auto)
by (metis Int_iff UN_I empty_iff equals0I set_empty)


subsubsection \<open>\<^const>\<open>replicate\<close>\<close>

lemma length_replicate [simp]: "length (replicate n x) = n"
by (induct n) auto

lemma replicate_eqI:
  assumes "length xs = n" and "\<And>y. y \<in> set xs \<Longrightarrow> y = x"
  shows "xs = replicate n x"
  using assms
proof (induct xs arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case by (cases n) simp_all
qed

lemma Ex_list_of_length: "\<exists>xs. length xs = n"
by (rule exI[of _ "replicate n undefined"]) simp

lemma map_replicate [simp]: "map f (replicate n x) = replicate n (f x)"
by (induct n) auto

lemma map_replicate_const:
  "map (\<lambda> x. k) lst = replicate (length lst) k"
by (induct lst) auto

lemma replicate_app_Cons_same:
"(replicate n x) @ (x # xs) = x # replicate n x @ xs"
by (induct n) auto

lemma rev_replicate [simp]: "rev (replicate n x) = replicate n x"
by (induct n) (auto simp: replicate_app_Cons_same)

lemma replicate_add: "replicate (n + m) x = replicate n x @ replicate m x"
by (induct n) auto

text\<open>Courtesy of Matthias Daum:\<close>
lemma append_replicate_commute:
  "replicate n x @ replicate k x = replicate k x @ replicate n x"
  by (metis add.commute replicate_add)

text\<open>Courtesy of Andreas Lochbihler:\<close>
lemma filter_replicate:
  "filter P (replicate n x) = (if P x then replicate n x else [])"
by(induct n) auto

lemma hd_replicate [simp]: "n \<noteq> 0 \<Longrightarrow> hd (replicate n x) = x"
by (induct n) auto

lemma tl_replicate [simp]: "tl (replicate n x) = replicate (n - 1) x"
by (induct n) auto

lemma last_replicate [simp]: "n \<noteq> 0 \<Longrightarrow> last (replicate n x) = x"
by (atomize (full), induct n) auto

lemma nth_replicate[simp]: "i < n \<Longrightarrow> (replicate n x)!i = x"
by (induct n arbitrary: i)(auto simp: nth_Cons split: nat.split)

text\<open>Courtesy of Matthias Daum (2 lemmas):\<close>
lemma take_replicate[simp]: "take i (replicate k x) = replicate (min i k) x"
proof (cases "k \<le> i")
  case True
  then show ?thesis
    by (simp add: min_def)
next
  case False
  then have "replicate k x = replicate i x @ replicate (k - i) x"
    by (simp add: replicate_add [symmetric])
  then show ?thesis
    by (simp add: min_def)
qed

lemma drop_replicate[simp]: "drop i (replicate k x) = replicate (k-i) x"
proof (induct k arbitrary: i)
  case (Suc k)
  then show ?case
    by (simp add: drop_Cons')
qed simp

lemma set_replicate_Suc: "set (replicate (Suc n) x) = {x}"
by (induct n) auto

lemma set_replicate [simp]: "n \<noteq> 0 \<Longrightarrow> set (replicate n x) = {x}"
by (fast dest!: not0_implies_Suc intro!: set_replicate_Suc)

lemma set_replicate_conv_if: "set (replicate n x) = (if n = 0 then {} else {x})"
by auto

lemma in_set_replicate[simp]: "(x \<in> set (replicate n y)) = (x = y \<and> n \<noteq> 0)"
by (simp add: set_replicate_conv_if)

lemma Ball_set_replicate[simp]:
  "(\<forall>x \<in> set(replicate n a). P x) = (P a \<or> n=0)"
by(simp add: set_replicate_conv_if)

lemma Bex_set_replicate[simp]:
  "(\<exists>x \<in> set(replicate n a). P x) = (P a \<and> n\<noteq>0)"
by(simp add: set_replicate_conv_if)

lemma replicate_append_same:
  "replicate i x @ [x] = x # replicate i x"
  by (induct i) simp_all

lemma map_replicate_trivial:
  "map (\<lambda>i. x) [0..<i] = replicate i x"
by (induct i) (simp_all add: replicate_append_same)

lemma concat_replicate_trivial[simp]:
  "concat (replicate i []) = []"
  by (induct i) (auto simp add: map_replicate_const)

lemma replicate_empty[simp]: "(replicate n x = []) \<longleftrightarrow> n=0"
by (induct n) auto

lemma empty_replicate[simp]: "([] = replicate n x) \<longleftrightarrow> n=0"
by (induct n) auto

lemma replicate_eq_replicate[simp]:
  "(replicate m x = replicate n y) \<longleftrightarrow> (m=n \<and> (m\<noteq>0 \<longrightarrow> x=y))"
proof (induct m arbitrary: n)
  case (Suc m n)
  then show ?case
    by (induct n) auto
qed simp

lemma takeWhile_replicate[simp]:
  "takeWhile P (replicate n x) = (if P x then replicate n x else [])"
using takeWhile_eq_Nil_iff by fastforce

lemma dropWhile_replicate[simp]:
  "dropWhile P (replicate n x) = (if P x then [] else replicate n x)"
using dropWhile_eq_self_iff by fastforce

lemma replicate_length_filter:
  "replicate (length (filter (\<lambda>y. x = y) xs)) x = filter (\<lambda>y. x = y) xs"
  by (induct xs) auto

lemma comm_append_are_replicate:
  "xs @ ys = ys @ xs \<Longrightarrow> \<exists>m n zs. concat (replicate m zs) = xs \<and> concat (replicate n zs) = ys"
proof (induction "length (xs @ ys) + length xs" arbitrary: xs ys rule: less_induct)
  case less
  consider (1) "length ys < length xs" | (2) "xs = []" | (3) "length xs \<le> length ys \<and> xs \<noteq> []"
    by linarith
  then show ?case
  proof (cases)
    case 1
    then show ?thesis
      using less.hyps[OF _ less.prems[symmetric]] nat_add_left_cancel_less by auto
  next
    case 2
    then have "concat (replicate 0 ys) = xs \<and> concat (replicate 1 ys) = ys"
      by simp
    then show ?thesis
      by blast
  next
    case 3
    then have "length xs \<le> length ys" and "xs \<noteq> []"
      by blast+
    from \<open>length xs \<le> length ys\<close> and  \<open>xs @ ys = ys @ xs\<close>
    obtain ws where "ys = xs @ ws"
      by (auto simp: append_eq_append_conv2)
    from this and \<open>xs \<noteq> []\<close>
    have "length ws < length ys"
      by simp
    from \<open>xs @ ys = ys @ xs\<close>[unfolded \<open>ys = xs @ ws\<close>]
    have "xs @ ws = ws @ xs"
      by simp
    from less.hyps[OF _ this] \<open>length ws < length ys\<close>
    obtain m n' zs where "concat (replicate m zs) = xs" and  "concat (replicate n' zs) = ws"
      by auto
    then have "concat (replicate (m+n') zs) = ys"
      using \<open>ys = xs @ ws\<close>
      by (simp add: replicate_add)
    then show ?thesis
      using \<open>concat (replicate m zs) = xs\<close> by blast
  qed
qed

lemma comm_append_is_replicate:
  fixes xs ys :: "'a list"
  assumes "xs \<noteq> []" "ys \<noteq> []"
  assumes "xs @ ys = ys @ xs"
  shows "\<exists>n zs. n > 1 \<and> concat (replicate n zs) = xs @ ys"
proof -
  obtain m n zs where "concat (replicate m zs) = xs"
    and "concat (replicate n zs) = ys"
    using comm_append_are_replicate[OF assms(3)] by blast
  then have "m + n > 1" and "concat (replicate (m+n) zs) = xs @ ys"
    using \<open>xs \<noteq> []\<close> and \<open>ys \<noteq> []\<close>
    by (auto simp: replicate_add)
  then show ?thesis by blast
qed

lemma Cons_replicate_eq:
  "x # xs = replicate n y \<longleftrightarrow> x = y \<and> n > 0 \<and> xs = replicate (n - 1) x"
by (induct n) auto

lemma replicate_length_same:
  "(\<forall>y\<in>set xs. y = x) \<Longrightarrow> replicate (length xs) x = xs"
by (induct xs) simp_all

lemma foldr_replicate [simp]:
  "foldr f (replicate n x) = f x ^^ n"
by (induct n) (simp_all)

lemma fold_replicate [simp]:
  "fold f (replicate n x) = f x ^^ n"
by (subst foldr_fold [symmetric]) simp_all


subsubsection \<open>\<^const>\<open>enumerate\<close>\<close>

lemma enumerate_simps [simp, code]:
  "enumerate n [] = []"
  "enumerate n (x # xs) = (n, x) # enumerate (Suc n) xs"
  by (simp_all add: enumerate_eq_zip upt_rec)

lemma length_enumerate [simp]:
  "length (enumerate n xs) = length xs"
by (simp add: enumerate_eq_zip)

lemma map_fst_enumerate [simp]:
  "map fst (enumerate n xs) = [n..<n + length xs]"
by (simp add: enumerate_eq_zip)

lemma map_snd_enumerate [simp]:
  "map snd (enumerate n xs) = xs"
by (simp add: enumerate_eq_zip)

lemma in_set_enumerate_eq:
  "p \<in> set (enumerate n xs) \<longleftrightarrow> n \<le> fst p \<and> fst p < length xs + n \<and> nth xs (fst p - n) = snd p"
proof -
  { fix m
    assume "n \<le> m"
    moreover assume "m < length xs + n"
    ultimately have "[n..<n + length xs] ! (m - n) = m \<and>
      xs ! (m - n) = xs ! (m - n) \<and> m - n < length xs" by auto
    then have "\<exists>q. [n..<n + length xs] ! q = m \<and>
        xs ! q = xs ! (m - n) \<and> q < length xs" ..
  } then show ?thesis by (cases p) (auto simp add: enumerate_eq_zip in_set_zip)
qed

lemma nth_enumerate_eq: "m < length xs \<Longrightarrow> enumerate n xs ! m = (n + m, xs ! m)"
by (simp add: enumerate_eq_zip)

lemma enumerate_replicate_eq:
  "enumerate n (replicate m a) = map (\<lambda>q. (q, a)) [n..<n + m]"
by (rule pair_list_eqI)
   (simp_all add: enumerate_eq_zip comp_def map_replicate_const)

lemma enumerate_Suc_eq:
  "enumerate (Suc n) xs = map (apfst Suc) (enumerate n xs)"
by (rule pair_list_eqI)
   (simp_all add: not_le, simp del: map_map add: map_Suc_upt map_map [symmetric])

lemma distinct_enumerate [simp]:
  "distinct (enumerate n xs)"
by (simp add: enumerate_eq_zip distinct_zipI1)

lemma enumerate_append_eq:
  "enumerate n (xs @ ys) = enumerate n xs @ enumerate (n + length xs) ys"
  by (simp add: enumerate_eq_zip add.assoc zip_append2)

lemma enumerate_map_upt:
  "enumerate n (map f [n..<m]) = map (\<lambda>k. (k, f k)) [n..<m]"
by (cases "n \<le> m") (simp_all add: zip_map2 zip_same_conv_map enumerate_eq_zip)


subsubsection \<open>\<^const>\<open>rotate1\<close> and \<^const>\<open>rotate\<close>\<close>

lemma rotate0[simp]: "rotate 0 = id"
by(simp add:rotate_def)

lemma rotate_Suc[simp]: "rotate (Suc n) xs = rotate1(rotate n xs)"
by(simp add:rotate_def)

lemma rotate_add:
  "rotate (m+n) = rotate m \<circ> rotate n"
by(simp add:rotate_def funpow_add)

lemma rotate_rotate: "rotate m (rotate n xs) = rotate (m+n) xs"
by(simp add:rotate_add)

lemma rotate1_map: "rotate1 (map f xs) = map f (rotate1 xs)"
by(cases xs) simp_all

lemma rotate1_rotate_swap: "rotate1 (rotate n xs) = rotate n (rotate1 xs)"
by(simp add:rotate_def funpow_swap1)

lemma rotate1_length01[simp]: "length xs \<le> 1 \<Longrightarrow> rotate1 xs = xs"
by(cases xs) simp_all

lemma rotate_length01[simp]: "length xs \<le> 1 \<Longrightarrow> rotate n xs = xs"
  by (induct n) (simp_all add:rotate_def)

lemma rotate1_hd_tl: "xs \<noteq> [] \<Longrightarrow> rotate1 xs = tl xs @ [hd xs]"
by (cases xs) simp_all

lemma rotate_drop_take:
  "rotate n xs = drop (n mod length xs) xs @ take (n mod length xs) xs"
proof (induct n)
  case (Suc n)
  show ?case
  proof (cases "xs = []")
    case False
    then show ?thesis
    proof (cases "n mod length xs = 0")
      case True
      then show ?thesis
        by (auto simp add: mod_Suc False Suc.hyps drop_Suc rotate1_hd_tl take_Suc Suc_length_conv)
    next
      case False
      with \<open>xs \<noteq> []\<close> Suc
      show ?thesis
        by (simp add: rotate_def mod_Suc rotate1_hd_tl drop_Suc[symmetric] drop_tl[symmetric]
            take_hd_drop linorder_not_le)
    qed
  qed simp
qed simp

lemma rotate_conv_mod: "rotate n xs = rotate (n mod length xs) xs"
  by(simp add:rotate_drop_take)

lemma rotate_id[simp]: "n mod length xs = 0 \<Longrightarrow> rotate n xs = xs"
  by(simp add:rotate_drop_take)

lemma length_rotate1[simp]: "length(rotate1 xs) = length xs"
  by (cases xs) simp_all

lemma length_rotate[simp]: "length(rotate n xs) = length xs"
  by (induct n arbitrary: xs) (simp_all add:rotate_def)

lemma distinct1_rotate[simp]: "distinct(rotate1 xs) = distinct xs"
  by (cases xs) auto

lemma distinct_rotate[simp]: "distinct(rotate n xs) = distinct xs"
  by (induct n) (simp_all add:rotate_def)

lemma rotate_map: "rotate n (map f xs) = map f (rotate n xs)"
  by(simp add:rotate_drop_take take_map drop_map)

lemma set_rotate1[simp]: "set(rotate1 xs) = set xs"
  by (cases xs) auto

lemma set_rotate[simp]: "set(rotate n xs) = set xs"
  by (induct n) (simp_all add:rotate_def)

lemma rotate1_is_Nil_conv[simp]: "(rotate1 xs = []) = (xs = [])"
  by (cases xs) auto

lemma rotate_is_Nil_conv[simp]: "(rotate n xs = []) = (xs = [])"
  by (induct n) (simp_all add:rotate_def)

lemma rotate_rev:
  "rotate n (rev xs) = rev(rotate (length xs - (n mod length xs)) xs)"
proof (cases "length xs = 0 \<or> n mod length xs = 0")
  case False
  then show ?thesis
    by(simp add:rotate_drop_take rev_drop rev_take)
qed force

lemma hd_rotate_conv_nth:
  assumes "xs \<noteq> []" shows "hd(rotate n xs) = xs!(n mod length xs)"
proof -
  have "n mod length xs < length xs"
    using assms by simp
  then show ?thesis
    by (metis drop_eq_Nil hd_append2 hd_drop_conv_nth leD rotate_drop_take)
qed

lemma rotate_append: "rotate (length l) (l @ q) = q @ l"
  by (induct l arbitrary: q) (auto simp add: rotate1_rotate_swap)

lemma nth_rotate:
  \<open>rotate m xs ! n = xs ! ((m + n) mod length xs)\<close> if \<open>n < length xs\<close>
  using that apply (auto simp add: rotate_drop_take nth_append not_less less_diff_conv ac_simps dest!: le_Suc_ex)
   apply (metis add.commute mod_add_right_eq mod_less)
  apply (metis (no_types, lifting) Nat.diff_diff_right add.commute add_diff_cancel_right' diff_le_self dual_order.strict_trans2 length_greater_0_conv less_nat_zero_code list.size(3) mod_add_right_eq mod_add_self2 mod_le_divisor mod_less)
  done

lemma nth_rotate1:
  \<open>rotate1 xs ! n = xs ! (Suc n mod length xs)\<close> if \<open>n < length xs\<close>
  using that nth_rotate [of n xs 1] by simp


subsubsection \<open>\<^const>\<open>nths\<close> --- a generalization of \<^const>\<open>nth\<close> to sets\<close>

lemma nths_empty [simp]: "nths xs {} = []"
  by (auto simp add: nths_def)

lemma nths_nil [simp]: "nths [] A = []"
  by (auto simp add: nths_def)

lemma nths_all: "\<forall>i < length xs. i \<in> I \<Longrightarrow> nths xs I = xs"
apply (simp add: nths_def)
apply (subst filter_True)
 apply (auto simp: in_set_zip subset_iff)
done

lemma length_nths:
  "length (nths xs I) = card{i. i < length xs \<and> i \<in> I}"
  by(simp add: nths_def length_filter_conv_card cong:conj_cong)

lemma nths_shift_lemma_Suc:
  "map fst (filter (\<lambda>p. P(Suc(snd p))) (zip xs is)) =
   map fst (filter (\<lambda>p. P(snd p)) (zip xs (map Suc is)))"
proof (induct xs arbitrary: "is")
  case (Cons x xs "is")
  show ?case
    by (cases "is") (auto simp add: Cons.hyps)
qed simp

lemma nths_shift_lemma:
  "map fst (filter (\<lambda>p. snd p \<in> A) (zip xs [i..<i + length xs])) =
   map fst (filter (\<lambda>p. snd p + i \<in> A) (zip xs [0..<length xs]))"
by (induct xs rule: rev_induct) (simp_all add: add.commute)

lemma nths_append:
  "nths (l @ l') A = nths l A @ nths l' {j. j + length l \<in> A}"
  unfolding nths_def
proof (induct l' rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by (simp add: upt_add_eq_append[of 0] nths_shift_lemma add.commute)
qed auto

lemma nths_Cons:
  "nths (x # l) A = (if 0 \<in> A then [x] else []) @ nths l {j. Suc j \<in> A}"
proof (induct l rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by (simp flip: append_Cons add: nths_append)
qed (auto simp: nths_def)

lemma nths_map: "nths (map f xs) I = map f (nths xs I)"
  by(induction xs arbitrary: I) (simp_all add: nths_Cons)

lemma set_nths: "set(nths xs I) = {xs!i|i. i<size xs \<and> i \<in> I}"
  by (induct xs arbitrary: I) (auto simp: nths_Cons nth_Cons split:nat.split dest!: gr0_implies_Suc)

lemma set_nths_subset: "set(nths xs I) \<subseteq> set xs"
  by(auto simp add:set_nths)

lemma notin_set_nthsI[simp]: "x \<notin> set xs \<Longrightarrow> x \<notin> set(nths xs I)"
  by(auto simp add:set_nths)

lemma in_set_nthsD: "x \<in> set(nths xs I) \<Longrightarrow> x \<in> set xs"
  by(auto simp add:set_nths)

lemma nths_singleton [simp]: "nths [x] A = (if 0 \<in> A then [x] else [])"
  by (simp add: nths_Cons)

lemma distinct_nthsI[simp]: "distinct xs \<Longrightarrow> distinct (nths xs I)"
  by (induct xs arbitrary: I) (auto simp: nths_Cons)

lemma nths_upt_eq_take [simp]: "nths l {..<n} = take n l"
  by (induct l rule: rev_induct) (simp_all split: nat_diff_split add: nths_append)

lemma nths_nths: "nths (nths xs A) B = nths xs {i \<in> A. \<exists>j \<in> B. card {i' \<in> A. i' < i} = j}"
  by (induction xs arbitrary: A B) (auto simp add: nths_Cons card_less_Suc card_less_Suc2)

lemma drop_eq_nths: "drop n xs = nths xs {i. i \<ge> n}"
  by (induction xs arbitrary: n) (auto simp add: nths_Cons nths_all drop_Cons' intro: arg_cong2[where f=nths, OF refl])

lemma nths_drop: "nths (drop n xs) I = nths xs ((+) n ` I)"
by(force simp: drop_eq_nths nths_nths simp flip: atLeastLessThan_iff
         intro: arg_cong2[where f=nths, OF refl])

lemma filter_eq_nths: "filter P xs = nths xs {i. i<length xs \<and> P(xs!i)}"
  by(induction xs) (auto simp: nths_Cons)

lemma filter_in_nths:
  "distinct xs \<Longrightarrow> filter (%x. x \<in> set (nths xs s)) xs = nths xs s"
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  then have "\<forall>x. x \<in> set xs \<longrightarrow> x \<noteq> a" by auto
  with Cons show ?case by(simp add: nths_Cons cong:filter_cong)
qed


subsubsection \<open>\<^const>\<open>subseqs\<close> and \<^const>\<open>List.n_lists\<close>\<close>

lemma length_subseqs: "length (subseqs xs) = 2 ^ length xs"
  by (induct xs) (simp_all add: Let_def)

lemma subseqs_powset: "set ` set (subseqs xs) = Pow (set xs)"
proof -
  have aux: "\<And>x A. set ` Cons x ` A = insert x ` set ` A"
    by (auto simp add: image_def)
  have "set (map set (subseqs xs)) = Pow (set xs)"
    by (induct xs) (simp_all add: aux Let_def Pow_insert Un_commute comp_def del: map_map)
  then show ?thesis by simp
qed

lemma distinct_set_subseqs:
  assumes "distinct xs"
  shows "distinct (map set (subseqs xs))"
proof (rule card_distinct)
  have "finite (set xs)" ..
  then have "card (Pow (set xs)) = 2 ^ card (set xs)"
    by (rule card_Pow)
  with assms distinct_card [of xs] have "card (Pow (set xs)) = 2 ^ length xs"
    by simp
  then show "card (set (map set (subseqs xs))) = length (map set (subseqs xs))"
    by (simp add: subseqs_powset length_subseqs)
qed

lemma n_lists_Nil [simp]: "List.n_lists n [] = (if n = 0 then [[]] else [])"
  by (induct n) simp_all

lemma length_n_lists_elem: "ys \<in> set (List.n_lists n xs) \<Longrightarrow> length ys = n"
  by (induct n arbitrary: ys) auto

lemma set_n_lists: "set (List.n_lists n xs) = {ys. length ys = n \<and> set ys \<subseteq> set xs}"
proof (rule set_eqI)
  fix ys :: "'a list"
  show "ys \<in> set (List.n_lists n xs) \<longleftrightarrow> ys \<in> {ys. length ys = n \<and> set ys \<subseteq> set xs}"
  proof -
    have "ys \<in> set (List.n_lists n xs) \<Longrightarrow> length ys = n"
      by (induct n arbitrary: ys) auto
    moreover have "\<And>x. ys \<in> set (List.n_lists n xs) \<Longrightarrow> x \<in> set ys \<Longrightarrow> x \<in> set xs"
      by (induct n arbitrary: ys) auto
    moreover have "set ys \<subseteq> set xs \<Longrightarrow> ys \<in> set (List.n_lists (length ys) xs)"
      by (induct ys) auto
    ultimately show ?thesis by auto
  qed
qed

lemma subseqs_refl: "xs \<in> set (subseqs xs)"
  by (induct xs) (simp_all add: Let_def)

lemma subset_subseqs: "X \<subseteq> set xs \<Longrightarrow> X \<in> set ` set (subseqs xs)"
  unfolding subseqs_powset by simp

lemma Cons_in_subseqsD: "y # ys \<in> set (subseqs xs) \<Longrightarrow> ys \<in> set (subseqs xs)"
  by (induct xs) (auto simp: Let_def)

lemma subseqs_distinctD: "\<lbrakk> ys \<in> set (subseqs xs); distinct xs \<rbrakk> \<Longrightarrow> distinct ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs ys)
  then show ?case
    by (auto simp: Let_def) (metis Pow_iff contra_subsetD image_eqI subseqs_powset)
qed simp


subsubsection \<open>\<^const>\<open>splice\<close>\<close>

lemma splice_Nil2 [simp]: "splice xs [] = xs"
  by (cases xs) simp_all

lemma length_splice[simp]: "length(splice xs ys) = length xs + length ys"
  by (induct xs ys rule: splice.induct) auto

lemma split_Nil_iff[simp]: "splice xs ys = [] \<longleftrightarrow> xs = [] \<and> ys = []"
  by (induct xs ys rule: splice.induct) auto

lemma splice_replicate[simp]: "splice (replicate m x) (replicate n x) = replicate (m+n) x"
proof (induction "replicate m x" "replicate n x" arbitrary: m n rule: splice.induct)
  case (2 x xs)
  then show ?case 
    by (auto simp add: Cons_replicate_eq dest: gr0_implies_Suc)
qed auto

subsubsection \<open>\<^const>\<open>shuffles\<close>\<close>

lemma shuffles_commutes: "shuffles xs ys = shuffles ys xs"
by (induction xs ys rule: shuffles.induct) (simp_all add: Un_commute)

lemma Nil_in_shuffles[simp]: "[] \<in> shuffles xs ys \<longleftrightarrow> xs = [] \<and> ys = []"
  by (induct xs ys rule: shuffles.induct) auto

lemma shufflesE:
  "zs \<in> shuffles xs ys \<Longrightarrow>
    (zs = xs \<Longrightarrow> ys = [] \<Longrightarrow> P) \<Longrightarrow>
    (zs = ys \<Longrightarrow> xs = [] \<Longrightarrow> P) \<Longrightarrow>
    (\<And>x xs' z zs'. xs = x # xs' \<Longrightarrow> zs = z # zs' \<Longrightarrow> x = z \<Longrightarrow> zs' \<in> shuffles xs' ys \<Longrightarrow> P) \<Longrightarrow>
    (\<And>y ys' z zs'. ys = y # ys' \<Longrightarrow> zs = z # zs' \<Longrightarrow> y = z \<Longrightarrow> zs' \<in> shuffles xs ys' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct xs ys rule: shuffles.induct) auto

lemma Cons_in_shuffles_iff:
  "z # zs \<in> shuffles xs ys \<longleftrightarrow>
    (xs \<noteq> [] \<and> hd xs = z \<and> zs \<in> shuffles (tl xs) ys \<or>
     ys \<noteq> [] \<and> hd ys = z \<and> zs \<in> shuffles xs (tl ys))"
  by (induct xs ys rule: shuffles.induct) auto

lemma splice_in_shuffles [simp, intro]: "splice xs ys \<in> shuffles xs ys"
  by (induction xs ys rule: splice.induct) (simp_all add: Cons_in_shuffles_iff shuffles_commutes)

lemma Nil_in_shufflesI: "xs = [] \<Longrightarrow> ys = [] \<Longrightarrow> [] \<in> shuffles xs ys"
  by simp

lemma Cons_in_shuffles_leftI: "zs \<in> shuffles xs ys \<Longrightarrow> z # zs \<in> shuffles (z # xs) ys"
  by (cases ys) auto

lemma Cons_in_shuffles_rightI: "zs \<in> shuffles xs ys \<Longrightarrow> z # zs \<in> shuffles xs (z # ys)"
  by (cases xs) auto

lemma finite_shuffles [simp, intro]: "finite (shuffles xs ys)"
  by (induction xs ys rule: shuffles.induct) simp_all

lemma length_shuffles: "zs \<in> shuffles xs ys \<Longrightarrow> length zs = length xs + length ys"
  by (induction xs ys arbitrary: zs rule: shuffles.induct) auto

lemma set_shuffles: "zs \<in> shuffles xs ys \<Longrightarrow> set zs = set xs \<union> set ys"
  by (induction xs ys arbitrary: zs rule: shuffles.induct) auto

lemma distinct_disjoint_shuffles:
  assumes "distinct xs" "distinct ys" "set xs \<inter> set ys = {}" "zs \<in> shuffles xs ys"
  shows   "distinct zs"
using assms
proof (induction xs ys arbitrary: zs rule: shuffles.induct)
  case (3 x xs y ys)
  show ?case
  proof (cases zs)
    case (Cons z zs')
    with "3.prems" and "3.IH"[of zs'] show ?thesis by (force dest: set_shuffles)
  qed simp_all
qed simp_all

lemma Cons_shuffles_subset1: "(#) x ` shuffles xs ys \<subseteq> shuffles (x # xs) ys"
  by (cases ys) auto

lemma Cons_shuffles_subset2: "(#) y ` shuffles xs ys \<subseteq> shuffles xs (y # ys)"
  by (cases xs) auto

lemma filter_shuffles:
  "filter P ` shuffles xs ys = shuffles (filter P xs) (filter P ys)"
proof -
  have *: "filter P ` (#) x ` A = (if P x then (#) x ` filter P ` A else filter P ` A)" for x A
    by (auto simp: image_image)
  show ?thesis
  by (induction xs ys rule: shuffles.induct)
     (simp_all split: if_splits add: image_Un * Un_absorb1 Un_absorb2
           Cons_shuffles_subset1 Cons_shuffles_subset2)
qed

lemma filter_shuffles_disjoint1:
  assumes "set xs \<inter> set ys = {}" "zs \<in> shuffles xs ys"
  shows   "filter (\<lambda>x. x \<in> set xs) zs = xs" (is "filter ?P _ = _")
    and   "filter (\<lambda>x. x \<notin> set xs) zs = ys" (is "filter ?Q _ = _")
  using assms
proof -
  from assms have "filter ?P zs \<in> filter ?P ` shuffles xs ys" by blast
  also have "filter ?P ` shuffles xs ys = shuffles (filter ?P xs) (filter ?P ys)"
    by (rule filter_shuffles)
  also have "filter ?P xs = xs" by (rule filter_True) simp_all
  also have "filter ?P ys = []" by (rule filter_False) (insert assms(1), auto)
  also have "shuffles xs [] = {xs}" by simp
  finally show "filter ?P zs = xs" by simp
next
  from assms have "filter ?Q zs \<in> filter ?Q ` shuffles xs ys" by blast
  also have "filter ?Q ` shuffles xs ys = shuffles (filter ?Q xs) (filter ?Q ys)"
    by (rule filter_shuffles)
  also have "filter ?Q ys = ys" by (rule filter_True) (insert assms(1), auto)
  also have "filter ?Q xs = []" by (rule filter_False) (insert assms(1), auto)
  also have "shuffles [] ys = {ys}" by simp
  finally show "filter ?Q zs = ys" by simp
qed

lemma filter_shuffles_disjoint2:
  assumes "set xs \<inter> set ys = {}" "zs \<in> shuffles xs ys"
  shows   "filter (\<lambda>x. x \<in> set ys) zs = ys" "filter (\<lambda>x. x \<notin> set ys) zs = xs"
  using filter_shuffles_disjoint1[of ys xs zs] assms
  by (simp_all add: shuffles_commutes Int_commute)

lemma partition_in_shuffles:
  "xs \<in> shuffles (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
proof (induction xs)
  case (Cons x xs)
  show ?case
  proof (cases "P x")
    case True
    hence "x # xs \<in> (#) x ` shuffles (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
      by (intro imageI Cons.IH)
    also have "\<dots> \<subseteq> shuffles (filter P (x # xs)) (filter (\<lambda>x. \<not>P x) (x # xs))"
      by (simp add: True Cons_shuffles_subset1)
    finally show ?thesis .
  next
    case False
    hence "x # xs \<in> (#) x ` shuffles (filter P xs) (filter (\<lambda>x. \<not>P x) xs)"
      by (intro imageI Cons.IH)
    also have "\<dots> \<subseteq> shuffles (filter P (x # xs)) (filter (\<lambda>x. \<not>P x) (x # xs))"
      by (simp add: False Cons_shuffles_subset2)
    finally show ?thesis .
  qed
qed auto

lemma inv_image_partition:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x" "\<And>y. y \<in> set ys \<Longrightarrow> \<not>P y"
  shows   "partition P -` {(xs, ys)} = shuffles xs ys"
proof (intro equalityI subsetI)
  fix zs assume zs: "zs \<in> shuffles xs ys"
  hence [simp]: "set zs = set xs \<union> set ys" by (rule set_shuffles)
  from assms have "filter P zs = filter (\<lambda>x. x \<in> set xs) zs"
                  "filter (\<lambda>x. \<not>P x) zs = filter (\<lambda>x. x \<in> set ys) zs"
    by (intro filter_cong refl; force)+
  moreover from assms have "set xs \<inter> set ys = {}" by auto
  ultimately show "zs \<in> partition P -` {(xs, ys)}" using zs
    by (simp add: o_def filter_shuffles_disjoint1 filter_shuffles_disjoint2)
next
  fix zs assume "zs \<in> partition P -` {(xs, ys)}"
  thus "zs \<in> shuffles xs ys" using partition_in_shuffles[of zs] by (auto simp: o_def)
qed


subsubsection \<open>Transpose\<close>

function transpose where
"transpose []             = []" |
"transpose ([]     # xss) = transpose xss" |
"transpose ((x#xs) # xss) =
  (x # [h. (h#t) \<leftarrow> xss]) # transpose (xs # [t. (h#t) \<leftarrow> xss])"
by pat_completeness auto

lemma transpose_aux_filter_head:
  "concat (map (case_list [] (\<lambda>h t. [h])) xss) =
  map (\<lambda>xs. hd xs) (filter (\<lambda>ys. ys \<noteq> []) xss)"
  by (induct xss) (auto split: list.split)

lemma transpose_aux_filter_tail:
  "concat (map (case_list [] (\<lambda>h t. [t])) xss) =
  map (\<lambda>xs. tl xs) (filter (\<lambda>ys. ys \<noteq> []) xss)"
  by (induct xss) (auto split: list.split)

lemma transpose_aux_max:
  "max (Suc (length xs)) (foldr (\<lambda>xs. max (length xs)) xss 0) =
  Suc (max (length xs) (foldr (\<lambda>x. max (length x - Suc 0)) (filter (\<lambda>ys. ys \<noteq> []) xss) 0))"
  (is "max _ ?foldB = Suc (max _ ?foldA)")
proof (cases "(filter (\<lambda>ys. ys \<noteq> []) xss) = []")
  case True
  hence "foldr (\<lambda>xs. max (length xs)) xss 0 = 0"
  proof (induct xss)
    case (Cons x xs)
    then have "x = []" by (cases x) auto
    with Cons show ?case by auto
  qed simp
  thus ?thesis using True by simp
next
  case False

  have foldA: "?foldA = foldr (\<lambda>x. max (length x)) (filter (\<lambda>ys. ys \<noteq> []) xss) 0 - 1"
    by (induct xss) auto
  have foldB: "?foldB = foldr (\<lambda>x. max (length x)) (filter (\<lambda>ys. ys \<noteq> []) xss) 0"
    by (induct xss) auto

  have "0 < ?foldB"
  proof -
    from False
    obtain z zs where zs: "(filter (\<lambda>ys. ys \<noteq> []) xss) = z#zs" by (auto simp: neq_Nil_conv)
    hence "z \<in> set (filter (\<lambda>ys. ys \<noteq> []) xss)" by auto
    hence "z \<noteq> []" by auto
    thus ?thesis
      unfolding foldB zs
      by (auto simp: max_def intro: less_le_trans)
  qed
  thus ?thesis
    unfolding foldA foldB max_Suc_Suc[symmetric]
    by simp
qed

termination transpose
  by (relation "measure (\<lambda>xs. foldr (\<lambda>xs. max (length xs)) xs 0 + length xs)")
     (auto simp: transpose_aux_filter_tail foldr_map comp_def transpose_aux_max less_Suc_eq_le)

lemma transpose_empty: "(transpose xs = []) \<longleftrightarrow> (\<forall>x \<in> set xs. x = [])"
  by (induct rule: transpose.induct) simp_all

lemma length_transpose:
  fixes xs :: "'a list list"
  shows "length (transpose xs) = foldr (\<lambda>xs. max (length xs)) xs 0"
  by (induct rule: transpose.induct)
    (auto simp: transpose_aux_filter_tail foldr_map comp_def transpose_aux_max
                max_Suc_Suc[symmetric] simp del: max_Suc_Suc)

lemma nth_transpose:
  fixes xs :: "'a list list"
  assumes "i < length (transpose xs)"
  shows "transpose xs ! i = map (\<lambda>xs. xs ! i) (filter (\<lambda>ys. i < length ys) xs)"
using assms proof (induct arbitrary: i rule: transpose.induct)
  case (3 x xs xss)
  define XS where "XS = (x # xs) # xss"
  hence [simp]: "XS \<noteq> []" by auto
  thus ?case
  proof (cases i)
    case 0
    thus ?thesis by (simp add: transpose_aux_filter_head hd_conv_nth)
  next
    case (Suc j)
    have *: "\<And>xss. xs # map tl xss = map tl ((x#xs)#xss)" by simp
    have **: "\<And>xss. (x#xs) # filter (\<lambda>ys. ys \<noteq> []) xss = filter (\<lambda>ys. ys \<noteq> []) ((x#xs)#xss)" by simp
    { fix x have "Suc j < length x \<longleftrightarrow> x \<noteq> [] \<and> j < length x - Suc 0"
      by (cases x) simp_all
    } note *** = this

    have j_less: "j < length (transpose (xs # concat (map (case_list [] (\<lambda>h t. [t])) xss)))"
      using "3.prems" by (simp add: transpose_aux_filter_tail length_transpose Suc)

    show ?thesis
      unfolding transpose.simps \<open>i = Suc j\<close> nth_Cons_Suc "3.hyps"[OF j_less]
      apply (auto simp: transpose_aux_filter_tail filter_map comp_def length_transpose * ** *** XS_def[symmetric])
      by (simp add: nth_tl)
  qed
qed simp_all

lemma transpose_map_map:
  "transpose (map (map f) xs) = map (map f) (transpose xs)"
proof (rule nth_equalityI)
  have [simp]: "length (transpose (map (map f) xs)) = length (transpose xs)"
    by (simp add: length_transpose foldr_map comp_def)
  show "length (transpose (map (map f) xs)) = length (map (map f) (transpose xs))" by simp

  fix i assume "i < length (transpose (map (map f) xs))"
  thus "transpose (map (map f) xs) ! i = map (map f) (transpose xs) ! i"
    by (simp add: nth_transpose filter_map comp_def)
qed

subsubsection \<open>\<^const>\<open>min\<close> and \<^const>\<open>arg_min\<close>\<close>

lemma min_list_Min: "xs \<noteq> [] \<Longrightarrow> min_list xs = Min (set xs)"
  by (induction xs rule: induct_list012)(auto)

lemma f_arg_min_list_f: "xs \<noteq> [] \<Longrightarrow> f (arg_min_list f xs) = Min (f ` (set xs))"
  by(induction f xs rule: arg_min_list.induct) (auto simp: min_def intro!: antisym)

lemma arg_min_list_in: "xs \<noteq> [] \<Longrightarrow> arg_min_list f xs \<in> set xs"
  by(induction xs rule: induct_list012) (auto simp: Let_def)


subsubsection \<open>(In)finiteness\<close>

lemma finite_maxlen:
  "finite (M::'a list set) \<Longrightarrow> \<exists>n. \<forall>s\<in>M. size s < n"
proof (induct rule: finite.induct)
  case emptyI show ?case by simp
next
  case (insertI M xs)
  then obtain n where "\<forall>s\<in>M. length s < n" by blast
  hence "\<forall>s\<in>insert xs M. size s < max n (size xs) + 1" by auto
  thus ?case ..
qed

lemma lists_length_Suc_eq:
  "{xs. set xs \<subseteq> A \<and> length xs = Suc n} =
    (\<lambda>(xs, n). n#xs) ` ({xs. set xs \<subseteq> A \<and> length xs = n} \<times> A)"
  by (auto simp: length_Suc_conv)

lemma
  assumes "finite A"
  shows finite_lists_length_eq: "finite {xs. set xs \<subseteq> A \<and> length xs = n}"
  and card_lists_length_eq: "card {xs. set xs \<subseteq> A \<and> length xs = n} = (card A)^n"
  using \<open>finite A\<close>
  by (induct n)
     (auto simp: card_image inj_split_Cons lists_length_Suc_eq cong: conj_cong)

lemma finite_lists_length_le:
  assumes "finite A" shows "finite {xs. set xs \<subseteq> A \<and> length xs \<le> n}"
 (is "finite ?S")
proof-
  have "?S = (\<Union>n\<in>{0..n}. {xs. set xs \<subseteq> A \<and> length xs = n})" by auto
  thus ?thesis by (auto intro!: finite_lists_length_eq[OF \<open>finite A\<close>] simp only:)
qed

lemma card_lists_length_le:
  assumes "finite A" shows "card {xs. set xs \<subseteq> A \<and> length xs \<le> n} = (\<Sum>i\<le>n. card A^i)"
proof -
  have "(\<Sum>i\<le>n. card A^i) = card (\<Union>i\<le>n. {xs. set xs \<subseteq> A \<and> length xs = i})"
    using \<open>finite A\<close>
    by (subst card_UN_disjoint)
       (auto simp add: card_lists_length_eq finite_lists_length_eq)
  also have "(\<Union>i\<le>n. {xs. set xs \<subseteq> A \<and> length xs = i}) = {xs. set xs \<subseteq> A \<and> length xs \<le> n}"
    by auto
  finally show ?thesis by simp
qed

lemma finite_lists_distinct_length_eq [intro]:
  assumes "finite A"
  shows "finite {xs. length xs = n \<and> distinct xs \<and> set xs \<subseteq> A}" (is "finite ?S")
proof -
  have "finite {xs. set xs \<subseteq> A \<and> length xs = n}"
    using \<open>finite A\<close> by (rule finite_lists_length_eq)
  moreover have "?S \<subseteq> {xs. set xs \<subseteq> A \<and> length xs = n}" by auto
  ultimately show ?thesis using finite_subset by auto
qed

lemma card_lists_distinct_length_eq:
  assumes "finite A" "k \<le> card A"
  shows "card {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> A} = \<Prod>{card A - k + 1 .. card A}"
using assms
proof (induct k)
  case 0
  then have "{xs. length xs = 0 \<and> distinct xs \<and> set xs \<subseteq> A} = {[]}" by auto
  then show ?case by simp
next
  case (Suc k)
  let "?k_list" = "\<lambda>k xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> A"
  have inj_Cons: "\<And>A. inj_on (\<lambda>(xs, n). n # xs) A"  by (rule inj_onI) auto

  from Suc have "k \<le> card A" by simp
  moreover note \<open>finite A\<close>
  moreover have "finite {xs. ?k_list k xs}"
    by (rule finite_subset) (use finite_lists_length_eq[OF \<open>finite A\<close>, of k] in auto)
  moreover have "\<And>i j. i \<noteq> j \<longrightarrow> {i} \<times> (A - set i) \<inter> {j} \<times> (A - set j) = {}"
    by auto
  moreover have "\<And>i. i \<in> {xs. ?k_list k xs} \<Longrightarrow> card (A - set i) = card A - k"
    by (simp add: card_Diff_subset distinct_card)
  moreover have "{xs. ?k_list (Suc k) xs} =
      (\<lambda>(xs, n). n#xs) ` \<Union>((\<lambda>xs. {xs} \<times> (A - set xs)) ` {xs. ?k_list k xs})"
    by (auto simp: length_Suc_conv)
  moreover have "Suc (card A - Suc k) = card A - k" using Suc.prems by simp
  then have "(card A - k) * \<Prod>{Suc (card A - k)..card A} = \<Prod>{Suc (card A - Suc k)..card A}"
    by (subst prod.insert[symmetric]) (simp add: atLeastAtMost_insertL)+
  ultimately show ?case
    by (simp add: card_image inj_Cons card_UN_disjoint Suc.hyps algebra_simps)
qed

lemma card_lists_distinct_length_eq':
  assumes "k < card A"
  shows "card {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> A} = \<Prod>{card A - k + 1 .. card A}"
proof -
  from \<open>k < card A\<close> have "finite A" and "k \<le> card A" using card.infinite by force+
  from this show ?thesis by (rule card_lists_distinct_length_eq)
qed

lemma infinite_UNIV_listI: "\<not> finite(UNIV::'a list set)"
  by (metis UNIV_I finite_maxlen length_replicate less_irrefl)

lemma same_length_different: 
  assumes "xs \<noteq> ys" and "length xs = length ys"
  shows "\<exists>pre x xs' y ys'. x\<noteq>y \<and> xs = pre @ [x] @ xs' \<and> ys = pre @ [y] @ ys'"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then obtain z zs where ys: "ys = Cons z zs"
    by (metis length_Suc_conv)
  show ?case
  proof (cases "x=z")
    case True
    then have "xs \<noteq> zs" "length xs = length zs"
      using Cons.prems ys by auto
    then obtain pre u xs' v ys' where "u\<noteq>v" and xs: "xs = pre @ [u] @ xs'" and zs: "zs = pre @ [v] @ys'"
      using Cons.IH by meson
    then have "x # xs = (z#pre) @ [u] @ xs' \<and> ys = (z#pre) @ [v] @ ys'"
      by (simp add: True ys)
    with \<open>u\<noteq>v\<close> show ?thesis
      by blast
  next
    case False
    then have "x # xs = [] @ [x] @ xs \<and> ys = [] @ [z] @ zs"
      by (simp add: ys)
    then show ?thesis
      using False by blast
  qed
qed

subsection \<open>Sorting\<close>

subsubsection \<open>\<^const>\<open>sorted_wrt\<close>\<close>

text \<open>Sometimes the second equation in the definition of \<^const>\<open>sorted_wrt\<close> is too aggressive
because it relates each list element to \emph{all} its successors. Then this equation
should be removed and \<open>sorted_wrt2_simps\<close> should be added instead.\<close>

lemma sorted_wrt1: "sorted_wrt P [x] = True"
by(simp)

lemma sorted_wrt2: "transp P \<Longrightarrow> sorted_wrt P (x # y # zs) = (P x y \<and> sorted_wrt P (y # zs))"
proof (induction zs arbitrary: x y)
  case (Cons z zs)
  then show ?case
    by simp (meson transpD)+
qed auto

lemmas sorted_wrt2_simps = sorted_wrt1 sorted_wrt2

lemma sorted_wrt_true [simp]:
  "sorted_wrt (\<lambda>_ _. True) xs"
by (induction xs) simp_all

lemma sorted_wrt_append:
  "sorted_wrt P (xs @ ys) \<longleftrightarrow>
  sorted_wrt P xs \<and> sorted_wrt P ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. P x y)"
by (induction xs) auto

lemma sorted_wrt_map:
  "sorted_wrt R (map f xs) = sorted_wrt (\<lambda>x y. R (f x) (f y)) xs"
by (induction xs) simp_all

lemma
  assumes "sorted_wrt f xs"
  shows sorted_wrt_take: "sorted_wrt f (take n xs)"
  and   sorted_wrt_drop: "sorted_wrt f (drop n xs)"
proof -
  from assms have "sorted_wrt f (take n xs @ drop n xs)" by simp
  thus "sorted_wrt f (take n xs)" and "sorted_wrt f (drop n xs)"
    unfolding sorted_wrt_append by simp_all
qed

lemma sorted_wrt_filter:
  "sorted_wrt f xs \<Longrightarrow> sorted_wrt f (filter P xs)"
by (induction xs) auto

lemma sorted_wrt_rev:
  "sorted_wrt P (rev xs) = sorted_wrt (\<lambda>x y. P y x) xs"
by (induction xs) (auto simp add: sorted_wrt_append)

lemma sorted_wrt_mono_rel:
  "(\<And>x y. \<lbrakk> x \<in> set xs; y \<in> set xs; P x y \<rbrakk> \<Longrightarrow> Q x y) \<Longrightarrow> sorted_wrt P xs \<Longrightarrow> sorted_wrt Q xs"
by(induction xs)(auto)

lemma sorted_wrt01: "length xs \<le> 1 \<Longrightarrow> sorted_wrt P xs"
by(auto simp: le_Suc_eq length_Suc_conv)

lemma sorted_wrt_iff_nth_less:
  "sorted_wrt P xs = (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> P (xs ! i) (xs ! j))"
  by (induction xs) (auto simp add: in_set_conv_nth Ball_def nth_Cons split: nat.split)

lemma sorted_wrt_nth_less:
  "\<lbrakk> sorted_wrt P xs; i < j; j < length xs \<rbrakk> \<Longrightarrow> P (xs ! i) (xs ! j)"
by(auto simp: sorted_wrt_iff_nth_less)

lemma sorted_wrt_iff_nth_Suc_transp: assumes "transp P"
  shows "sorted_wrt P xs \<longleftrightarrow> (\<forall>i.  Suc i < length xs \<longrightarrow> P (xs!i) (xs!(Suc i)))" (is "?L = ?R")
proof
  assume ?L
  thus ?R
    by (simp add: sorted_wrt_iff_nth_less) 
next
  assume ?R
  have "i < j \<Longrightarrow> j < length xs \<Longrightarrow> P (xs ! i) (xs ! j)" for i j
    by(induct i j rule: less_Suc_induct)(simp add: \<open>?R\<close>, meson assms transpE transp_less)
  thus ?L
    by (simp add: sorted_wrt_iff_nth_less)
qed

lemma sorted_wrt_upt[simp]: "sorted_wrt (<) [m..<n]"
by(induction n) (auto simp: sorted_wrt_append)

lemma sorted_wrt_upto[simp]: "sorted_wrt (<) [i..j]"
proof(induct i j rule:upto.induct)
  case (1 i j)
  from this show ?case
    unfolding upto.simps[of i j] by auto
qed

text \<open>Each element is greater or equal to its index:\<close>

lemma sorted_wrt_less_idx:
  "sorted_wrt (<) ns \<Longrightarrow> i < length ns \<Longrightarrow> i \<le> ns!i"
proof (induction ns arbitrary: i rule: rev_induct)
  case Nil thus ?case by simp
next
  case snoc
  thus ?case
    by (auto simp: nth_append sorted_wrt_append)
       (metis less_antisym not_less nth_mem)
qed


subsubsection \<open>\<^const>\<open>sorted\<close>\<close>

context linorder
begin

text \<open>Sometimes the second equation in the definition of \<^const>\<open>sorted\<close> is too aggressive
because it relates each list element to \emph{all} its successors. Then this equation
should be removed and \<open>sorted2_simps\<close> should be added instead.
Executable code is one such use case.\<close>

lemma sorted1: "sorted [x] = True"
by simp

lemma sorted2: "sorted (x # y # zs) = (x \<le> y \<and> sorted (y # zs))"
by(induction zs) auto

lemmas sorted2_simps = sorted1 sorted2

lemmas [code] = sorted.simps(1) sorted2_simps

lemma sorted_append:
  "sorted (xs@ys) = (sorted xs \<and> sorted ys \<and> (\<forall>x \<in> set xs. \<forall>y \<in> set ys. x\<le>y))"
by (simp add: sorted_sorted_wrt sorted_wrt_append)

lemma sorted_map:
  "sorted (map f xs) = sorted_wrt (\<lambda>x y. f x \<le> f y) xs"
by (simp add: sorted_sorted_wrt sorted_wrt_map)

lemma sorted01: "length xs \<le> 1 \<Longrightarrow> sorted xs"
by (simp add: sorted_sorted_wrt sorted_wrt01)

lemma sorted_tl:
  "sorted xs \<Longrightarrow> sorted (tl xs)"
by (cases xs) (simp_all)

lemma sorted_iff_nth_mono_less:
  "sorted xs = (\<forall>i j. i < j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j)"
by (simp add: sorted_sorted_wrt sorted_wrt_iff_nth_less)

lemma sorted_iff_nth_mono:
  "sorted xs = (\<forall>i j. i \<le> j \<longrightarrow> j < length xs \<longrightarrow> xs ! i \<le> xs ! j)"
by (auto simp: sorted_iff_nth_mono_less nat_less_le)

lemma sorted_nth_mono:
  "sorted xs \<Longrightarrow> i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> xs!i \<le> xs!j"
by (auto simp: sorted_iff_nth_mono)

lemma sorted_iff_nth_Suc: 
  "sorted xs \<longleftrightarrow> (\<forall>i.  Suc i < length xs \<longrightarrow> xs!i \<le> xs!(Suc i))"
by(simp add: sorted_sorted_wrt sorted_wrt_iff_nth_Suc_transp)

lemma sorted_rev_nth_mono:
  "sorted (rev xs) \<Longrightarrow> i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> xs!j \<le> xs!i"
using sorted_nth_mono[ of "rev xs" "length xs - j - 1" "length xs - i - 1"]
      rev_nth[of "length xs - i - 1" "xs"] rev_nth[of "length xs - j - 1" "xs"]
by auto

lemma sorted_rev_iff_nth_mono:
  "sorted (rev xs) \<longleftrightarrow> (\<forall> i j. i \<le> j \<longrightarrow> j < length xs \<longrightarrow> xs!j \<le> xs!i)" (is "?L = ?R")
proof
  assume ?L thus ?R
    by (blast intro: sorted_rev_nth_mono)
next
  assume ?R
  have "rev xs ! k \<le> rev xs ! l" if asms: "k \<le> l" "l < length(rev xs)" for k l
  proof -
    have "k < length xs"  "l < length xs"
      "length xs - Suc l \<le> length xs - Suc k" "length xs - Suc k < length xs"
      using asms by auto
    thus "rev xs ! k \<le> rev xs ! l"
      using \<open>?R\<close> \<open>k \<le> l\<close> unfolding rev_nth[OF \<open>k < length xs\<close>] rev_nth[OF \<open>l < length xs\<close>] by blast
  qed
  thus ?L by (simp add: sorted_iff_nth_mono)
qed

lemma sorted_rev_iff_nth_Suc: 
  "sorted (rev xs) \<longleftrightarrow> (\<forall>i.  Suc i < length xs \<longrightarrow> xs!(Suc i) \<le> xs!i)"
proof-
  interpret dual: linorder "(\<lambda>x y. y \<le> x)" "(\<lambda>x y. y < x)"
    using dual_linorder .
  show ?thesis
    using dual_linorder dual.sorted_iff_nth_Suc dual.sorted_iff_nth_mono 
    unfolding sorted_rev_iff_nth_mono by simp
qed

lemma sorted_map_remove1:
  "sorted (map f xs) \<Longrightarrow> sorted (map f (remove1 x xs))"
by (induct xs) (auto)

lemma sorted_remove1: "sorted xs \<Longrightarrow> sorted (remove1 a xs)"
using sorted_map_remove1 [of "\<lambda>x. x"] by simp

lemma sorted_butlast:
  assumes "xs \<noteq> []" and "sorted xs"
  shows "sorted (butlast xs)"
proof -
  from \<open>xs \<noteq> []\<close> obtain ys y where "xs = ys @ [y]"
    by (cases xs rule: rev_cases) auto
  with \<open>sorted xs\<close> show ?thesis by (simp add: sorted_append)
qed

lemma sorted_replicate [simp]: "sorted(replicate n x)"
by(induction n) (auto)

lemma sorted_remdups[simp]:
  "sorted xs \<Longrightarrow> sorted (remdups xs)"
by (induct xs) (auto)

lemma sorted_remdups_adj[simp]:
  "sorted xs \<Longrightarrow> sorted (remdups_adj xs)"
by (induct xs rule: remdups_adj.induct, simp_all split: if_split_asm)

lemma sorted_nths: "sorted xs \<Longrightarrow> sorted (nths xs I)"
by(induction xs arbitrary: I)(auto simp: nths_Cons)

lemma sorted_distinct_set_unique:
assumes "sorted xs" "distinct xs" "sorted ys" "distinct ys" "set xs = set ys"
shows "xs = ys"
proof -
  from assms have 1: "length xs = length ys" by (auto dest!: distinct_card)
  from assms show ?thesis
  proof(induct rule:list_induct2[OF 1])
    case 1 show ?case by simp
  next
    case (2 x xs y ys)
    then show ?case
      by (cases \<open>x = y\<close>) (auto simp add: insert_eq_iff)
  qed
qed

lemma map_sorted_distinct_set_unique:
  assumes "inj_on f (set xs \<union> set ys)"
  assumes "sorted (map f xs)" "distinct (map f xs)"
    "sorted (map f ys)" "distinct (map f ys)"
  assumes "set xs = set ys"
  shows "xs = ys"
proof -
  from assms have "map f xs = map f ys"
    by (simp add: sorted_distinct_set_unique)
  with \<open>inj_on f (set xs \<union> set ys)\<close> show "xs = ys"
    by (blast intro: map_inj_on)
qed

lemma
  assumes "sorted xs"
  shows sorted_take: "sorted (take n xs)"
  and sorted_drop: "sorted (drop n xs)"
proof -
  from assms have "sorted (take n xs @ drop n xs)" by simp
  then show "sorted (take n xs)" and "sorted (drop n xs)"
    unfolding sorted_append by simp_all
qed

lemma sorted_dropWhile: "sorted xs \<Longrightarrow> sorted (dropWhile P xs)"
  by (auto dest: sorted_drop simp add: dropWhile_eq_drop)

lemma sorted_takeWhile: "sorted xs \<Longrightarrow> sorted (takeWhile P xs)"
  by (subst takeWhile_eq_take) (auto dest: sorted_take)

lemma sorted_filter:
  "sorted (map f xs) \<Longrightarrow> sorted (map f (filter P xs))"
  by (induct xs) simp_all

lemma foldr_max_sorted:
  assumes "sorted (rev xs)"
  shows "foldr max xs y = (if xs = [] then y else max (xs ! 0) y)"
  using assms
proof (induct xs)
  case (Cons x xs)
  then have "sorted (rev xs)" using sorted_append by auto
  with Cons show ?case
    by (cases xs) (auto simp add: sorted_append max_def)
qed simp

lemma filter_equals_takeWhile_sorted_rev:
  assumes sorted: "sorted (rev (map f xs))"
  shows "filter (\<lambda>x. t < f x) xs = takeWhile (\<lambda> x. t < f x) xs"
    (is "filter ?P xs = ?tW")
proof (rule takeWhile_eq_filter[symmetric])
  let "?dW" = "dropWhile ?P xs"
  fix x assume "x \<in> set ?dW"
  then obtain i where i: "i < length ?dW" and nth_i: "x = ?dW ! i"
    unfolding in_set_conv_nth by auto
  hence "length ?tW + i < length (?tW @ ?dW)"
    unfolding length_append by simp
  hence i': "length (map f ?tW) + i < length (map f xs)" by simp
  have "(map f ?tW @ map f ?dW) ! (length (map f ?tW) + i) \<le>
        (map f ?tW @ map f ?dW) ! (length (map f ?tW) + 0)"
    using sorted_rev_nth_mono[OF sorted _ i', of "length ?tW"]
    unfolding map_append[symmetric] by simp
  hence "f x \<le> f (?dW ! 0)"
    unfolding nth_append_length_plus nth_i
    using i preorder_class.le_less_trans[OF le0 i] by simp
  also have "... \<le> t"
    using hd_dropWhile[of "?P" xs] le0[THEN preorder_class.le_less_trans, OF i]
    using hd_conv_nth[of "?dW"] by simp
  finally show "\<not> t < f x" by simp
qed

lemma sorted_map_same:
  "sorted (map f (filter (\<lambda>x. f x = g xs) xs))"
proof (induct xs arbitrary: g)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have "sorted (map f (filter (\<lambda>y. f y = (\<lambda>xs. f x) xs) xs))" .
  moreover from Cons have "sorted (map f (filter (\<lambda>y. f y = (g \<circ> Cons x) xs) xs))" .
  ultimately show ?case by simp_all
qed

lemma sorted_same:
  "sorted (filter (\<lambda>x. x = g xs) xs)"
using sorted_map_same [of "\<lambda>x. x"] by simp

end

lemma sorted_upt[simp]: "sorted [m..<n]"
by(simp add: sorted_sorted_wrt sorted_wrt_mono_rel[OF _ sorted_wrt_upt])

lemma sorted_upto[simp]: "sorted [m..n]"
by(simp add: sorted_sorted_wrt sorted_wrt_mono_rel[OF _ sorted_wrt_upto])


subsubsection \<open>Sorting functions\<close>

text\<open>Currently it is not shown that \<^const>\<open>sort\<close> returns a
permutation of its input because the nicest proof is via multisets,
which are not part of Main. Alternatively one could define a function
that counts the number of occurrences of an element in a list and use
that instead of multisets to state the correctness property.\<close>

context linorder
begin

lemma set_insort_key:
  "set (insort_key f x xs) = insert x (set xs)"
by (induct xs) auto

lemma length_insort [simp]:
  "length (insort_key f x xs) = Suc (length xs)"
by (induct xs) simp_all

lemma insort_key_left_comm:
  assumes "f x \<noteq> f y"
  shows "insort_key f y (insort_key f x xs) = insort_key f x (insort_key f y xs)"
by (induct xs) (auto simp add: assms dest: order.antisym)

lemma insort_left_comm:
  "insort x (insort y xs) = insort y (insort x xs)"
by (cases "x = y") (auto intro: insort_key_left_comm)

lemma comp_fun_commute_insort: "comp_fun_commute insort"
proof
qed (simp add: insort_left_comm fun_eq_iff)

lemma sort_key_simps [simp]:
  "sort_key f [] = []"
  "sort_key f (x#xs) = insort_key f x (sort_key f xs)"
by (simp_all add: sort_key_def)

lemma sort_key_conv_fold:
  assumes "inj_on f (set xs)"
  shows "sort_key f xs = fold (insort_key f) xs []"
proof -
  have "fold (insort_key f) (rev xs) = fold (insort_key f) xs"
  proof (rule fold_rev, rule ext)
    fix zs
    fix x y
    assume "x \<in> set xs" "y \<in> set xs"
    with assms have *: "f y = f x \<Longrightarrow> y = x" by (auto dest: inj_onD)
    have **: "x = y \<longleftrightarrow> y = x" by auto
    show "(insort_key f y \<circ> insort_key f x) zs = (insort_key f x \<circ> insort_key f y) zs"
      by (induct zs) (auto intro: * simp add: **)
  qed
  then show ?thesis by (simp add: sort_key_def foldr_conv_fold)
qed

lemma sort_conv_fold:
  "sort xs = fold insort xs []"
by (rule sort_key_conv_fold) simp

lemma length_sort[simp]: "length (sort_key f xs) = length xs"
by (induct xs, auto)

lemma set_sort[simp]: "set(sort_key f xs) = set xs"
by (induct xs) (simp_all add: set_insort_key)

lemma distinct_insort: "distinct (insort_key f x xs) = (x \<notin> set xs \<and> distinct xs)"
by(induct xs)(auto simp: set_insort_key)

lemma distinct_sort[simp]: "distinct (sort_key f xs) = distinct xs"
by (induct xs) (simp_all add: distinct_insort)

lemma sorted_insort_key: "sorted (map f (insort_key f x xs)) = sorted (map f xs)"
by (induct xs) (auto simp: set_insort_key)

lemma sorted_insort: "sorted (insort x xs) = sorted xs"
using sorted_insort_key [where f="\<lambda>x. x"] by simp

theorem sorted_sort_key [simp]: "sorted (map f (sort_key f xs))"
by (induct xs) (auto simp:sorted_insort_key)

theorem sorted_sort [simp]: "sorted (sort xs)"
using sorted_sort_key [where f="\<lambda>x. x"] by simp

lemma insort_not_Nil [simp]:
  "insort_key f a xs \<noteq> []"
by (induction xs) simp_all

lemma insort_is_Cons: "\<forall>x\<in>set xs. f a \<le> f x \<Longrightarrow> insort_key f a xs = a # xs"
by (cases xs) auto

lemma sorted_sort_id: "sorted xs \<Longrightarrow> sort xs = xs"
by (induct xs) (auto simp add: insort_is_Cons)

lemma insort_key_remove1:
  assumes "a \<in> set xs" and "sorted (map f xs)" and "hd (filter (\<lambda>x. f a = f x) xs) = a"
  shows "insort_key f a (remove1 a xs) = xs"
using assms proof (induct xs)
  case (Cons x xs)
  then show ?case
  proof (cases "x = a")
    case False
    then have "f x \<noteq> f a" using Cons.prems by auto
    then have "f x < f a" using Cons.prems by auto
    with \<open>f x \<noteq> f a\<close> show ?thesis using Cons by (auto simp: insort_is_Cons)
  qed (auto simp: insort_is_Cons)
qed simp

lemma insort_remove1:
  assumes "a \<in> set xs" and "sorted xs"
  shows "insort a (remove1 a xs) = xs"
proof (rule insort_key_remove1)
  define n where "n = length (filter ((=) a) xs) - 1"
  from \<open>a \<in> set xs\<close> show "a \<in> set xs" .
  from \<open>sorted xs\<close> show "sorted (map (\<lambda>x. x) xs)" by simp
  from \<open>a \<in> set xs\<close> have "a \<in> set (filter ((=) a) xs)" by auto
  then have "set (filter ((=) a) xs) \<noteq> {}" by auto
  then have "filter ((=) a) xs \<noteq> []" by (auto simp only: set_empty)
  then have "length (filter ((=) a) xs) > 0" by simp
  then have n: "Suc n = length (filter ((=) a) xs)" by (simp add: n_def)
  moreover have "replicate (Suc n) a = a # replicate n a"
    by simp
  ultimately show "hd (filter ((=) a) xs) = a" by (simp add: replicate_length_filter)
qed

lemma finite_sorted_distinct_unique:
  assumes "finite A" shows "\<exists>!xs. set xs = A \<and> sorted xs \<and> distinct xs"
proof -
  obtain xs where "distinct xs" "A = set xs"
    using finite_distinct_list [OF assms] by metis
  then show ?thesis
    by (rule_tac a="sort xs" in ex1I) (auto simp: sorted_distinct_set_unique)
qed

lemma insort_insert_key_triv:
  "f x \<in> f ` set xs \<Longrightarrow> insort_insert_key f x xs = xs"
  by (simp add: insort_insert_key_def)

lemma insort_insert_triv:
  "x \<in> set xs \<Longrightarrow> insort_insert x xs = xs"
  using insort_insert_key_triv [of "\<lambda>x. x"] by simp

lemma insort_insert_insort_key:
  "f x \<notin> f ` set xs \<Longrightarrow> insort_insert_key f x xs = insort_key f x xs"
  by (simp add: insort_insert_key_def)

lemma insort_insert_insort:
  "x \<notin> set xs \<Longrightarrow> insort_insert x xs = insort x xs"
  using insort_insert_insort_key [of "\<lambda>x. x"] by simp

lemma set_insort_insert:
  "set (insort_insert x xs) = insert x (set xs)"
  by (auto simp add: insort_insert_key_def set_insort_key)

lemma distinct_insort_insert:
  assumes "distinct xs"
  shows "distinct (insort_insert_key f x xs)"
using assms by (induct xs) (auto simp add: insort_insert_key_def set_insort_key)

lemma sorted_insort_insert_key:
  assumes "sorted (map f xs)"
  shows "sorted (map f (insort_insert_key f x xs))"
  using assms by (simp add: insort_insert_key_def sorted_insort_key)

lemma sorted_insort_insert:
  assumes "sorted xs"
  shows "sorted (insort_insert x xs)"
  using assms sorted_insort_insert_key [of "\<lambda>x. x"] by simp

lemma filter_insort_triv:
  "\<not> P x \<Longrightarrow> filter P (insort_key f x xs) = filter P xs"
  by (induct xs) simp_all

lemma filter_insort:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort_key f x xs) = insort_key f x (filter P xs)"
  by (induct xs) (auto, subst insort_is_Cons, auto)

lemma filter_sort:
  "filter P (sort_key f xs) = sort_key f (filter P xs)"
  by (induct xs) (simp_all add: filter_insort_triv filter_insort)

lemma remove1_insort [simp]:
  "remove1 x (insort x xs) = xs"
  by (induct xs) simp_all

end

lemma sort_upt [simp]: "sort [m..<n] = [m..<n]"
by (rule sorted_sort_id) simp

lemma sort_upto [simp]: "sort [i..j] = [i..j]"
by (rule sorted_sort_id) simp

lemma sorted_find_Min:
  "sorted xs \<Longrightarrow> \<exists>x \<in> set xs. P x \<Longrightarrow> List.find P xs = Some (Min {x\<in>set xs. P x})"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) show ?case proof (cases "P x")
    case True
    with Cons show ?thesis by (auto intro: Min_eqI [symmetric])
  next
    case False then have "{y. (y = x \<or> y \<in> set xs) \<and> P y} = {y \<in> set xs. P y}"
      by auto
    with Cons False show ?thesis by (simp_all)
  qed
qed

lemma sorted_enumerate [simp]: "sorted (map fst (enumerate n xs))"
by (simp add: enumerate_eq_zip)

text \<open>Stability of \<^const>\<open>sort_key\<close>:\<close>

lemma sort_key_stable: "filter (\<lambda>y. f y = k) (sort_key f xs) = filter (\<lambda>y. f y = k) xs"
by (induction xs) (auto simp: filter_insort insort_is_Cons filter_insort_triv)

corollary stable_sort_key_sort_key: "stable_sort_key sort_key"
by(simp add: stable_sort_key_def sort_key_stable)

lemma sort_key_const: "sort_key (\<lambda>x. c) xs = xs"
by (metis (mono_tags) filter_True sort_key_stable)


subsubsection \<open>\<^const>\<open>transpose\<close> on sorted lists\<close>

lemma sorted_transpose[simp]: "sorted (rev (map length (transpose xs)))"
by (auto simp: sorted_iff_nth_mono rev_nth nth_transpose
    length_filter_conv_card intro: card_mono)

lemma transpose_max_length:
  "foldr (\<lambda>xs. max (length xs)) (transpose xs) 0 = length (filter (\<lambda>x. x \<noteq> []) xs)"
  (is "?L = ?R")
proof (cases "transpose xs = []")
  case False
  have "?L = foldr max (map length (transpose xs)) 0"
    by (simp add: foldr_map comp_def)
  also have "... = length (transpose xs ! 0)"
    using False sorted_transpose by (simp add: foldr_max_sorted)
  finally show ?thesis
    using False by (simp add: nth_transpose)
next
  case True
  hence "filter (\<lambda>x. x \<noteq> []) xs = []"
    by (auto intro!: filter_False simp: transpose_empty)
  thus ?thesis by (simp add: transpose_empty True)
qed

lemma length_transpose_sorted:
  fixes xs :: "'a list list"
  assumes sorted: "sorted (rev (map length xs))"
  shows "length (transpose xs) = (if xs = [] then 0 else length (xs ! 0))"
proof (cases "xs = []")
  case False
  thus ?thesis
    using foldr_max_sorted[OF sorted] False
    unfolding length_transpose foldr_map comp_def
    by simp
qed simp

lemma nth_nth_transpose_sorted[simp]:
  fixes xs :: "'a list list"
  assumes sorted: "sorted (rev (map length xs))"
  and i: "i < length (transpose xs)"
  and j: "j < length (filter (\<lambda>ys. i < length ys) xs)"
  shows "transpose xs ! i ! j = xs ! j  ! i"
using j filter_equals_takeWhile_sorted_rev[OF sorted, of i]
    nth_transpose[OF i] nth_map[OF j]
by (simp add: takeWhile_nth)

lemma transpose_column_length:
  fixes xs :: "'a list list"
  assumes sorted: "sorted (rev (map length xs))" and "i < length xs"
  shows "length (filter (\<lambda>ys. i < length ys) (transpose xs)) = length (xs ! i)"
proof -
  have "xs \<noteq> []" using \<open>i < length xs\<close> by auto
  note filter_equals_takeWhile_sorted_rev[OF sorted, simp]
  { fix j assume "j \<le> i"
    note sorted_rev_nth_mono[OF sorted, of j i, simplified, OF this \<open>i < length xs\<close>]
  } note sortedE = this[consumes 1]

  have "{j. j < length (transpose xs) \<and> i < length (transpose xs ! j)}
    = {..< length (xs ! i)}"
  proof safe
    fix j
    assume "j < length (transpose xs)" and "i < length (transpose xs ! j)"
    with this(2) nth_transpose[OF this(1)]
    have "i < length (takeWhile (\<lambda>ys. j < length ys) xs)" by simp
    from nth_mem[OF this] takeWhile_nth[OF this]
    show "j < length (xs ! i)" by (auto dest: set_takeWhileD)
  next
    fix j assume "j < length (xs ! i)"
    thus "j < length (transpose xs)"
      using foldr_max_sorted[OF sorted] \<open>xs \<noteq> []\<close> sortedE[OF le0]
      by (auto simp: length_transpose comp_def foldr_map)

    have "Suc i \<le> length (takeWhile (\<lambda>ys. j < length ys) xs)"
      using \<open>i < length xs\<close> \<open>j < length (xs ! i)\<close> less_Suc_eq_le
      by (auto intro!: length_takeWhile_less_P_nth dest!: sortedE)
    with nth_transpose[OF \<open>j < length (transpose xs)\<close>]
    show "i < length (transpose xs ! j)" by simp
  qed
  thus ?thesis by (simp add: length_filter_conv_card)
qed

lemma transpose_column:
  fixes xs :: "'a list list"
  assumes sorted: "sorted (rev (map length xs))" and "i < length xs"
  shows "map (\<lambda>ys. ys ! i) (filter (\<lambda>ys. i < length ys) (transpose xs))
    = xs ! i" (is "?R = _")
proof (rule nth_equalityI)
  show length: "length ?R = length (xs ! i)"
    using transpose_column_length[OF assms] by simp

  fix j assume j: "j < length ?R"
  note * = less_le_trans[OF this, unfolded length_map, OF length_filter_le]
  from j have j_less: "j < length (xs ! i)" using length by simp
  have i_less_tW: "Suc i \<le> length (takeWhile (\<lambda>ys. Suc j \<le> length ys) xs)"
  proof (rule length_takeWhile_less_P_nth)
    show "Suc i \<le> length xs" using \<open>i < length xs\<close> by simp
    fix k assume "k < Suc i"
    hence "k \<le> i" by auto
    with sorted_rev_nth_mono[OF sorted this] \<open>i < length xs\<close>
    have "length (xs ! i) \<le> length (xs ! k)" by simp
    thus "Suc j \<le> length (xs ! k)" using j_less by simp
  qed
  have i_less_filter: "i < length (filter (\<lambda>ys. j < length ys) xs) "
    unfolding filter_equals_takeWhile_sorted_rev[OF sorted, of j]
    using i_less_tW by (simp_all add: Suc_le_eq)
  from j show "?R ! j = xs ! i ! j"
    unfolding filter_equals_takeWhile_sorted_rev[OF sorted_transpose, of i]
    by (simp add: takeWhile_nth nth_nth_transpose_sorted[OF sorted * i_less_filter])
qed

lemma transpose_transpose:
  fixes xs :: "'a list list"
  assumes sorted: "sorted (rev (map length xs))"
  shows "transpose (transpose xs) = takeWhile (\<lambda>x. x \<noteq> []) xs" (is "?L = ?R")
proof -
  have len: "length ?L = length ?R"
    unfolding length_transpose transpose_max_length
    using filter_equals_takeWhile_sorted_rev[OF sorted, of 0]
    by simp

  { fix i assume "i < length ?R"
    with less_le_trans[OF _ length_takeWhile_le[of _ xs]]
    have "i < length xs" by simp
  } note * = this
  show ?thesis
    by (rule nth_equalityI)
       (simp_all add: len nth_transpose transpose_column[OF sorted] * takeWhile_nth)
qed

theorem transpose_rectangle:
  assumes "xs = [] \<Longrightarrow> n = 0"
  assumes rect: "\<And> i. i < length xs \<Longrightarrow> length (xs ! i) = n"
  shows "transpose xs = map (\<lambda> i. map (\<lambda> j. xs ! j ! i) [0..<length xs]) [0..<n]"
    (is "?trans = ?map")
proof (rule nth_equalityI)
  have "sorted (rev (map length xs))"
    by (auto simp: rev_nth rect sorted_iff_nth_mono)
  from foldr_max_sorted[OF this] assms
  show len: "length ?trans = length ?map"
    by (simp_all add: length_transpose foldr_map comp_def)
  moreover
  { fix i assume "i < n" hence "filter (\<lambda>ys. i < length ys) xs = xs"
      using rect by (auto simp: in_set_conv_nth intro!: filter_True) }
  ultimately show "\<And>i. i < length (transpose xs) \<Longrightarrow> ?trans ! i = ?map ! i"
    by (auto simp: nth_transpose intro: nth_equalityI)
qed


subsubsection \<open>\<open>sorted_list_of_set\<close>\<close>

text\<open>This function maps (finite) linearly ordered sets to sorted
lists. Warning: in most cases it is not a good idea to convert from
sets to lists but one should convert in the other direction (via
\<^const>\<open>set\<close>).\<close>

context linorder
begin

definition sorted_list_of_set :: "'a set \<Rightarrow> 'a list" where
  "sorted_list_of_set = folding.F insort []"

sublocale sorted_list_of_set: folding insort Nil
rewrites
  "folding.F insort [] = sorted_list_of_set"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show "folding insort" by standard (fact comp_fun_commute)
  show "folding.F insort [] = sorted_list_of_set" by (simp only: sorted_list_of_set_def)
qed

lemma sorted_list_of_set_empty:
  "sorted_list_of_set {} = []"
  by (fact sorted_list_of_set.empty)

lemma sorted_list_of_set_insert [simp]:
  "finite A \<Longrightarrow> sorted_list_of_set (insert x A) = insort x (sorted_list_of_set (A - {x}))"
  by (fact sorted_list_of_set.insert_remove)

lemma sorted_list_of_set_eq_Nil_iff [simp]:
  "finite A \<Longrightarrow> sorted_list_of_set A = [] \<longleftrightarrow> A = {}"
  by (auto simp: sorted_list_of_set.remove)

lemma set_sorted_list_of_set [simp]:
  "finite A \<Longrightarrow> set (sorted_list_of_set A) = A"
  by(induct A rule: finite_induct) (simp_all add: set_insort_key)

lemma sorted_sorted_list_of_set [simp]: "sorted (sorted_list_of_set A)"
proof (cases "finite A")
  case True thus ?thesis by(induction A) (simp_all add: sorted_insort)
next
  case False thus ?thesis by simp
qed

lemma distinct_sorted_list_of_set [simp]: "distinct (sorted_list_of_set A)"
proof (cases "finite A")
  case True thus ?thesis by(induction A) (simp_all add: distinct_insort)
next
  case False thus ?thesis by simp
qed

lemma length_sorted_list_of_set [simp]: "length (sorted_list_of_set A) = card A"
proof (cases "finite A")
  case True
  then show ?thesis 
    by(metis distinct_card distinct_sorted_list_of_set set_sorted_list_of_set)
qed auto

lemmas sorted_list_of_set = set_sorted_list_of_set sorted_sorted_list_of_set distinct_sorted_list_of_set

lemma sorted_list_of_set_sort_remdups [code]:
  "sorted_list_of_set (set xs) = sort (remdups xs)"
proof -
  interpret comp_fun_commute insort by (fact comp_fun_commute_insort)
  show ?thesis by (simp add: sorted_list_of_set.eq_fold sort_conv_fold fold_set_fold_remdups)
qed

lemma sorted_list_of_set_remove:
  assumes "finite A"
  shows "sorted_list_of_set (A - {x}) = remove1 x (sorted_list_of_set A)"
proof (cases "x \<in> A")
  case False with assms have "x \<notin> set (sorted_list_of_set A)" by simp
  with False show ?thesis by (simp add: remove1_idem)
next
  case True then obtain B where A: "A = insert x B" by (rule Set.set_insert)
  with assms show ?thesis by simp
qed

lemma strict_sorted_list_of_set [simp]: "strict_sorted (sorted_list_of_set A)"
  by (simp add: strict_sorted_iff)

lemma finite_set_strict_sorted:
  assumes "finite A"
  obtains l where "strict_sorted l" "set l = A" "length l = card A"
  by (metis assms distinct_card distinct_sorted_list_of_set set_sorted_list_of_set strict_sorted_list_of_set)

lemma strict_sorted_equal:
  assumes "strict_sorted xs"
      and "strict_sorted ys"
      and "set ys = set xs"
    shows "ys = xs"
  using assms
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  show ?case
  proof (cases ys)
    case Nil
    then show ?thesis
      using Cons.prems by auto 
  next
    case (Cons y ys')
    then have "xs = ys'"
      by (metis Cons.prems list.inject sorted_distinct_set_unique strict_sorted_iff)
    moreover have "x = y"
      using Cons.prems \<open>xs = ys'\<close> local.Cons by fastforce
    ultimately show ?thesis
      using local.Cons by blast
  qed
qed auto

lemma strict_sorted_equal_Uniq: "\<exists>\<^sub>\<le>\<^sub>1xs. strict_sorted xs \<and> set xs = A"
  by (simp add: Uniq_def strict_sorted_equal)

lemma sorted_list_of_set_inject:
  assumes "sorted_list_of_set A = sorted_list_of_set B" "finite A" "finite B" 
  shows "A = B"
  using assms set_sorted_list_of_set by fastforce

lemma sorted_list_of_set_unique:
  assumes "finite A"
  shows "strict_sorted l \<and> set l = A \<and> length l = card A \<longleftrightarrow> sorted_list_of_set A = l"
  using assms strict_sorted_equal by force

end

lemma sorted_list_of_set_range [simp]:
  "sorted_list_of_set {m..<n} = [m..<n]"
by (rule sorted_distinct_set_unique) simp_all

lemma sorted_list_of_set_lessThan_Suc [simp]: 
  "sorted_list_of_set {..<Suc k} = sorted_list_of_set {..<k} @ [k]"
proof -
  have "sorted_wrt (<) (sorted_list_of_set {..<k} @ [k])"
    unfolding sorted_wrt_append  by (auto simp flip: strict_sorted_sorted_wrt)
  then show ?thesis
    by (simp add: lessThan_atLeast0)
qed

lemma sorted_list_of_set_atMost_Suc [simp]:
  "sorted_list_of_set {..Suc k} = sorted_list_of_set {..k} @ [Suc k]"
  using lessThan_Suc_atMost sorted_list_of_set_lessThan_Suc by fastforce

lemma sorted_list_of_set_nonempty:
  assumes "finite A" "A \<noteq> {}"
  shows "sorted_list_of_set A = Min A # sorted_list_of_set (A - {Min A})"
  using assms by (auto simp: less_le simp flip: sorted_list_of_set_unique intro: Min_in)

lemma sorted_list_of_set_greaterThanLessThan:
  assumes "Suc i < j" 
    shows "sorted_list_of_set {i<..<j} = Suc i # sorted_list_of_set {Suc i<..<j}"
proof -
  have "{i<..<j} = insert (Suc i) {Suc i<..<j}"
    using assms by auto
  then show ?thesis
    by (metis assms atLeastSucLessThan_greaterThanLessThan sorted_list_of_set_range upt_conv_Cons)
qed

lemma sorted_list_of_set_greaterThanAtMost:
  assumes "Suc i \<le> j" 
    shows "sorted_list_of_set {i<..j} = Suc i # sorted_list_of_set {Suc i<..j}"
  using sorted_list_of_set_greaterThanLessThan [of i "Suc j"]
  by (metis assms greaterThanAtMost_def greaterThanLessThan_eq le_imp_less_Suc lessThan_Suc_atMost)

lemma nth_sorted_list_of_set_greaterThanLessThan: 
  "n < j - Suc i \<Longrightarrow> sorted_list_of_set {i<..<j} ! n = Suc (i+n)"
  by (induction n arbitrary: i) (auto simp: sorted_list_of_set_greaterThanLessThan)

lemma nth_sorted_list_of_set_greaterThanAtMost: 
  "n < j - i \<Longrightarrow> sorted_list_of_set {i<..j} ! n = Suc (i+n)"
  using nth_sorted_list_of_set_greaterThanLessThan [of n "Suc j" i]
  by (simp add: greaterThanAtMost_def greaterThanLessThan_eq lessThan_Suc_atMost)


subsubsection \<open>\<open>lists\<close>: the list-forming operator over sets\<close>

inductive_set
  lists :: "'a set => 'a list set"
  for A :: "'a set"
where
    Nil [intro!, simp]: "[] \<in> lists A"
  | Cons [intro!, simp]: "\<lbrakk>a \<in> A; l \<in> lists A\<rbrakk> \<Longrightarrow> a#l \<in> lists A"

inductive_cases listsE [elim!]: "x#l \<in> lists A"
inductive_cases listspE [elim!]: "listsp A (x # l)"

inductive_simps listsp_simps[code]:
  "listsp A []"
  "listsp A (x # xs)"

lemma listsp_mono [mono]: "A \<le> B \<Longrightarrow> listsp A \<le> listsp B"
by (rule predicate1I, erule listsp.induct, blast+)

lemmas lists_mono = listsp_mono [to_set]

lemma listsp_infI:
  assumes l: "listsp A l" shows "listsp B l \<Longrightarrow> listsp (inf A B) l" using l
by induct blast+

lemmas lists_IntI = listsp_infI [to_set]

lemma listsp_inf_eq [simp]: "listsp (inf A B) = inf (listsp A) (listsp B)"
proof (rule mono_inf [where f=listsp, THEN order_antisym])
  show "mono listsp" by (simp add: mono_def listsp_mono)
  show "inf (listsp A) (listsp B) \<le> listsp (inf A B)" by (blast intro!: listsp_infI)
qed

lemmas listsp_conj_eq [simp] = listsp_inf_eq [simplified inf_fun_def inf_bool_def]

lemmas lists_Int_eq [simp] = listsp_inf_eq [to_set]

lemma Cons_in_lists_iff[simp]: "x#xs \<in> lists A \<longleftrightarrow> x \<in> A \<and> xs \<in> lists A"
by auto

lemma append_in_listsp_conv [iff]:
     "(listsp A (xs @ ys)) = (listsp A xs \<and> listsp A ys)"
by (induct xs) auto

lemmas append_in_lists_conv [iff] = append_in_listsp_conv [to_set]

lemma in_listsp_conv_set: "(listsp A xs) = (\<forall>x \<in> set xs. A x)"
\<comment> \<open>eliminate \<open>listsp\<close> in favour of \<open>set\<close>\<close>
by (induct xs) auto

lemmas in_lists_conv_set [code_unfold] = in_listsp_conv_set [to_set]

lemma in_listspD [dest!]: "listsp A xs \<Longrightarrow> \<forall>x\<in>set xs. A x"
by (rule in_listsp_conv_set [THEN iffD1])

lemmas in_listsD [dest!] = in_listspD [to_set]

lemma in_listspI [intro!]: "\<forall>x\<in>set xs. A x \<Longrightarrow> listsp A xs"
by (rule in_listsp_conv_set [THEN iffD2])

lemmas in_listsI [intro!] = in_listspI [to_set]

lemma lists_eq_set: "lists A = {xs. set xs \<le> A}"
by auto

lemma lists_empty [simp]: "lists {} = {[]}"
by auto

lemma lists_UNIV [simp]: "lists UNIV = UNIV"
by auto

lemma lists_image: "lists (f`A) = map f ` lists A"
proof -
  { fix xs have "\<forall>x\<in>set xs. x \<in> f ` A \<Longrightarrow> xs \<in> map f ` lists A"
      by (induct xs) (auto simp del: list.map simp add: list.map[symmetric] intro!: imageI) }
  then show ?thesis by auto
qed

subsubsection \<open>Inductive definition for membership\<close>

inductive ListMem :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
    elem:  "ListMem x (x # xs)"
  | insert:  "ListMem x xs \<Longrightarrow> ListMem x (y # xs)"

lemma ListMem_iff: "(ListMem x xs) = (x \<in> set xs)"
proof
  show "ListMem x xs \<Longrightarrow> x \<in> set xs"
    by (induct set: ListMem) auto
  show "x \<in> set xs \<Longrightarrow> ListMem x xs"
    by (induct xs) (auto intro: ListMem.intros)
qed


subsubsection \<open>Lists as Cartesian products\<close>

text\<open>\<open>set_Cons A Xs\<close>: the set of lists with head drawn from
\<^term>\<open>A\<close> and tail drawn from \<^term>\<open>Xs\<close>.\<close>

definition set_Cons :: "'a set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
"set_Cons A XS = {z. \<exists>x xs. z = x # xs \<and> x \<in> A \<and> xs \<in> XS}"

lemma set_Cons_sing_Nil [simp]: "set_Cons A {[]} = (%x. [x])`A"
by (auto simp add: set_Cons_def)

text\<open>Yields the set of lists, all of the same length as the argument and
with elements drawn from the corresponding element of the argument.\<close>

primrec listset :: "'a set list \<Rightarrow> 'a list set" where
"listset [] = {[]}" |
"listset (A # As) = set_Cons A (listset As)"


subsection \<open>Relations on Lists\<close>

subsubsection \<open>Length Lexicographic Ordering\<close>

text\<open>These orderings preserve well-foundedness: shorter lists
  precede longer lists. These ordering are not used in dictionaries.\<close>

primrec \<comment> \<open>The lexicographic ordering for lists of the specified length\<close>
  lexn :: "('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a list) set" where
"lexn r 0 = {}" |
"lexn r (Suc n) =
  (map_prod (%(x, xs). x#xs) (%(x, xs). x#xs) ` (r <*lex*> lexn r n)) Int
  {(xs, ys). length xs = Suc n \<and> length ys = Suc n}"

definition lex :: "('a \<times> 'a) set \<Rightarrow> ('a list \<times> 'a list) set" where
"lex r = (\<Union>n. lexn r n)" \<comment> \<open>Holds only between lists of the same length\<close>

definition lenlex :: "('a \<times> 'a) set => ('a list \<times> 'a list) set" where
"lenlex r = inv_image (less_than <*lex*> lex r) (\<lambda>xs. (length xs, xs))"
        \<comment> \<open>Compares lists by their length and then lexicographically\<close>

lemma wf_lexn: assumes "wf r" shows "wf (lexn r n)"
proof (induct n)
  case (Suc n)
  have inj: "inj (\<lambda>(x, xs). x # xs)"
    using assms by (auto simp: inj_on_def)
  have wf: "wf (map_prod (\<lambda>(x, xs). x # xs) (\<lambda>(x, xs). x # xs) ` (r <*lex*> lexn r n))"
    by (simp add: Suc.hyps assms wf_lex_prod wf_map_prod_image [OF _ inj])
  then show ?case
    by (rule wf_subset) auto
qed auto

lemma lexn_length:
  "(xs, ys) \<in> lexn r n \<Longrightarrow> length xs = n \<and> length ys = n"
  by (induct n arbitrary: xs ys) auto

lemma wf_lex [intro!]: 
  assumes "wf r" shows "wf (lex r)"
  unfolding lex_def
proof (rule wf_UN)
  show "wf (lexn r i)" for i
    by (simp add: assms wf_lexn)
  show "\<And>i j. lexn r i \<noteq> lexn r j \<Longrightarrow> Domain (lexn r i) \<inter> Range (lexn r j) = {}"
    by (metis DomainE Int_emptyI RangeE lexn_length)
qed

lemma lexn_conv:
  "lexn r n =
    {(xs,ys). length xs = n \<and> length ys = n \<and>
    (\<exists>xys x y xs' ys'. xs= xys @ x#xs' \<and> ys= xys @ y # ys' \<and> (x, y) \<in> r)}"
proof (induction n)
  case (Suc n)
  then show ?case
    apply (simp add: image_Collect lex_prod_def, safe, blast)
     apply (rule_tac x = "ab # xys" in exI, simp)
    apply (case_tac xys; force)
    done
qed auto

text\<open>By Mathias Fleury:\<close>
proposition lexn_transI:
  assumes "trans r" shows "trans (lexn r n)"
unfolding trans_def
proof (intro allI impI)
  fix as bs cs
  assume asbs: "(as, bs) \<in> lexn r n" and bscs: "(bs, cs) \<in> lexn r n"
  obtain abs a b as' bs' where
    n: "length as = n" and "length bs = n" and
    as: "as = abs @ a # as'" and
    bs: "bs = abs @ b # bs'" and
    abr: "(a, b) \<in> r"
    using asbs unfolding lexn_conv by blast
  obtain bcs b' c' cs' bs' where
    n': "length cs = n" and "length bs = n" and
    bs': "bs = bcs @ b' # bs'" and
    cs: "cs = bcs @ c' # cs'" and
    b'c'r: "(b', c') \<in> r"
    using bscs unfolding lexn_conv by blast
  consider (le) "length bcs < length abs"
    | (eq) "length bcs = length abs"
    | (ge) "length bcs > length abs" by linarith
  thus "(as, cs) \<in> lexn r n"
  proof cases
    let ?k = "length bcs"
    case le
    hence "as ! ?k = bs ! ?k" unfolding as bs by (simp add: nth_append)
    hence "(as ! ?k, cs ! ?k) \<in> r" using b'c'r unfolding bs' cs by auto
    moreover
    have "length bcs < length as" using le unfolding as by simp
    from id_take_nth_drop[OF this]
    have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
    moreover
    have "length bcs < length cs" unfolding cs by simp
    from id_take_nth_drop[OF this]
    have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
    moreover have "take ?k as = take ?k cs"
      using le arg_cong[OF bs, of "take (length bcs)"]
      unfolding cs as bs' by auto
    ultimately show ?thesis using n n' unfolding lexn_conv by auto
  next
    let ?k = "length abs"
    case ge
    hence "bs ! ?k = cs ! ?k" unfolding bs' cs by (simp add: nth_append)
    hence "(as ! ?k, cs ! ?k) \<in> r" using abr unfolding as bs by auto
    moreover
    have "length abs < length as" using ge unfolding as by simp
    from id_take_nth_drop[OF this]
    have "as = take ?k as @ as ! ?k # drop (Suc ?k) as" .
    moreover have "length abs < length cs" using n n' unfolding as by simp
    from id_take_nth_drop[OF this]
    have "cs = take ?k cs @ cs ! ?k # drop (Suc ?k) cs" .
    moreover have "take ?k as = take ?k cs"
      using ge arg_cong[OF bs', of "take (length abs)"]
      unfolding cs as bs by auto
    ultimately show ?thesis using n n' unfolding lexn_conv by auto
  next
    let ?k = "length abs"
    case eq
    hence *: "abs = bcs" "b = b'" using bs bs' by auto
    hence "(a, c') \<in> r"
      using abr b'c'r assms unfolding trans_def by blast
    with * show ?thesis using n n' unfolding lexn_conv as bs cs by auto
  qed
qed

corollary lex_transI:
    assumes "trans r" shows "trans (lex r)"
  using lexn_transI [OF assms]
  by (clarsimp simp add: lex_def trans_def) (metis lexn_length)

lemma lex_conv:
  "lex r =
    {(xs,ys). length xs = length ys \<and>
    (\<exists>xys x y xs' ys'. xs = xys @ x # xs' \<and> ys = xys @ y # ys' \<and> (x, y) \<in> r)}"
by (force simp add: lex_def lexn_conv)

lemma wf_lenlex [intro!]: "wf r \<Longrightarrow> wf (lenlex r)"
by (unfold lenlex_def) blast

lemma lenlex_conv:
    "lenlex r = {(xs,ys). length xs < length ys \<or>
                 length xs = length ys \<and> (xs, ys) \<in> lex r}"
  by (auto simp add: lenlex_def Id_on_def lex_prod_def inv_image_def)

lemma total_lenlex:
  assumes "total r"
  shows "total (lenlex r)"
proof -
  have "(xs,ys) \<in> lexn r (length xs) \<or> (ys,xs) \<in> lexn r (length xs)"
    if "xs \<noteq> ys" and len: "length xs = length ys" for xs ys
  proof -
    obtain pre x xs' y ys' where "x\<noteq>y" and xs: "xs = pre @ [x] @ xs'" and ys: "ys = pre @ [y] @ys'"
      by (meson len \<open>xs \<noteq> ys\<close> same_length_different) 
    then consider "(x,y) \<in> r" | "(y,x) \<in> r"
      by (meson UNIV_I assms total_on_def)
    then show ?thesis
    by cases (use len in \<open>(force simp add: lexn_conv xs ys)+\<close>)
qed
  then show ?thesis
    by (fastforce simp: lenlex_def total_on_def lex_def)
qed

lemma lenlex_transI [intro]: "trans r \<Longrightarrow> trans (lenlex r)"
  unfolding lenlex_def
  by (meson lex_transI trans_inv_image trans_less_than trans_lex_prod)

lemma Nil_notin_lex [iff]: "([], ys) \<notin> lex r"
  by (simp add: lex_conv)

lemma Nil2_notin_lex [iff]: "(xs, []) \<notin> lex r"
  by (simp add:lex_conv)

lemma Cons_in_lex [simp]:
  "(x # xs, y # ys) \<in> lex r \<longleftrightarrow> (x, y) \<in> r \<and> length xs = length ys \<or> x = y \<and> (xs, ys) \<in> lex r"
 (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: lex_conv) (metis hd_append list.sel(1) list.sel(3) tl_append2)
next
  assume ?rhs then show ?lhs
    by (simp add: lex_conv) (blast intro: Cons_eq_appendI)
qed

lemma Nil_lenlex_iff1 [simp]: "([], ns) \<in> lenlex r \<longleftrightarrow> ns \<noteq> []" 
  and Nil_lenlex_iff2 [simp]: "(ns,[]) \<notin> lenlex r"
  by (auto simp: lenlex_def)

lemma Cons_lenlex_iff: 
  "((m # ms, n # ns) \<in> lenlex r) \<longleftrightarrow> 
    length ms < length ns 
  \<or> length ms = length ns \<and> (m,n) \<in> r 
  \<or> (m = n \<and> (ms,ns) \<in> lenlex r)"
  by (auto simp: lenlex_def)

lemma lenlex_irreflexive: "(\<And>x. (x,x) \<notin> r) \<Longrightarrow> (xs,xs) \<notin> lenlex r"
  by (induction xs) (auto simp add: Cons_lenlex_iff)

lemma lenlex_trans:
    "\<lbrakk>(x,y) \<in> lenlex r; (y,z) \<in> lenlex r; trans r\<rbrakk> \<Longrightarrow> (x,z) \<in> lenlex r"
  by (meson lenlex_transI transD)

lemma lenlex_length: "(ms, ns) \<in> lenlex r \<Longrightarrow> length ms \<le> length ns"
  by (auto simp: lenlex_def)

lemma lex_append_rightI:
  "(xs, ys) \<in> lex r \<Longrightarrow> length vs = length us \<Longrightarrow> (xs @ us, ys @ vs) \<in> lex r"
  by (fastforce simp: lex_def lexn_conv)

lemma lex_append_leftI:
  "(ys, zs) \<in> lex r \<Longrightarrow> (xs @ ys, xs @ zs) \<in> lex r"
  by (induct xs) auto

lemma lex_append_leftD:
  "\<forall>x. (x,x) \<notin> r \<Longrightarrow> (xs @ ys, xs @ zs) \<in> lex r \<Longrightarrow> (ys, zs) \<in> lex r"
  by (induct xs) auto

lemma lex_append_left_iff:
  "\<forall>x. (x,x) \<notin> r \<Longrightarrow> (xs @ ys, xs @ zs) \<in> lex r \<longleftrightarrow> (ys, zs) \<in> lex r"
  by(metis lex_append_leftD lex_append_leftI)

lemma lex_take_index:
  assumes "(xs, ys) \<in> lex r"
  obtains i where "i < length xs" and "i < length ys" and "take i xs = take i ys"
    and "(xs ! i, ys ! i) \<in> r"
proof -
  obtain n us x xs' y ys' where "(xs, ys) \<in> lexn r n" and "length xs = n" and "length ys = n"
    and "xs = us @ x # xs'" and "ys = us @ y # ys'" and "(x, y) \<in> r"
    using assms by (fastforce simp: lex_def lexn_conv)
  then show ?thesis by (intro that [of "length us"]) auto
qed

lemma irrefl_lex: "irrefl r \<Longrightarrow> irrefl (lex r)"
  by (meson irrefl_def lex_take_index)

lemma lexl_not_refl [simp]: "irrefl r \<Longrightarrow> (x,x) \<notin> lex r"
  by (meson irrefl_def lex_take_index)


subsubsection \<open>Lexicographic Ordering\<close>

text \<open>Classical lexicographic ordering on lists, ie. "a" < "ab" < "b".
    This ordering does \emph{not} preserve well-foundedness.
     Author: N. Voelker, March 2005.\<close>

definition lexord :: "('a \<times> 'a) set \<Rightarrow> ('a list \<times> 'a list) set" where
"lexord r = {(x,y). \<exists> a v. y = x @ a # v \<or>
            (\<exists> u a b v w. (a,b) \<in> r \<and> x = u @ (a # v) \<and> y = u @ (b # w))}"

lemma lexord_Nil_left[simp]:  "([],y) \<in> lexord r = (\<exists> a x. y = a # x)"
by (unfold lexord_def, induct_tac y, auto)

lemma lexord_Nil_right[simp]: "(x,[]) \<notin> lexord r"
by (unfold lexord_def, induct_tac x, auto)

lemma lexord_cons_cons[simp]:
  "(a # x, b # y) \<in> lexord r \<longleftrightarrow> (a,b)\<in> r \<or> (a = b \<and> (x,y)\<in> lexord r)"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: lexord_def)
    apply (metis hd_append list.sel(1) list.sel(3) tl_append2)
    done
qed (auto simp add: lexord_def; (blast | meson Cons_eq_appendI))

lemmas lexord_simps = lexord_Nil_left lexord_Nil_right lexord_cons_cons

lemma lexord_same_pref_iff:
  "(xs @ ys, xs @ zs) \<in> lexord r \<longleftrightarrow> (\<exists>x \<in> set xs. (x,x) \<in> r) \<or> (ys, zs) \<in> lexord r"
by(induction xs) auto

lemma lexord_same_pref_if_irrefl[simp]:
  "irrefl r \<Longrightarrow> (xs @ ys, xs @ zs) \<in> lexord r \<longleftrightarrow> (ys, zs) \<in> lexord r"
by (simp add: irrefl_def lexord_same_pref_iff)

lemma lexord_append_rightI: "\<exists> b z. y = b # z \<Longrightarrow> (x, x @ y) \<in> lexord r"
by (metis append_Nil2 lexord_Nil_left lexord_same_pref_iff)

lemma lexord_append_left_rightI:
  "(a,b) \<in> r \<Longrightarrow> (u @ a # x, u @ b # y) \<in> lexord r"
by (simp add: lexord_same_pref_iff)

lemma lexord_append_leftI: "(u,v) \<in> lexord r \<Longrightarrow> (x @ u, x @ v) \<in> lexord r"
by (simp add: lexord_same_pref_iff)

lemma lexord_append_leftD:
  "\<lbrakk>(x @ u, x @ v) \<in> lexord r; (\<forall>a. (a,a) \<notin> r) \<rbrakk> \<Longrightarrow> (u,v) \<in> lexord r"
by (simp add: lexord_same_pref_iff)

lemma lexord_take_index_conv:
   "((x,y) \<in> lexord r) =
    ((length x < length y \<and> take (length x) y = x) \<or>
     (\<exists>i. i < min(length x)(length y) \<and> take i x = take i y \<and> (x!i,y!i) \<in> r))"
proof -
  have "(\<exists>a v. y = x @ a # v) = (length x < length y \<and> take (length x) y = x)"
    by (metis Cons_nth_drop_Suc append_eq_conv_conj drop_all list.simps(3) not_le)
  moreover
  have "(\<exists>u a b. (a, b) \<in> r \<and> (\<exists>v. x = u @ a # v) \<and> (\<exists>w. y = u @ b # w)) =
        (\<exists>i<length x. i < length y \<and> take i x = take i y \<and> (x ! i, y ! i) \<in> r)"
    apply safe
    using less_iff_Suc_add apply auto[1]
    by (metis id_take_nth_drop)
  ultimately show ?thesis
    by (auto simp: lexord_def Let_def)
qed

\<comment> \<open>lexord is extension of partial ordering List.lex\<close>
lemma lexord_lex: "(x,y) \<in> lex r = ((x,y) \<in> lexord r \<and> length x = length y)"
proof (induction x arbitrary: y)
  case (Cons a x y) then show ?case
    by (cases y) (force+)
qed auto

lemma lexord_sufI:
  assumes "(u,w) \<in> lexord r" "length w \<le> length u"
  shows "(u@v,w@z) \<in> lexord r"
proof-
  from leD[OF assms(2)] assms(1)[unfolded lexord_take_index_conv[of u w r] min_absorb2[OF assms(2)]]
  obtain i where "take i u = take i w" and "(u!i,w!i) \<in> r" and "i < length w"
    by blast   
  hence "((u@v)!i, (w@z)!i) \<in> r"
    unfolding nth_append using less_le_trans[OF \<open>i < length w\<close> assms(2)] \<open>(u!i,w!i) \<in> r\<close>
    by presburger
  moreover have "i < min (length (u@v)) (length (w@z))"
    using assms(2) \<open>i < length w\<close> by simp
  moreover have "take i (u@v) = take i (w@z)"
    using assms(2) \<open>i < length w\<close> \<open>take i u = take i w\<close> by simp 
  ultimately show ?thesis
    using lexord_take_index_conv by blast
qed

lemma lexord_sufE: 
  assumes "(xs@zs,ys@qs) \<in> lexord r" "xs \<noteq> ys" "length xs = length ys" "length zs = length qs"
  shows "(xs,ys) \<in> lexord r"
proof-
  obtain i where "i < length (xs@zs)" and "i < length (ys@qs)" and "take i (xs@zs) = take i (ys@qs)"
  and "((xs@zs) ! i, (ys@qs) ! i) \<in> r"
    using assms(1) lex_take_index[unfolded lexord_lex,of "xs @ zs" "ys @ qs" r]
      length_append[of xs zs, unfolded assms(3,4), folded length_append[of ys qs]]
    by blast
  have "length (take i xs) = length (take i ys)"
    by (simp add: assms(3))
  have "i < length xs"
    using assms(2,3) le_less_linear take_all[of xs i] take_all[of ys i]
      \<open>take i (xs @ zs) = take i (ys @ qs)\<close> append_eq_append_conv take_append
    by metis
  hence "(xs ! i, ys ! i) \<in> r"
    using \<open>((xs @ zs) ! i, (ys @ qs) ! i) \<in> r\<close> assms(3) by (simp add: nth_append)
  moreover have "take i xs = take i ys"
    using assms(3) \<open>take i (xs @ zs) = take i (ys @ qs)\<close> by auto
  ultimately show ?thesis
    unfolding lexord_take_index_conv using \<open>i < length xs\<close> assms(3) by fastforce
qed

lemma lexord_irreflexive: "\<forall>x. (x,x) \<notin> r \<Longrightarrow> (xs,xs) \<notin> lexord r"
by (induct xs) auto

text\<open>By Ren\'e Thiemann:\<close>
lemma lexord_partial_trans:
  "(\<And>x y z. x \<in> set xs \<Longrightarrow> (x,y) \<in> r \<Longrightarrow> (y,z) \<in> r \<Longrightarrow> (x,z) \<in> r)
   \<Longrightarrow>  (xs,ys) \<in> lexord r  \<Longrightarrow>  (ys,zs) \<in> lexord r \<Longrightarrow>  (xs,zs) \<in> lexord r"
proof (induct xs arbitrary: ys zs)
  case Nil
  from Nil(3) show ?case unfolding lexord_def by (cases zs, auto)
next
  case (Cons x xs yys zzs)
  from Cons(3) obtain y ys where yys: "yys = y # ys" unfolding lexord_def
    by (cases yys, auto)
  note Cons = Cons[unfolded yys]
  from Cons(3) have one: "(x,y) \<in> r \<or> x = y \<and> (xs,ys) \<in> lexord r" by auto
  from Cons(4) obtain z zs where zzs: "zzs = z # zs" unfolding lexord_def
    by (cases zzs, auto)
  note Cons = Cons[unfolded zzs]
  from Cons(4) have two: "(y,z) \<in> r \<or> y = z \<and> (ys,zs) \<in> lexord r" by auto
  {
    assume "(xs,ys) \<in> lexord r" and "(ys,zs) \<in> lexord r"
    from Cons(1)[OF _ this] Cons(2)
    have "(xs,zs) \<in> lexord r" by auto
  } note ind1 = this
  {
    assume "(x,y) \<in> r" and "(y,z) \<in> r"
    from Cons(2)[OF _ this] have "(x,z) \<in> r" by auto
  } note ind2 = this
  from one two ind1 ind2
  have "(x,z) \<in> r \<or> x = z \<and> (xs,zs) \<in> lexord r" by blast
  thus ?case unfolding zzs by auto
qed

lemma lexord_trans:
  "\<lbrakk> (x, y) \<in> lexord r; (y, z) \<in> lexord r; trans r \<rbrakk> \<Longrightarrow> (x, z) \<in> lexord r"
  by(auto simp: trans_def intro:lexord_partial_trans)

lemma lexord_transI:  "trans r \<Longrightarrow> trans (lexord r)"
  by (meson lexord_trans transI)

lemma total_lexord: "total r \<Longrightarrow> total (lexord r)"
  unfolding total_on_def
proof clarsimp
  fix x y
  assume "\<forall>x y. x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"
    and "(x::'a list) \<noteq> y"
    and "(y, x) \<notin> lexord r"
  then
  show "(x, y) \<in> lexord r"
  proof (induction x arbitrary: y)
    case Nil
    then show ?case
      by (metis lexord_Nil_left list.exhaust)
  next
    case (Cons a x y) then show ?case
      by (cases y) (force+)
  qed
qed

corollary lexord_linear: "(\<forall>a b. (a,b) \<in> r \<or> a = b \<or> (b,a) \<in> r) \<Longrightarrow> (x,y) \<in> lexord r \<or> x = y \<or> (y,x) \<in> lexord r"
  using total_lexord by (metis UNIV_I total_on_def) 

lemma lexord_irrefl:
  "irrefl R \<Longrightarrow> irrefl (lexord R)"
by (simp add: irrefl_def lexord_irreflexive)

lemma lexord_asym:
  assumes "asym R"
  shows "asym (lexord R)"
proof 
  fix xs ys
  assume "(xs, ys) \<in> lexord R"
  then show "(ys, xs) \<notin> lexord R"
  proof (induct xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    then obtain z zs where ys: "ys = z # zs" by (cases ys) auto
    with assms Cons show ?case by (auto elim: asym.cases)
  qed
qed

lemma lexord_asymmetric:
  assumes "asym R"
  assumes hyp: "(a, b) \<in> lexord R"
  shows "(b, a) \<notin> lexord R"
proof -
  from \<open>asym R\<close> have "asym (lexord R)" by (rule lexord_asym)
  then show ?thesis by (rule asym.cases) (auto simp add: hyp)
qed

lemma asym_lex: "asym R \<Longrightarrow> asym (lex R)"
  by (meson asym.simps irrefl_lex lexord_asym lexord_lex)

lemma asym_lenlex: "asym R \<Longrightarrow> asym (lenlex R)"
  by (simp add: lenlex_def asym_inv_image asym_less_than asym_lex asym_lex_prod)

lemma lenlex_append1:
  assumes len: "(us,xs) \<in> lenlex R" and eq: "length vs = length ys" 
  shows "(us @ vs, xs @ ys) \<in> lenlex R"
  using len
proof (induction us)
  case Nil
  then show ?case 
    by (simp add: lenlex_def eq)
next
  case (Cons u us)
  with lex_append_rightI show ?case
    by (fastforce simp add: lenlex_def eq)
qed

lemma lenlex_append2 [simp]:
  assumes "irrefl R"
  shows "(us @ xs, us @ ys) \<in> lenlex R \<longleftrightarrow> (xs, ys) \<in> lenlex R"
proof (induction us)
  case Nil
  then show ?case 
    by (simp add: lenlex_def)
next
  case (Cons u us)
  with assms show ?case
    by (auto simp: lenlex_def irrefl_def)
qed

text \<open>
  Predicate version of lexicographic order integrated with Isabelle's order type classes.
  Author: Andreas Lochbihler
\<close>

context ord
begin

context
  notes [[inductive_internals]]
begin

inductive lexordp :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  Nil: "lexordp [] (y # ys)"
| Cons: "x < y \<Longrightarrow> lexordp (x # xs) (y # ys)"
| Cons_eq:
  "\<lbrakk> \<not> x < y; \<not> y < x; lexordp xs ys \<rbrakk> \<Longrightarrow> lexordp (x # xs) (y # ys)"

end

lemma lexordp_simps [simp]:
  "lexordp [] ys = (ys \<noteq> [])"
  "lexordp xs [] = False"
  "lexordp (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> \<not> y < x \<and> lexordp xs ys"
by(subst lexordp.simps, fastforce simp add: neq_Nil_conv)+

inductive lexordp_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  Nil: "lexordp_eq [] ys"
| Cons: "x < y \<Longrightarrow> lexordp_eq (x # xs) (y # ys)"
| Cons_eq: "\<lbrakk> \<not> x < y; \<not> y < x; lexordp_eq xs ys \<rbrakk> \<Longrightarrow> lexordp_eq (x # xs) (y # ys)"

lemma lexordp_eq_simps [simp]:
  "lexordp_eq [] ys = True"
  "lexordp_eq xs [] \<longleftrightarrow> xs = []"
  "lexordp_eq (x # xs) [] = False"
  "lexordp_eq (x # xs) (y # ys) \<longleftrightarrow> x < y \<or> \<not> y < x \<and> lexordp_eq xs ys"
by(subst lexordp_eq.simps, fastforce)+

lemma lexordp_append_rightI: "ys \<noteq> Nil \<Longrightarrow> lexordp xs (xs @ ys)"
by(induct xs)(auto simp add: neq_Nil_conv)

lemma lexordp_append_left_rightI: "x < y \<Longrightarrow> lexordp (us @ x # xs) (us @ y # ys)"
by(induct us) auto

lemma lexordp_eq_refl: "lexordp_eq xs xs"
by(induct xs) simp_all

lemma lexordp_append_leftI: "lexordp us vs \<Longrightarrow> lexordp (xs @ us) (xs @ vs)"
by(induct xs) auto

lemma lexordp_append_leftD: "\<lbrakk> lexordp (xs @ us) (xs @ vs); \<forall>a. \<not> a < a \<rbrakk> \<Longrightarrow> lexordp us vs"
by(induct xs) auto

lemma lexordp_irreflexive:
  assumes irrefl: "\<forall>x. \<not> x < x"
  shows "\<not> lexordp xs xs"
proof
  assume "lexordp xs xs"
  thus False by(induct xs ys\<equiv>xs)(simp_all add: irrefl)
qed

lemma lexordp_into_lexordp_eq:
  "lexordp xs ys \<Longrightarrow> lexordp_eq xs ys"
by (induction rule: lexordp.induct) simp_all

lemma lexordp_eq_pref: "lexordp_eq u (u @ v)"
by (metis append_Nil2 lexordp_append_rightI lexordp_eq_refl lexordp_into_lexordp_eq)

end

declare ord.lexordp_simps [simp, code]
declare ord.lexordp_eq_simps [code, simp]

context order
begin

lemma lexordp_antisym:
  assumes "lexordp xs ys" "lexordp ys xs"
  shows False
  using assms by induct auto

lemma lexordp_irreflexive': "\<not> lexordp xs xs"
by(rule lexordp_irreflexive) simp

end

context linorder begin

lemma lexordp_cases [consumes 1, case_names Nil Cons Cons_eq, cases pred: lexordp]:
  assumes "lexordp xs ys"
  obtains (Nil) y ys' where "xs = []" "ys = y # ys'"
  | (Cons) x xs' y ys' where "xs = x # xs'" "ys = y # ys'" "x < y"
  | (Cons_eq) x xs' ys' where "xs = x # xs'" "ys = x # ys'" "lexordp xs' ys'"
using assms by cases (fastforce simp add: not_less_iff_gr_or_eq)+

lemma lexordp_induct [consumes 1, case_names Nil Cons Cons_eq, induct pred: lexordp]:
  assumes major: "lexordp xs ys"
  and Nil: "\<And>y ys. P [] (y # ys)"
  and Cons: "\<And>x xs y ys. x < y \<Longrightarrow> P (x # xs) (y # ys)"
  and Cons_eq: "\<And>x xs ys. \<lbrakk> lexordp xs ys; P xs ys \<rbrakk> \<Longrightarrow> P (x # xs) (x # ys)"
  shows "P xs ys"
using major by induct (simp_all add: Nil Cons not_less_iff_gr_or_eq Cons_eq)

lemma lexordp_iff:
  "lexordp xs ys \<longleftrightarrow> (\<exists>x vs. ys = xs @ x # vs) \<or> (\<exists>us a b vs ws. a < b \<and> xs = us @ a # vs \<and> ys = us @ b # ws)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
  proof induct
    case Cons_eq thus ?case by simp (metis append.simps(2))
  qed(fastforce intro: disjI2 del: disjCI intro: exI[where x="[]"])+
next
  assume ?rhs thus ?lhs
    by(auto intro: lexordp_append_leftI[where us="[]", simplified] lexordp_append_leftI)
qed

lemma lexordp_conv_lexord:
  "lexordp xs ys \<longleftrightarrow> (xs, ys) \<in> lexord {(x, y). x < y}"
by(simp add: lexordp_iff lexord_def)

lemma lexordp_eq_antisym:
  assumes "lexordp_eq xs ys" "lexordp_eq ys xs"
  shows "xs = ys"
using assms by induct simp_all

lemma lexordp_eq_trans:
  assumes "lexordp_eq xs ys" and "lexordp_eq ys zs"
  shows "lexordp_eq xs zs"
  using assms
  by (induct arbitrary: zs) (case_tac zs; auto)+

lemma lexordp_trans:
  assumes "lexordp xs ys" "lexordp ys zs"
  shows "lexordp xs zs"
  using assms
  by (induct arbitrary: zs) (case_tac zs; auto)+

lemma lexordp_linear: "lexordp xs ys \<or> xs = ys \<or> lexordp ys xs"
  by(induct xs arbitrary: ys; case_tac ys; fastforce)

lemma lexordp_conv_lexordp_eq: "lexordp xs ys \<longleftrightarrow> lexordp_eq xs ys \<and> \<not> lexordp_eq ys xs"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "\<not> lexordp_eq ys xs" by induct simp_all
  with \<open>?lhs\<close> show ?rhs by (simp add: lexordp_into_lexordp_eq)
next
  assume ?rhs
  hence "lexordp_eq xs ys" "\<not> lexordp_eq ys xs" by simp_all
  thus ?lhs by induct simp_all
qed

lemma lexordp_eq_conv_lexord: "lexordp_eq xs ys \<longleftrightarrow> xs = ys \<or> lexordp xs ys"
by(auto simp add: lexordp_conv_lexordp_eq lexordp_eq_refl dest: lexordp_eq_antisym)

lemma lexordp_eq_linear: "lexordp_eq xs ys \<or> lexordp_eq ys xs"
  by (induct xs arbitrary: ys) (case_tac ys; auto)+

lemma lexordp_linorder: "class.linorder lexordp_eq lexordp"
  by unfold_locales
     (auto simp add: lexordp_conv_lexordp_eq lexordp_eq_refl lexordp_eq_antisym intro: lexordp_eq_trans del: disjCI intro: lexordp_eq_linear)

end

lemma sorted_insort_is_snoc: "sorted xs \<Longrightarrow> \<forall>x \<in> set xs. a \<ge> x \<Longrightarrow> insort a xs = xs @ [a]"
 by (induct xs) (auto dest!: insort_is_Cons)


subsubsection \<open>Lexicographic combination of measure functions\<close>

text \<open>These are useful for termination proofs\<close>

definition "measures fs = inv_image (lex less_than) (%a. map (%f. f a) fs)"

lemma wf_measures[simp]: "wf (measures fs)"
unfolding measures_def
by blast

lemma in_measures[simp]:
  "(x, y) \<in> measures [] = False"
  "(x, y) \<in> measures (f # fs)
         = (f x < f y \<or> (f x = f y \<and> (x, y) \<in> measures fs))"
unfolding measures_def
by auto

lemma measures_less: "f x < f y \<Longrightarrow> (x, y) \<in> measures (f#fs)"
by simp

lemma measures_lesseq: "f x \<le> f y \<Longrightarrow> (x, y) \<in> measures fs \<Longrightarrow> (x, y) \<in> measures (f#fs)"
by auto


subsubsection \<open>Lifting Relations to Lists: one element\<close>

definition listrel1 :: "('a \<times> 'a) set \<Rightarrow> ('a list \<times> 'a list) set" where
"listrel1 r = {(xs,ys).
   \<exists>us z z' vs. xs = us @ z # vs \<and> (z,z') \<in> r \<and> ys = us @ z' # vs}"

lemma listrel1I:
  "\<lbrakk> (x, y) \<in> r;  xs = us @ x # vs;  ys = us @ y # vs \<rbrakk> \<Longrightarrow>
  (xs, ys) \<in> listrel1 r"
unfolding listrel1_def by auto

lemma listrel1E:
  "\<lbrakk> (xs, ys) \<in> listrel1 r;
     !!x y us vs. \<lbrakk> (x, y) \<in> r;  xs = us @ x # vs;  ys = us @ y # vs \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
unfolding listrel1_def by auto

lemma not_Nil_listrel1 [iff]: "([], xs) \<notin> listrel1 r"
unfolding listrel1_def by blast

lemma not_listrel1_Nil [iff]: "(xs, []) \<notin> listrel1 r"
unfolding listrel1_def by blast

lemma Cons_listrel1_Cons [iff]:
  "(x # xs, y # ys) \<in> listrel1 r \<longleftrightarrow>
   (x,y) \<in> r \<and> xs = ys \<or> x = y \<and> (xs, ys) \<in> listrel1 r"
by (simp add: listrel1_def Cons_eq_append_conv) (blast)

lemma listrel1I1: "(x,y) \<in> r \<Longrightarrow> (x # xs, y # xs) \<in> listrel1 r"
by fast

lemma listrel1I2: "(xs, ys) \<in> listrel1 r \<Longrightarrow> (x # xs, x # ys) \<in> listrel1 r"
by fast

lemma append_listrel1I:
  "(xs, ys) \<in> listrel1 r \<and> us = vs \<or> xs = ys \<and> (us, vs) \<in> listrel1 r
    \<Longrightarrow> (xs @ us, ys @ vs) \<in> listrel1 r"
unfolding listrel1_def
by auto (blast intro: append_eq_appendI)+

lemma Cons_listrel1E1[elim!]:
  assumes "(x # xs, ys) \<in> listrel1 r"
    and "\<And>y. ys = y # xs \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> R"
    and "\<And>zs. ys = x # zs \<Longrightarrow> (xs, zs) \<in> listrel1 r \<Longrightarrow> R"
  shows R
using assms by (cases ys) blast+

lemma Cons_listrel1E2[elim!]:
  assumes "(xs, y # ys) \<in> listrel1 r"
    and "\<And>x. xs = x # ys \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> R"
    and "\<And>zs. xs = y # zs \<Longrightarrow> (zs, ys) \<in> listrel1 r \<Longrightarrow> R"
  shows R
using assms by (cases xs) blast+

lemma snoc_listrel1_snoc_iff:
  "(xs @ [x], ys @ [y]) \<in> listrel1 r
    \<longleftrightarrow> (xs, ys) \<in> listrel1 r \<and> x = y \<or> xs = ys \<and> (x,y) \<in> r" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R
    by (fastforce simp: listrel1_def snoc_eq_iff_butlast butlast_append)
next
  assume ?R then show ?L unfolding listrel1_def by force
qed

lemma listrel1_eq_len: "(xs,ys) \<in> listrel1 r \<Longrightarrow> length xs = length ys"
unfolding listrel1_def by auto

lemma listrel1_mono:
  "r \<subseteq> s \<Longrightarrow> listrel1 r \<subseteq> listrel1 s"
unfolding listrel1_def by blast


lemma listrel1_converse: "listrel1 (r\<inverse>) = (listrel1 r)\<inverse>"
unfolding listrel1_def by blast

lemma in_listrel1_converse:
  "(x,y) \<in> listrel1 (r\<inverse>) \<longleftrightarrow> (x,y) \<in> (listrel1 r)\<inverse>"
unfolding listrel1_def by blast

lemma listrel1_iff_update:
  "(xs,ys) \<in> (listrel1 r)
   \<longleftrightarrow> (\<exists>y n. (xs ! n, y) \<in> r \<and> n < length xs \<and> ys = xs[n:=y])" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?L"
  then obtain x y u v where "xs = u @ x # v"  "ys = u @ y # v"  "(x,y) \<in> r"
    unfolding listrel1_def by auto
  then have "ys = xs[length u := y]" and "length u < length xs"
    and "(xs ! length u, y) \<in> r" by auto
  then show "?R" by auto
next
  assume "?R"
  then obtain x y n where "(xs!n, y) \<in> r" "n < size xs" "ys = xs[n:=y]" "x = xs!n"
    by auto
  then obtain u v where "xs = u @ x # v" and "ys = u @ y # v" and "(x, y) \<in> r"
    by (auto intro: upd_conv_take_nth_drop id_take_nth_drop)
  then show "?L" by (auto simp: listrel1_def)
qed


text\<open>Accessible part and wellfoundedness:\<close>

lemma Cons_acc_listrel1I [intro!]:
  "x \<in> Wellfounded.acc r \<Longrightarrow> xs \<in> Wellfounded.acc (listrel1 r) \<Longrightarrow> (x # xs) \<in> Wellfounded.acc (listrel1 r)"
apply (induct arbitrary: xs set: Wellfounded.acc)
apply (erule thin_rl)
apply (erule acc_induct)
  apply (rule accI)
apply (blast)
done

lemma lists_accD: "xs \<in> lists (Wellfounded.acc r) \<Longrightarrow> xs \<in> Wellfounded.acc (listrel1 r)"
proof (induct set: lists)
  case Nil
  then show ?case
    by (meson acc.intros not_listrel1_Nil)
next
  case (Cons a l)
  then show ?case
    by blast
qed

lemma lists_accI: "xs \<in> Wellfounded.acc (listrel1 r) \<Longrightarrow> xs \<in> lists (Wellfounded.acc r)"
apply (induct set: Wellfounded.acc)
apply clarify
apply (rule accI)
apply (fastforce dest!: in_set_conv_decomp[THEN iffD1] simp: listrel1_def)
done

lemma wf_listrel1_iff[simp]: "wf(listrel1 r) = wf r"
by (auto simp: wf_acc_iff
      intro: lists_accD lists_accI[THEN Cons_in_lists_iff[THEN iffD1, THEN conjunct1]])

subsubsection \<open>Lifting Relations to Lists: all elements\<close>

inductive_set
  listrel :: "('a \<times> 'b) set \<Rightarrow> ('a list \<times> 'b list) set"
  for r :: "('a \<times> 'b) set"
where
    Nil:  "([],[]) \<in> listrel r"
  | Cons: "\<lbrakk>(x,y) \<in> r; (xs,ys) \<in> listrel r\<rbrakk> \<Longrightarrow> (x#xs, y#ys) \<in> listrel r"

inductive_cases listrel_Nil1 [elim!]: "([],xs) \<in> listrel r"
inductive_cases listrel_Nil2 [elim!]: "(xs,[]) \<in> listrel r"
inductive_cases listrel_Cons1 [elim!]: "(y#ys,xs) \<in> listrel r"
inductive_cases listrel_Cons2 [elim!]: "(xs,y#ys) \<in> listrel r"


lemma listrel_eq_len:  "(xs, ys) \<in> listrel r \<Longrightarrow> length xs = length ys"
  by(induct rule: listrel.induct) auto

lemma listrel_iff_zip [code_unfold]: "(xs,ys) \<in> listrel r \<longleftrightarrow>
  length xs = length ys \<and> (\<forall>(x,y) \<in> set(zip xs ys). (x,y) \<in> r)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R by induct (auto intro: listrel_eq_len)
next
  assume ?R thus ?L
    apply (clarify)
    by (induct rule: list_induct2) (auto intro: listrel.intros)
qed

lemma listrel_iff_nth: "(xs,ys) \<in> listrel r \<longleftrightarrow>
  length xs = length ys \<and> (\<forall>n < length xs. (xs!n, ys!n) \<in> r)" (is "?L \<longleftrightarrow> ?R")
  by (auto simp add: all_set_conv_all_nth listrel_iff_zip)

lemma listrel_mono: "r \<subseteq> s \<Longrightarrow> listrel r \<subseteq> listrel s"
  by (meson listrel_iff_nth subrelI subset_eq)

lemma listrel_subset:
  assumes "r \<subseteq> A \<times> A" shows "listrel r \<subseteq> lists A \<times> lists A"
proof clarify
  show "a \<in> lists A \<and> b \<in> lists A" if "(a, b) \<in> listrel r" for a b
    using that assms by (induction rule: listrel.induct, auto)
qed

lemma listrel_refl_on:
  assumes "refl_on A r" shows "refl_on (lists A) (listrel r)"
proof -
  have "l \<in> lists A \<Longrightarrow> (l, l) \<in> listrel r" for l
    using assms unfolding refl_on_def
    by (induction l, auto intro: listrel.intros)
  then show ?thesis
    by (meson assms listrel_subset refl_on_def)
qed

lemma listrel_sym: "sym r \<Longrightarrow> sym (listrel r)"
  by (simp add: listrel_iff_nth sym_def)

lemma listrel_trans:
  assumes "trans r" shows "trans (listrel r)"
proof -
  have "(x, z) \<in> listrel r" if "(x, y) \<in> listrel r" "(y, z) \<in> listrel r" for x y z
    using that
  proof induction
    case (Cons x y xs ys)
    then show ?case
      by clarsimp (metis assms listrel.Cons listrel_iff_nth transD)
  qed auto
  then show ?thesis
    using transI by blast
qed

theorem equiv_listrel: "equiv A r \<Longrightarrow> equiv (lists A) (listrel r)"
  by (simp add: equiv_def listrel_refl_on listrel_sym listrel_trans)

lemma listrel_rtrancl_refl[iff]: "(xs,xs) \<in> listrel(r\<^sup>*)"
  using listrel_refl_on[of UNIV, OF refl_rtrancl]
  by(auto simp: refl_on_def)

lemma listrel_rtrancl_trans:
  "\<lbrakk>(xs,ys) \<in> listrel(r\<^sup>*);  (ys,zs) \<in> listrel(r\<^sup>*)\<rbrakk> \<Longrightarrow> (xs,zs) \<in> listrel(r\<^sup>*)"
  by (metis listrel_trans trans_def trans_rtrancl)

lemma listrel_Nil [simp]: "listrel r `` {[]} = {[]}"
  by (blast intro: listrel.intros)

lemma listrel_Cons:
  "listrel r `` {x#xs} = set_Cons (r``{x}) (listrel r `` {xs})"
  by (auto simp add: set_Cons_def intro: listrel.intros)

text \<open>Relating \<^term>\<open>listrel1\<close>, \<^term>\<open>listrel\<close> and closures:\<close>

lemma listrel1_rtrancl_subset_rtrancl_listrel1: "listrel1 (r\<^sup>*) \<subseteq> (listrel1 r)\<^sup>*"
proof (rule subrelI)
  fix xs ys assume 1: "(xs,ys) \<in> listrel1 (r\<^sup>*)"
  { fix x y us vs
    have "(x,y) \<in> r\<^sup>* \<Longrightarrow> (us @ x # vs, us @ y # vs) \<in> (listrel1 r)\<^sup>*"
    proof(induct rule: rtrancl.induct)
      case rtrancl_refl show ?case by simp
    next
      case rtrancl_into_rtrancl thus ?case
        by (metis listrel1I rtrancl.rtrancl_into_rtrancl)
    qed }
  thus "(xs,ys) \<in> (listrel1 r)\<^sup>*" using 1 by(blast elim: listrel1E)
qed

lemma rtrancl_listrel1_eq_len: "(x,y) \<in> (listrel1 r)\<^sup>* \<Longrightarrow> length x = length y"
  by (induct rule: rtrancl.induct) (auto intro: listrel1_eq_len)

lemma rtrancl_listrel1_ConsI1:
  "(xs,ys) \<in> (listrel1 r)\<^sup>* \<Longrightarrow> (x#xs,x#ys) \<in> (listrel1 r)\<^sup>*"
proof (induction rule: rtrancl.induct)
  case (rtrancl_into_rtrancl a b c)
  then show ?case
    by (metis listrel1I2 rtrancl.rtrancl_into_rtrancl)
qed auto

lemma rtrancl_listrel1_ConsI2:
  "(x,y) \<in> r\<^sup>* \<Longrightarrow> (xs, ys) \<in> (listrel1 r)\<^sup>* \<Longrightarrow> (x # xs, y # ys) \<in> (listrel1 r)\<^sup>*"
  by (meson in_mono listrel1I1 listrel1_rtrancl_subset_rtrancl_listrel1 rtrancl_listrel1_ConsI1 rtrancl_trans)

lemma listrel1_subset_listrel:
  "r \<subseteq> r' \<Longrightarrow> refl r' \<Longrightarrow> listrel1 r \<subseteq> listrel(r')"
  by(auto elim!: listrel1E simp add: listrel_iff_zip set_zip refl_on_def)

lemma listrel_reflcl_if_listrel1:
  "(xs,ys) \<in> listrel1 r \<Longrightarrow> (xs,ys) \<in> listrel(r\<^sup>*)"
  by(erule listrel1E)(auto simp add: listrel_iff_zip set_zip)

lemma listrel_rtrancl_eq_rtrancl_listrel1: "listrel (r\<^sup>*) = (listrel1 r)\<^sup>*"
proof
  { fix x y assume "(x,y) \<in> listrel (r\<^sup>*)"
    then have "(x,y) \<in> (listrel1 r)\<^sup>*"
    by induct (auto intro: rtrancl_listrel1_ConsI2) }
  then show "listrel (r\<^sup>*) \<subseteq> (listrel1 r)\<^sup>*"
    by (rule subrelI)
next
  show "listrel (r\<^sup>*) \<supseteq> (listrel1 r)\<^sup>*"
  proof(rule subrelI)
    fix xs ys assume "(xs,ys) \<in> (listrel1 r)\<^sup>*"
    then show "(xs,ys) \<in> listrel (r\<^sup>*)"
    proof induct
      case base show ?case by(auto simp add: listrel_iff_zip set_zip)
    next
      case (step ys zs)
      thus ?case by (metis listrel_reflcl_if_listrel1 listrel_rtrancl_trans)
    qed
  qed
qed

lemma rtrancl_listrel1_if_listrel:
  "(xs,ys) \<in> listrel r \<Longrightarrow> (xs,ys) \<in> (listrel1 r)\<^sup>*"
  by(metis listrel_rtrancl_eq_rtrancl_listrel1 subsetD[OF listrel_mono] r_into_rtrancl subsetI)

lemma listrel_subset_rtrancl_listrel1: "listrel r \<subseteq> (listrel1 r)\<^sup>*"
  by(fast intro:rtrancl_listrel1_if_listrel)


subsection \<open>Size function\<close>

lemma [measure_function]: "is_measure f \<Longrightarrow> is_measure (size_list f)"
  by (rule is_measure_trivial)

lemma [measure_function]: "is_measure f \<Longrightarrow> is_measure (size_option f)"
  by (rule is_measure_trivial)

lemma size_list_estimation[termination_simp]:
  "x \<in> set xs \<Longrightarrow> y < f x \<Longrightarrow> y < size_list f xs"
  by (induct xs) auto

lemma size_list_estimation'[termination_simp]:
  "x \<in> set xs \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_list f xs"
  by (induct xs) auto

lemma size_list_map[simp]: "size_list f (map g xs) = size_list (f \<circ> g) xs"
  by (induct xs) auto

lemma size_list_append[simp]: "size_list f (xs @ ys) = size_list f xs + size_list f ys"
  by (induct xs, auto)

lemma size_list_pointwise[termination_simp]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> size_list f xs \<le> size_list g xs"
  by (induct xs) force+


subsection \<open>Monad operation\<close>

definition bind :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'b list" where
"bind xs f = concat (map f xs)"

hide_const (open) bind

lemma bind_simps [simp]:
  "List.bind [] f = []"
  "List.bind (x # xs) f = f x @ List.bind xs f"
  by (simp_all add: bind_def)

lemma list_bind_cong [fundef_cong]:
  assumes "xs = ys" "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)"
  shows   "List.bind xs f = List.bind ys g"
proof -
  from assms(2) have "List.bind xs f = List.bind xs g"
    by (induction xs) simp_all
  with assms(1) show ?thesis by simp
qed

lemma set_list_bind: "set (List.bind xs f) = (\<Union>x\<in>set xs. set (f x))"
  by (induction xs) simp_all


subsection \<open>Code generation\<close>

text\<open>Optional tail recursive version of \<^const>\<open>map\<close>. Can avoid
stack overflow in some target languages.\<close>

fun map_tailrec_rev ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
"map_tailrec_rev f [] bs = bs" |
"map_tailrec_rev f (a#as) bs = map_tailrec_rev f as (f a # bs)"

lemma map_tailrec_rev:
  "map_tailrec_rev f as bs = rev(map f as) @ bs"
by(induction as arbitrary: bs) simp_all

definition map_tailrec :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map_tailrec f as = rev (map_tailrec_rev f as [])"

text\<open>Code equation:\<close>
lemma map_eq_map_tailrec: "map = map_tailrec"
by(simp add: fun_eq_iff map_tailrec_def map_tailrec_rev)


subsubsection \<open>Counterparts for set-related operations\<close>

definition member :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
[code_abbrev]: "member xs x \<longleftrightarrow> x \<in> set xs"

text \<open>
  Use \<open>member\<close> only for generating executable code.  Otherwise use
  \<^prop>\<open>x \<in> set xs\<close> instead --- it is much easier to reason about.
\<close>

lemma member_rec [code]:
  "member (x # xs) y \<longleftrightarrow> x = y \<or> member xs y"
  "member [] y \<longleftrightarrow> False"
  by (auto simp add: member_def)

lemma in_set_member (* FIXME delete candidate *):
  "x \<in> set xs \<longleftrightarrow> member xs x"
  by (simp add: member_def)

lemmas list_all_iff [code_abbrev] = fun_cong[OF list.pred_set]

definition list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
list_ex_iff [code_abbrev]: "list_ex P xs \<longleftrightarrow> Bex (set xs) P"

definition list_ex1 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
list_ex1_iff [code_abbrev]: "list_ex1 P xs \<longleftrightarrow> (\<exists>! x. x \<in> set xs \<and> P x)"

text \<open>
  Usually you should prefer \<open>\<forall>x\<in>set xs\<close>, \<open>\<exists>x\<in>set xs\<close>
  and \<open>\<exists>!x. x\<in>set xs \<and> _\<close> over \<^const>\<open>list_all\<close>, \<^const>\<open>list_ex\<close>
  and \<^const>\<open>list_ex1\<close> in specifications.
\<close>

lemma list_all_simps [code]:
  "list_all P (x # xs) \<longleftrightarrow> P x \<and> list_all P xs"
  "list_all P [] \<longleftrightarrow> True"
  by (simp_all add: list_all_iff)

lemma list_ex_simps [simp, code]:
  "list_ex P (x # xs) \<longleftrightarrow> P x \<or> list_ex P xs"
  "list_ex P [] \<longleftrightarrow> False"
  by (simp_all add: list_ex_iff)

lemma list_ex1_simps [simp, code]:
  "list_ex1 P [] = False"
  "list_ex1 P (x # xs) = (if P x then list_all (\<lambda>y. \<not> P y \<or> x = y) xs else list_ex1 P xs)"
  by (auto simp add: list_ex1_iff list_all_iff)

lemma Ball_set_list_all: (* FIXME delete candidate *)
  "Ball (set xs) P \<longleftrightarrow> list_all P xs"
  by (simp add: list_all_iff)

lemma Bex_set_list_ex: (* FIXME delete candidate *)
  "Bex (set xs) P \<longleftrightarrow> list_ex P xs"
  by (simp add: list_ex_iff)

lemma list_all_append [simp]:
  "list_all P (xs @ ys) \<longleftrightarrow> list_all P xs \<and> list_all P ys"
  by (auto simp add: list_all_iff)

lemma list_ex_append [simp]:
  "list_ex P (xs @ ys) \<longleftrightarrow> list_ex P xs \<or> list_ex P ys"
  by (auto simp add: list_ex_iff)

lemma list_all_rev [simp]:
  "list_all P (rev xs) \<longleftrightarrow> list_all P xs"
  by (simp add: list_all_iff)

lemma list_ex_rev [simp]:
  "list_ex P (rev xs) \<longleftrightarrow> list_ex P xs"
  by (simp add: list_ex_iff)

lemma list_all_length:
  "list_all P xs \<longleftrightarrow> (\<forall>n < length xs. P (xs ! n))"
  by (auto simp add: list_all_iff set_conv_nth)

lemma list_ex_length:
  "list_ex P xs \<longleftrightarrow> (\<exists>n < length xs. P (xs ! n))"
  by (auto simp add: list_ex_iff set_conv_nth)

lemmas list_all_cong [fundef_cong] = list.pred_cong

lemma list_ex_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x. x \<in> set ys \<Longrightarrow> f x = g x) \<Longrightarrow> list_ex f xs = list_ex g ys"
by (simp add: list_ex_iff)

definition can_select :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
[code_abbrev]: "can_select P A = (\<exists>!x\<in>A. P x)"

lemma can_select_set_list_ex1 [code]:
  "can_select P (set A) = list_ex1 P A"
  by (simp add: list_ex1_iff can_select_def)


text \<open>Executable checks for relations on sets\<close>

definition listrel1p :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"listrel1p r xs ys = ((xs, ys) \<in> listrel1 {(x, y). r x y})"

lemma [code_unfold]:
  "(xs, ys) \<in> listrel1 r = listrel1p (\<lambda>x y. (x, y) \<in> r) xs ys"
unfolding listrel1p_def by auto

lemma [code]:
  "listrel1p r [] xs = False"
  "listrel1p r xs [] =  False"
  "listrel1p r (x # xs) (y # ys) \<longleftrightarrow>
     r x y \<and> xs = ys \<or> x = y \<and> listrel1p r xs ys"
by (simp add: listrel1p_def)+

definition
  lexordp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "lexordp r xs ys = ((xs, ys) \<in> lexord {(x, y). r x y})"

lemma [code_unfold]:
  "(xs, ys) \<in> lexord r = lexordp (\<lambda>x y. (x, y) \<in> r) xs ys"
unfolding lexordp_def by auto

lemma [code]:
  "lexordp r xs [] = False"
  "lexordp r [] (y#ys) = True"
  "lexordp r (x # xs) (y # ys) = (r x y \<or> (x = y \<and> lexordp r xs ys))"
unfolding lexordp_def by auto

text \<open>Bounded quantification and summation over nats.\<close>

lemma atMost_upto [code_unfold]:
  "{..n} = set [0..<Suc n]"
  by auto

lemma atLeast_upt [code_unfold]:
  "{..<n} = set [0..<n]"
  by auto

lemma greaterThanLessThan_upt [code_unfold]:
  "{n<..<m} = set [Suc n..<m]"
  by auto

lemmas atLeastLessThan_upt [code_unfold] = set_upt [symmetric]

lemma greaterThanAtMost_upt [code_unfold]:
  "{n<..m} = set [Suc n..<Suc m]"
  by auto

lemma atLeastAtMost_upt [code_unfold]:
  "{n..m} = set [n..<Suc m]"
  by auto

lemma all_nat_less_eq [code_unfold]:
  "(\<forall>m<n::nat. P m) \<longleftrightarrow> (\<forall>m \<in> {0..<n}. P m)"
  by auto

lemma ex_nat_less_eq [code_unfold]:
  "(\<exists>m<n::nat. P m) \<longleftrightarrow> (\<exists>m \<in> {0..<n}. P m)"
  by auto

lemma all_nat_less [code_unfold]:
  "(\<forall>m\<le>n::nat. P m) \<longleftrightarrow> (\<forall>m \<in> {0..n}. P m)"
  by auto

lemma ex_nat_less [code_unfold]:
  "(\<exists>m\<le>n::nat. P m) \<longleftrightarrow> (\<exists>m \<in> {0..n}. P m)"
  by auto

text\<open>Bounded \<open>LEAST\<close> operator:\<close>

definition "Bleast S P = (LEAST x. x \<in> S \<and> P x)"

definition "abort_Bleast S P = (LEAST x. x \<in> S \<and> P x)"

declare [[code abort: abort_Bleast]]

lemma Bleast_code [code]:
 "Bleast (set xs) P = (case filter P (sort xs) of
    x#xs \<Rightarrow> x |
    [] \<Rightarrow> abort_Bleast (set xs) P)"
proof (cases "filter P (sort xs)")
  case Nil thus ?thesis by (simp add: Bleast_def abort_Bleast_def)
next
  case (Cons x ys)
  have "(LEAST x. x \<in> set xs \<and> P x) = x"
  proof (rule Least_equality)
    show "x \<in> set xs \<and> P x"
      by (metis Cons Cons_eq_filter_iff in_set_conv_decomp set_sort)
    next
      fix y assume "y \<in> set xs \<and> P y"
      hence "y \<in> set (filter P xs)" by auto
      thus "x \<le> y"
        by (metis Cons eq_iff filter_sort set_ConsD set_sort sorted.simps(2) sorted_sort)
  qed
  thus ?thesis using Cons by (simp add: Bleast_def)
qed

declare Bleast_def[symmetric, code_unfold]

text \<open>Summation over ints.\<close>

lemma greaterThanLessThan_upto [code_unfold]:
  "{i<..<j::int} = set [i+1..j - 1]"
by auto

lemma atLeastLessThan_upto [code_unfold]:
  "{i..<j::int} = set [i..j - 1]"
by auto

lemma greaterThanAtMost_upto [code_unfold]:
  "{i<..j::int} = set [i+1..j]"
by auto

lemmas atLeastAtMost_upto [code_unfold] = set_upto [symmetric]


subsubsection \<open>Optimizing by rewriting\<close>

definition null :: "'a list \<Rightarrow> bool" where
  [code_abbrev]: "null xs \<longleftrightarrow> xs = []"

text \<open>
  Efficient emptyness check is implemented by \<^const>\<open>null\<close>.
\<close>

lemma null_rec [code]:
  "null (x # xs) \<longleftrightarrow> False"
  "null [] \<longleftrightarrow> True"
  by (simp_all add: null_def)

lemma eq_Nil_null: (* FIXME delete candidate *)
  "xs = [] \<longleftrightarrow> null xs"
  by (simp add: null_def)

lemma equal_Nil_null [code_unfold]:
  "HOL.equal xs [] \<longleftrightarrow> null xs"
  "HOL.equal [] = null"
  by (auto simp add: equal null_def)

definition maps :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  [code_abbrev]: "maps f xs = concat (map f xs)"

definition map_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  [code_post]: "map_filter f xs = map (the \<circ> f) (filter (\<lambda>x. f x \<noteq> None) xs)"

text \<open>
  Operations \<^const>\<open>maps\<close> and \<^const>\<open>map_filter\<close> avoid
  intermediate lists on execution -- do not use for proving.
\<close>

lemma maps_simps [code]:
  "maps f (x # xs) = f x @ maps f xs"
  "maps f [] = []"
  by (simp_all add: maps_def)

lemma map_filter_simps [code]:
  "map_filter f (x # xs) = (case f x of None \<Rightarrow> map_filter f xs | Some y \<Rightarrow> y # map_filter f xs)"
  "map_filter f [] = []"
  by (simp_all add: map_filter_def split: option.split)

lemma concat_map_maps: (* FIXME delete candidate *)
  "concat (map f xs) = maps f xs"
  by (simp add: maps_def)

lemma map_filter_map_filter [code_unfold]:
  "map f (filter P xs) = map_filter (\<lambda>x. if P x then Some (f x) else None) xs"
  by (simp add: map_filter_def)

text \<open>Optimized code for \<open>\<forall>i\<in>{a..b::int}\<close> and \<open>\<forall>n:{a..<b::nat}\<close>
and similiarly for \<open>\<exists>\<close>.\<close>

definition all_interval_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "all_interval_nat P i j \<longleftrightarrow> (\<forall>n \<in> {i..<j}. P n)"

lemma [code]:
  "all_interval_nat P i j \<longleftrightarrow> i \<ge> j \<or> P i \<and> all_interval_nat P (Suc i) j"
proof -
  have *: "\<And>n. P i \<Longrightarrow> \<forall>n\<in>{Suc i..<j}. P n \<Longrightarrow> i \<le> n \<Longrightarrow> n < j \<Longrightarrow> P n"
  proof -
    fix n
    assume "P i" "\<forall>n\<in>{Suc i..<j}. P n" "i \<le> n" "n < j"
    then show "P n" by (cases "n = i") simp_all
  qed
  show ?thesis by (auto simp add: all_interval_nat_def intro: *)
qed

lemma list_all_iff_all_interval_nat [code_unfold]:
  "list_all P [i..<j] \<longleftrightarrow> all_interval_nat P i j"
  by (simp add: list_all_iff all_interval_nat_def)

lemma list_ex_iff_not_all_inverval_nat [code_unfold]:
  "list_ex P [i..<j] \<longleftrightarrow> \<not> (all_interval_nat (Not \<circ> P) i j)"
  by (simp add: list_ex_iff all_interval_nat_def)

definition all_interval_int :: "(int \<Rightarrow> bool) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "all_interval_int P i j \<longleftrightarrow> (\<forall>k \<in> {i..j}. P k)"

lemma [code]:
  "all_interval_int P i j \<longleftrightarrow> i > j \<or> P i \<and> all_interval_int P (i + 1) j"
proof -
  have *: "\<And>k. P i \<Longrightarrow> \<forall>k\<in>{i+1..j}. P k \<Longrightarrow> i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> P k"
  proof -
    fix k
    assume "P i" "\<forall>k\<in>{i+1..j}. P k" "i \<le> k" "k \<le> j"
    then show "P k" by (cases "k = i") simp_all
  qed
  show ?thesis by (auto simp add: all_interval_int_def intro: *)
qed

lemma list_all_iff_all_interval_int [code_unfold]:
  "list_all P [i..j] \<longleftrightarrow> all_interval_int P i j"
  by (simp add: list_all_iff all_interval_int_def)

lemma list_ex_iff_not_all_inverval_int [code_unfold]:
  "list_ex P [i..j] \<longleftrightarrow> \<not> (all_interval_int (Not \<circ> P) i j)"
  by (simp add: list_ex_iff all_interval_int_def)

text \<open>optimized code (tail-recursive) for \<^term>\<open>length\<close>\<close>

definition gen_length :: "nat \<Rightarrow> 'a list \<Rightarrow> nat"
where "gen_length n xs = n + length xs"

lemma gen_length_code [code]:
  "gen_length n [] = n"
  "gen_length n (x # xs) = gen_length (Suc n) xs"
by(simp_all add: gen_length_def)

declare list.size(3-4)[code del]

lemma length_code [code]: "length = gen_length 0"
by(simp add: gen_length_def fun_eq_iff)

hide_const (open) member null maps map_filter all_interval_nat all_interval_int gen_length


subsubsection \<open>Pretty lists\<close>

ML \<open>
(* Code generation for list literals. *)

signature LIST_CODE =
sig
  val add_literal_list: string -> theory -> theory
end;

structure List_Code : LIST_CODE =
struct

open Basic_Code_Thingol;

fun implode_list t =
  let
    fun dest_cons (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Cons\<close>, ... } `$ t1 `$ t2) = SOME (t1, t2)
      | dest_cons _ = NONE;
    val (ts, t') = Code_Thingol.unfoldr dest_cons t;
  in case t'
   of IConst { sym = Code_Symbol.Constant \<^const_name>\<open>Nil\<close>, ... } => SOME ts
    | _ => NONE
  end;

fun print_list (target_fxy, target_cons) pr fxy t1 t2 =
  Code_Printer.brackify_infix (target_fxy, Code_Printer.R) fxy (
    pr (Code_Printer.INFX (target_fxy, Code_Printer.X)) t1,
    Code_Printer.str target_cons,
    pr (Code_Printer.INFX (target_fxy, Code_Printer.R)) t2
  );

fun add_literal_list target =
  let
    fun pretty literals pr _ vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list t2)
       of SOME ts =>
            Code_Printer.literal_list literals (map (pr vars Code_Printer.NOBR) ts)
        | NONE =>
            print_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in
    Code_Target.set_printings (Code_Symbol.Constant (\<^const_name>\<open>Cons\<close>,
      [(target, SOME (Code_Printer.complex_const_syntax (2, pretty)))]))
  end

end;
\<close>

code_printing
  type_constructor list \<rightharpoonup>
    (SML) "_ list"
    and (OCaml) "_ list"
    and (Haskell) "![(_)]"
    and (Scala) "List[(_)]"
| constant Nil \<rightharpoonup>
    (SML) "[]"
    and (OCaml) "[]"
    and (Haskell) "[]"
    and (Scala) "!Nil"
| class_instance list :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: 'a list \<Rightarrow> 'a list \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) infix 4 "=="

setup \<open>fold (List_Code.add_literal_list) ["SML", "OCaml", "Haskell", "Scala"]\<close>

code_reserved SML
  list

code_reserved OCaml
  list


subsubsection \<open>Use convenient predefined operations\<close>

code_printing
  constant "(@)" \<rightharpoonup>
    (SML) infixr 7 "@"
    and (OCaml) infixr 6 "@"
    and (Haskell) infixr 5 "++"
    and (Scala) infixl 7 "++"
| constant map \<rightharpoonup>
    (Haskell) "map"
| constant filter \<rightharpoonup>
    (Haskell) "filter"
| constant concat \<rightharpoonup>
    (Haskell) "concat"
| constant List.maps \<rightharpoonup>
    (Haskell) "concatMap"
| constant rev \<rightharpoonup>
    (Haskell) "reverse"
| constant zip \<rightharpoonup>
    (Haskell) "zip"
| constant List.null \<rightharpoonup>
    (Haskell) "null"
| constant takeWhile \<rightharpoonup>
    (Haskell) "takeWhile"
| constant dropWhile \<rightharpoonup>
    (Haskell) "dropWhile"
| constant list_all \<rightharpoonup>
    (Haskell) "all"
| constant list_ex \<rightharpoonup>
    (Haskell) "any"


subsubsection \<open>Implementation of sets by lists\<close>

lemma is_empty_set [code]:
  "Set.is_empty (set xs) \<longleftrightarrow> List.null xs"
  by (simp add: Set.is_empty_def null_def)

lemma empty_set [code]:
  "{} = set []"
  by simp

lemma UNIV_coset [code]:
  "UNIV = List.coset []"
  by simp

lemma compl_set [code]:
  "- set xs = List.coset xs"
  by simp

lemma compl_coset [code]:
  "- List.coset xs = set xs"
  by simp

lemma [code]:
  "x \<in> set xs \<longleftrightarrow> List.member xs x"
  "x \<in> List.coset xs \<longleftrightarrow> \<not> List.member xs x"
  by (simp_all add: member_def)

lemma insert_code [code]:
  "insert x (set xs) = set (List.insert x xs)"
  "insert x (List.coset xs) = List.coset (removeAll x xs)"
  by simp_all

lemma remove_code [code]:
  "Set.remove x (set xs) = set (removeAll x xs)"
  "Set.remove x (List.coset xs) = List.coset (List.insert x xs)"
  by (simp_all add: remove_def Compl_insert)

lemma filter_set [code]:
  "Set.filter P (set xs) = set (filter P xs)"
  by auto

lemma image_set [code]:
  "image f (set xs) = set (map f xs)"
  by simp

lemma subset_code [code]:
  "set xs \<le> B \<longleftrightarrow> (\<forall>x\<in>set xs. x \<in> B)"
  "A \<le> List.coset ys \<longleftrightarrow> (\<forall>y\<in>set ys. y \<notin> A)"
  "List.coset [] \<subseteq> set [] \<longleftrightarrow> False"
  by auto

text \<open>A frequent case -- avoid intermediate sets\<close>
lemma [code_unfold]:
  "set xs \<subseteq> set ys \<longleftrightarrow> list_all (\<lambda>x. x \<in> set ys) xs"
  by (auto simp: list_all_iff)

lemma Ball_set [code]:
  "Ball (set xs) P \<longleftrightarrow> list_all P xs"
  by (simp add: list_all_iff)

lemma Bex_set [code]:
  "Bex (set xs) P \<longleftrightarrow> list_ex P xs"
  by (simp add: list_ex_iff)

lemma card_set [code]:
  "card (set xs) = length (remdups xs)"
proof -
  have "card (set (remdups xs)) = length (remdups xs)"
    by (rule distinct_card) simp
  then show ?thesis by simp
qed

lemma the_elem_set [code]:
  "the_elem (set [x]) = x"
  by simp

lemma Pow_set [code]:
  "Pow (set []) = {{}}"
  "Pow (set (x # xs)) = (let A = Pow (set xs) in A \<union> insert x ` A)"
  by (simp_all add: Pow_insert Let_def)

definition map_project :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "map_project f A = {b. \<exists> a \<in> A. f a = Some b}"

lemma [code]:
  "map_project f (set xs) = set (List.map_filter f xs)"
  by (auto simp add: map_project_def map_filter_def image_def)

hide_const (open) map_project


text \<open>Operations on relations\<close>

lemma product_code [code]:
  "Product_Type.product (set xs) (set ys) = set [(x, y). x \<leftarrow> xs, y \<leftarrow> ys]"
  by (auto simp add: Product_Type.product_def)

lemma Id_on_set [code]:
  "Id_on (set xs) = set [(x, x). x \<leftarrow> xs]"
  by (auto simp add: Id_on_def)

lemma [code]:
  "R `` S = List.map_project (\<lambda>(x, y). if x \<in> S then Some y else None) R"
unfolding map_project_def by (auto split: prod.split if_split_asm)

lemma trancl_set_ntrancl [code]:
  "trancl (set xs) = ntrancl (card (set xs) - 1) (set xs)"
  by (simp add: finite_trancl_ntranl)

lemma set_relcomp [code]:
  "set xys O set yzs = set ([(fst xy, snd yz). xy \<leftarrow> xys, yz \<leftarrow> yzs, snd xy = fst yz])"
  by auto (auto simp add: Bex_def image_def)

lemma wf_set [code]:
  "wf (set xs) = acyclic (set xs)"
  by (simp add: wf_iff_acyclic_if_finite)


subsection \<open>Setup for Lifting/Transfer\<close>

subsubsection \<open>Transfer rules for the Transfer package\<close>

context includes lifting_syntax
begin

lemma tl_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) tl tl"
  unfolding tl_def[abs_def] by transfer_prover

lemma butlast_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) butlast butlast"
  by (rule rel_funI, erule list_all2_induct, auto)

lemma map_rec: "map f xs = rec_list Nil (%x _ y. Cons (f x) y) xs"
  by (induct xs) auto

lemma append_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A ===> list_all2 A) append append"
  unfolding List.append_def by transfer_prover

lemma rev_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) rev rev"
  unfolding List.rev_def by transfer_prover

lemma filter_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> list_all2 A) filter filter"
  unfolding List.filter_def by transfer_prover

lemma fold_transfer [transfer_rule]:
  "((A ===> B ===> B) ===> list_all2 A ===> B ===> B) fold fold"
  unfolding List.fold_def by transfer_prover

lemma foldr_transfer [transfer_rule]:
  "((A ===> B ===> B) ===> list_all2 A ===> B ===> B) foldr foldr"
  unfolding List.foldr_def by transfer_prover

lemma foldl_transfer [transfer_rule]:
  "((B ===> A ===> B) ===> B ===> list_all2 A ===> B) foldl foldl"
  unfolding List.foldl_def by transfer_prover

lemma concat_transfer [transfer_rule]:
  "(list_all2 (list_all2 A) ===> list_all2 A) concat concat"
  unfolding List.concat_def by transfer_prover

lemma drop_transfer [transfer_rule]:
  "((=) ===> list_all2 A ===> list_all2 A) drop drop"
  unfolding List.drop_def by transfer_prover

lemma take_transfer [transfer_rule]:
  "((=) ===> list_all2 A ===> list_all2 A) take take"
  unfolding List.take_def by transfer_prover

lemma list_update_transfer [transfer_rule]:
  "(list_all2 A ===> (=) ===> A ===> list_all2 A) list_update list_update"
  unfolding list_update_def by transfer_prover

lemma takeWhile_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> list_all2 A) takeWhile takeWhile"
  unfolding takeWhile_def by transfer_prover

lemma dropWhile_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> list_all2 A) dropWhile dropWhile"
  unfolding dropWhile_def by transfer_prover

lemma zip_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 B ===> list_all2 (rel_prod A B)) zip zip"
  unfolding zip_def by transfer_prover

lemma product_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 B ===> list_all2 (rel_prod A B)) List.product List.product"
  unfolding List.product_def by transfer_prover

lemma product_lists_transfer [transfer_rule]:
  "(list_all2 (list_all2 A) ===> list_all2 (list_all2 A)) product_lists product_lists"
  unfolding product_lists_def by transfer_prover

lemma insert_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) List.insert List.insert"
  unfolding List.insert_def [abs_def] by transfer_prover

lemma find_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> rel_option A) List.find List.find"
  unfolding List.find_def by transfer_prover

lemma those_transfer [transfer_rule]:
  "(list_all2 (rel_option P) ===> rel_option (list_all2 P)) those those"
  unfolding List.those_def by transfer_prover

lemma remove1_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) remove1 remove1"
  unfolding remove1_def by transfer_prover

lemma removeAll_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) removeAll removeAll"
  unfolding removeAll_def by transfer_prover

lemma successively_transfer [transfer_rule]:
  "((A ===> A ===> (=)) ===> list_all2 A ===> (=)) successively successively"
  unfolding successively_altdef by transfer_prover

lemma distinct_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> (=)) distinct distinct"
  unfolding distinct_def by transfer_prover

lemma distinct_adj_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(list_all2 A ===> (=)) distinct_adj distinct_adj"
  unfolding rel_fun_def
proof (intro allI impI)
  fix xs ys assume "list_all2 A xs ys"
  thus "distinct_adj xs \<longleftrightarrow> distinct_adj ys"
  proof (induction rule: list_all2_induct)
    case (Cons x xs y ys)
    note * = this
    show ?case
    proof (cases xs)
      case [simp]: (Cons x' xs')
      with * obtain y' ys' where [simp]: "ys = y' # ys'"
        by (cases ys) auto
      from * show ?thesis
        using assms by (auto simp: distinct_adj_Cons bi_unique_def)
    qed (use * in auto)
  qed auto
qed

lemma remdups_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A) remdups remdups"
  unfolding remdups_def by transfer_prover

lemma remdups_adj_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A) remdups_adj remdups_adj"
  proof (rule rel_funI, erule list_all2_induct)
  qed (auto simp: remdups_adj_Cons assms[unfolded bi_unique_def] split: list.splits)

lemma replicate_transfer [transfer_rule]:
  "((=) ===> A ===> list_all2 A) replicate replicate"
  unfolding replicate_def by transfer_prover

lemma length_transfer [transfer_rule]:
  "(list_all2 A ===> (=)) length length"
  unfolding size_list_overloaded_def size_list_def by transfer_prover

lemma rotate1_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) rotate1 rotate1"
  unfolding rotate1_def by transfer_prover

lemma rotate_transfer [transfer_rule]:
  "((=) ===> list_all2 A ===> list_all2 A) rotate rotate"
  unfolding rotate_def [abs_def] by transfer_prover

lemma nths_transfer [transfer_rule]:
  "(list_all2 A ===> rel_set (=) ===> list_all2 A) nths nths"
  unfolding nths_def [abs_def] by transfer_prover

lemma subseqs_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 (list_all2 A)) subseqs subseqs"
  unfolding subseqs_def [abs_def] by transfer_prover

lemma partition_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> rel_prod (list_all2 A) (list_all2 A))
    partition partition"
  unfolding partition_def by transfer_prover

lemma lists_transfer [transfer_rule]:
  "(rel_set A ===> rel_set (list_all2 A)) lists lists"
proof (rule rel_funI, rule rel_setI)
  show "\<lbrakk>l \<in> lists X; rel_set A X Y\<rbrakk> \<Longrightarrow> \<exists>y\<in>lists Y. list_all2 A l y" for X Y l
  proof (induction l rule: lists.induct)
    case (Cons a l)
    then show ?case
      by (simp only: rel_set_def list_all2_Cons1, metis lists.Cons)
  qed auto
  show "\<lbrakk>l \<in> lists Y; rel_set A X Y\<rbrakk> \<Longrightarrow> \<exists>x\<in>lists X. list_all2 A x l" for X Y l
  proof (induction l rule: lists.induct)
    case (Cons a l)
    then show ?case
      by (simp only: rel_set_def list_all2_Cons2, metis lists.Cons)
  qed auto
qed

lemma set_Cons_transfer [transfer_rule]:
  "(rel_set A ===> rel_set (list_all2 A) ===> rel_set (list_all2 A))
    set_Cons set_Cons"
  unfolding rel_fun_def rel_set_def set_Cons_def
  by (fastforce simp add: list_all2_Cons1 list_all2_Cons2)

lemma listset_transfer [transfer_rule]:
  "(list_all2 (rel_set A) ===> rel_set (list_all2 A)) listset listset"
  unfolding listset_def by transfer_prover

lemma null_transfer [transfer_rule]:
  "(list_all2 A ===> (=)) List.null List.null"
  unfolding rel_fun_def List.null_def by auto

lemma list_all_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> (=)) list_all list_all"
  unfolding list_all_iff [abs_def] by transfer_prover

lemma list_ex_transfer [transfer_rule]:
  "((A ===> (=)) ===> list_all2 A ===> (=)) list_ex list_ex"
  unfolding list_ex_iff [abs_def] by transfer_prover

lemma splice_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A ===> list_all2 A) splice splice"
  apply (rule rel_funI, erule list_all2_induct, simp add: rel_fun_def, simp)
  apply (rule rel_funI)
  apply (erule_tac xs=x in list_all2_induct, simp, simp add: rel_fun_def)
  done

lemma shuffles_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A ===> rel_set (list_all2 A)) shuffles shuffles"
proof (intro rel_funI, goal_cases)
  case (1 xs xs' ys ys')
  thus ?case
  proof (induction xs ys arbitrary: xs' ys' rule: shuffles.induct)
    case (3 x xs y ys xs' ys')
    from "3.prems" obtain x' xs'' where xs': "xs' = x' # xs''" by (cases xs') auto
    from "3.prems" obtain y' ys'' where ys': "ys' = y' # ys''" by (cases ys') auto
    have [transfer_rule]: "A x x'" "A y y'" "list_all2 A xs xs''" "list_all2 A ys ys''"
      using "3.prems" by (simp_all add: xs' ys')
    have [transfer_rule]: "rel_set (list_all2 A) (shuffles xs (y # ys)) (shuffles xs'' ys')" and
         [transfer_rule]: "rel_set (list_all2 A) (shuffles (x # xs) ys) (shuffles xs' ys'')"
      using "3.prems" by (auto intro!: "3.IH" simp: xs' ys')
    have "rel_set (list_all2 A) ((#) x ` shuffles xs (y # ys) \<union> (#) y ` shuffles (x # xs) ys)
               ((#) x' ` shuffles xs'' ys' \<union> (#) y' ` shuffles xs' ys'')" by transfer_prover
    thus ?case by (simp add: xs' ys')
  qed (auto simp: rel_set_def)
qed

lemma rtrancl_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "bi_total A"
  shows "(rel_set (rel_prod A A) ===> rel_set (rel_prod A A)) rtrancl rtrancl"
unfolding rtrancl_def by transfer_prover

lemma monotone_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> A ===> (=)) ===> (B ===> B ===> (=)) ===> (A ===> B) ===> (=)) monotone monotone"
unfolding monotone_def[abs_def] by transfer_prover

lemma fun_ord_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total C"
  shows "((A ===> B ===> (=)) ===> (C ===> A) ===> (C ===> B) ===> (=)) fun_ord fun_ord"
unfolding fun_ord_def[abs_def] by transfer_prover

lemma fun_lub_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"  "bi_unique A"
  shows "((rel_set A ===> B) ===> rel_set (C ===> A) ===> C ===> B) fun_lub fun_lub"
unfolding fun_lub_def[abs_def] by transfer_prover

end

end
