(*  Title:      HOL/Library/IArray.thy
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section \<open>Immutable Arrays with Code Generation\<close>

theory IArray
imports Main
begin

subsection \<open>Fundamental operations\<close>

text \<open>Immutable arrays are lists wrapped up in an additional constructor.
There are no update operations. Hence code generation can safely implement
this type by efficient target language arrays.  Currently only SML is
provided. Could be extended to other target languages and more operations.\<close>

context
begin

datatype 'a iarray = IArray "'a list"

qualified primrec list_of :: "'a iarray \<Rightarrow> 'a list" where
"list_of (IArray xs) = xs"

qualified definition of_fun :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a iarray" where
[simp]: "of_fun f n = IArray (map f [0..<n])"

qualified definition sub :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
[simp]: "as !! n = IArray.list_of as ! n"

qualified definition length :: "'a iarray \<Rightarrow> nat" where
[simp]: "length as = List.length (IArray.list_of as)"

qualified definition all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
[simp]: "all p as \<longleftrightarrow> (\<forall>a \<in> set (list_of as). p a)"

qualified definition exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool" where
[simp]: "exists p as \<longleftrightarrow> (\<exists>a \<in> set (list_of as). p a)"

lemma of_fun_nth:
"IArray.of_fun f n !! i = f i" if "i < n"
using that by (simp add: map_nth)

end


subsection \<open>Generic code equations\<close>

lemma [code]:
  "size (as :: 'a iarray) = Suc (IArray.length as)"
  by (cases as) simp

lemma [code]:
  "size_iarray f as = Suc (size_list f (IArray.list_of as))"
  by (cases as) simp

lemma [code]:
  "rec_iarray f as = f (IArray.list_of as)"
  by (cases as) simp

lemma [code]:
  "case_iarray f as = f (IArray.list_of as)"
  by (cases as) simp

lemma [code]:
  "set_iarray as = set (IArray.list_of as)"
  by (cases as) auto

lemma [code]:
  "map_iarray f as = IArray (map f (IArray.list_of as))"
  by (cases as) auto

lemma [code]:
  "rel_iarray r as bs = list_all2 r (IArray.list_of as) (IArray.list_of bs)"
  by (cases as, cases bs) auto

lemma list_of_code [code]:
  "IArray.list_of as = map (\<lambda>n. as !! n) [0 ..< IArray.length as]"
  by (cases as) (simp add: map_nth)

lemma [code]:
  "HOL.equal as bs \<longleftrightarrow> HOL.equal (IArray.list_of as) (IArray.list_of bs)"
  by (cases as, cases bs) (simp add: equal)

lemma [code]:
  "IArray.all p = Not \<circ> IArray.exists (Not \<circ> p)"
  by (simp add: fun_eq_iff)

context
  includes term_syntax
begin

lemma [code]:
  "Code_Evaluation.term_of (as :: 'a::typerep iarray) =
    Code_Evaluation.Const (STR ''IArray.iarray.IArray'') (TYPEREP('a list \<Rightarrow> 'a iarray)) <\<cdot>> (Code_Evaluation.term_of (IArray.list_of as))"
  by (subst term_of_anything) rule

end


subsection \<open>Auxiliary operations for code generation\<close>

context
begin

qualified primrec tabulate :: "integer \<times> (integer \<Rightarrow> 'a) \<Rightarrow> 'a iarray" where
  "tabulate (n, f) = IArray (map (f \<circ> integer_of_nat) [0..<nat_of_integer n])"

lemma [code]:
  "IArray.of_fun f n = IArray.tabulate (integer_of_nat n, f \<circ> nat_of_integer)"
  by simp

qualified primrec sub' :: "'a iarray \<times> integer \<Rightarrow> 'a" where
  "sub' (as, n) = as !! nat_of_integer n"

lemma [code]:
  "IArray.sub' (IArray as, n) = as ! nat_of_integer n"
  by simp

lemma [code]:
  "as !! n = IArray.sub' (as, integer_of_nat n)"
  by simp

qualified definition length' :: "'a iarray \<Rightarrow> integer" where
  [simp]: "length' as = integer_of_nat (List.length (IArray.list_of as))"

lemma [code]:
  "IArray.length' (IArray as) = integer_of_nat (List.length as)"
  by simp

lemma [code]:
  "IArray.length as = nat_of_integer (IArray.length' as)"
  by simp

qualified definition exists_upto :: "('a \<Rightarrow> bool) \<Rightarrow> integer \<Rightarrow> 'a iarray \<Rightarrow> bool" where
  [simp]: "exists_upto p k as \<longleftrightarrow> (\<exists>l. 0 \<le> l \<and> l < k \<and> p (sub' (as, l)))"

lemma exists_upto_of_nat:
  "exists_upto p (of_nat n) as \<longleftrightarrow> (\<exists>m<n. p (as !! m))"
  including integer.lifting by (simp, transfer)
    (metis nat_int nat_less_iff of_nat_0_le_iff)

lemma [code]:
  "exists_upto p k as \<longleftrightarrow> (if k \<le> 0 then False else
    let l = k - 1 in p (sub' (as, l)) \<or> exists_upto p l as)"
proof (cases "k \<ge> 1")
  case False
  then show ?thesis
    by (auto simp add: not_le discrete)
next
  case True
  then have less: "k \<le> 0 \<longleftrightarrow> False"
    by simp
  define n where "n = nat_of_integer (k - 1)"
  with True have k: "k - 1 = of_nat n" "k = of_nat (Suc n)"
    by simp_all
  show ?thesis unfolding less Let_def k(1) unfolding k(2) exists_upto_of_nat
    using less_Suc_eq by auto
qed

lemma [code]:
  "IArray.exists p as \<longleftrightarrow> exists_upto p (length' as) as"
  including integer.lifting by (simp, transfer)
   (auto, metis in_set_conv_nth less_imp_of_nat_less nat_int of_nat_0_le_iff)

end


subsection \<open>Code Generation for SML\<close>

text \<open>Note that arrays cannot be printed directly but only by turning them into
lists first. Arrays could be converted back into lists for printing if they
were wrapped up in an additional constructor.\<close>

code_reserved SML Vector

code_printing
  type_constructor iarray \<rightharpoonup> (SML) "_ Vector.vector"
| constant IArray \<rightharpoonup> (SML) "Vector.fromList"
| constant IArray.all \<rightharpoonup> (SML) "Vector.all"
| constant IArray.exists \<rightharpoonup> (SML) "Vector.exists"
| constant IArray.tabulate \<rightharpoonup> (SML) "Vector.tabulate"
| constant IArray.sub' \<rightharpoonup> (SML) "Vector.sub"
| constant IArray.length' \<rightharpoonup> (SML) "Vector.length"


subsection \<open>Code Generation for Haskell\<close>

text \<open>We map \<^typ>\<open>'a iarray\<close>s in Isabelle/HOL to \<open>Data.Array.IArray.array\<close>
  in Haskell.  Performance mapping to \<open>Data.Array.Unboxed.Array\<close> and
  \<open>Data.Array.Array\<close> is similar.\<close>

code_printing
  code_module "IArray" \<rightharpoonup> (Haskell) \<open>
module IArray(IArray, tabulate, of_list, sub, length) where {

  import Prelude (Bool(True, False), not, Maybe(Nothing, Just),
    Integer, (+), (-), (<), fromInteger, toInteger, map, seq, (.));
  import qualified Prelude;
  import qualified Data.Array.IArray;
  import qualified Data.Array.Base;
  import qualified Data.Ix;

  newtype IArray e = IArray (Data.Array.IArray.Array Integer e);

  tabulate :: (Integer, (Integer -> e)) -> IArray e;
  tabulate (k, f) = IArray (Data.Array.IArray.array (0, k - 1) (map (\i -> let fi = f i in fi `seq` (i, fi)) [0..k - 1]));

  of_list :: [e] -> IArray e;
  of_list l = IArray (Data.Array.IArray.listArray (0, (toInteger . Prelude.length) l - 1) l);

  sub :: (IArray e, Integer) -> e;
  sub (IArray v, i) = v `Data.Array.Base.unsafeAt` fromInteger i;

  length :: IArray e -> Integer;
  length (IArray v) = toInteger (Data.Ix.rangeSize (Data.Array.IArray.bounds v));

}\<close> for type_constructor iarray constant IArray IArray.tabulate IArray.sub' IArray.length'

code_reserved Haskell IArray_Impl

code_printing
  type_constructor iarray \<rightharpoonup> (Haskell) "IArray.IArray _"
| constant IArray \<rightharpoonup> (Haskell) "IArray.of'_list"
| constant IArray.tabulate \<rightharpoonup> (Haskell) "IArray.tabulate"
| constant IArray.sub' \<rightharpoonup> (Haskell)  "IArray.sub"
| constant IArray.length' \<rightharpoonup> (Haskell) "IArray.length"

end
