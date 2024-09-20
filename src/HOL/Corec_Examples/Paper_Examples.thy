(*  Title:      HOL/Corec_Examples/Paper_Examples.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2016

Small examples from the paper "Friends with Benefits".
*)

section \<open>Small Examples from the Paper ``Friends with Benefits''\<close>

theory Paper_Examples
imports "HOL-Library.BNF_Corec" "HOL-Library.FSet" Complex_Main
begin

section \<open>Examples from the introduction\<close>

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream") (infixr \<open>\<lhd>\<close> 65)

corec "natsFrom" :: "nat \<Rightarrow> nat stream" where
  "natsFrom n = n \<lhd> natsFrom (n + 1)"

corec (friend) add1 :: "nat stream \<Rightarrow> nat stream"
where "add1 ns = (shd ns + 1) \<lhd> add1 (stl ns)"

corec natsFrom' :: "nat \<Rightarrow> nat stream" where
  "natsFrom' n = n \<lhd> add1 (natsFrom' n)"

section \<open>Examples from section 3\<close>

text \<open>We curry the example functions in this section because infix syntax works only for curried functions.\<close>

corec (friend) Plus :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix \<open>\<oplus>\<close> 67) where
  "x\<^sub>1 \<oplus> x\<^sub>2 = (shd x\<^sub>1 + shd x\<^sub>2) \<lhd> (stl x\<^sub>1 \<oplus> stl x\<^sub>2)"

section \<open>Examples from section 4\<close>

codatatype 'a llist = LNil | LCons 'a "'a llist"

corec collatz :: "nat \<Rightarrow> nat llist" where
  "collatz n = (if n \<le> 1 then LNil
     else if even n then collatz (n div 2)
     else LCons n (collatz (3 * n + 1)))"

datatype 'a nelist = NEList (hd:'a) (tl:"'a list")

primrec (transfer) snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a nelist" (infix \<open>\<rhd>\<close> 64) where
 "[] \<rhd> a = NEList a []"
|"(b # bs) \<rhd> a = NEList b (bs @ [a])"

corec (friend) inter :: "nat stream nelist \<Rightarrow> nat stream" where
"inter xss = shd (hd xss) \<lhd> inter (tl xss \<rhd> stl (hd xss))"

corec (friend) inter' :: "nat stream nelist \<Rightarrow> nat stream" where
"inter' xss = (case hd xss of x \<lhd> xs \<Rightarrow> x \<lhd> inter' (tl xss \<rhd> xs))"

corec zero :: "nat stream" where "zero = 0 \<lhd> zero"

section \<open>Examples from Blanchette et al. (ICFP 2015)\<close>

corec oneTwos :: "nat stream" where "oneTwos = 1 \<lhd> 2 \<lhd> oneTwos"

corec everyOther :: "'a stream \<Rightarrow> 'a stream"
where "everyOther xs = shd xs \<lhd> everyOther (stl (stl xs))"

corec fibA :: "nat stream"
where "fibA = 0 \<lhd> (1 \<lhd> fibA \<oplus> fibA)"

corec fibB :: "nat stream"
where "fibB = (0 \<lhd> 1 \<lhd> fibB) \<oplus> (0 \<lhd> fibB)"

corec (friend) times :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix \<open>\<otimes>\<close> 69)
where "xs \<otimes> ys = (shd xs * shd ys) \<lhd> xs \<otimes> stl ys \<oplus> stl xs \<otimes> ys"

corec (friend) exp :: "nat stream \<Rightarrow> nat stream"
where "exp xs = 2 ^ shd xs \<lhd> (stl xs \<otimes> exp xs)"

corec facA :: "nat stream"
where "facA = (1 \<lhd> facA) \<otimes> (1 \<lhd> facA)"

corec facB :: "nat stream"
where "facB = exp (0 \<lhd> facB)"

corec (friend) sfsup :: "nat stream fset \<Rightarrow> nat stream"
where "sfsup X = Sup (fset (fimage shd X)) \<lhd> sfsup (fimage stl X)"

codatatype tree = Node (val: nat) (sub: "tree list")

corec (friend) tplus :: "tree \<Rightarrow> tree \<Rightarrow> tree"
where "tplus t u = Node (val t + val u) (map (\<lambda>(t', u'). tplus t' u') (zip (sub t) (sub u)))"

corec (friend) ttimes :: "tree \<Rightarrow> tree \<Rightarrow> tree"
where "ttimes t u = Node (val t * val u)
  (map (\<lambda>(t, u). tplus (ttimes t u) (ttimes t u)) (zip (sub t) (sub u)))"

corecursive primes :: "nat \<Rightarrow> nat \<Rightarrow> nat stream"
where "primes m n =
  (if (m = 0 \<and> n > 1) \<or> coprime m n then n \<lhd> primes (m * n) (n + 1) else primes m (n + 1))"
apply (relation "measure (\<lambda>(m, n). if n = 0 then 1 else if coprime m n then 0 else m - n mod m)")
   apply (auto simp: mod_Suc diff_less_mono2 intro: Suc_lessI elim!: not_coprimeE)
   apply (metis dvd_1_iff_1 dvd_eq_mod_eq_0 mod_0 mod_Suc mod_Suc_eq mod_mod_cancel)
  done

corec facC :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat stream"
where "facC n a i = (if i = 0 then a \<lhd> facC (n + 1) 1 (n + 1) else facC n (a * i) (i - 1))"

corec catalan :: "nat \<Rightarrow> nat stream"
where "catalan n = (if n > 0 then catalan (n - 1) \<oplus> (0 \<lhd> catalan (n + 1)) else 1 \<lhd> catalan 1)"

corec (friend) heart :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infix \<open>\<heartsuit>\<close> 65)
where "xs \<heartsuit> ys = SCons (shd xs * shd ys) ((((xs \<heartsuit> stl ys) \<oplus> (stl xs \<otimes> ys)) \<heartsuit> ys) \<otimes> ys)"

corec (friend) g :: "'a stream \<Rightarrow> 'a stream"
where "g xs = shd xs \<lhd> g (g (stl xs))"

end
