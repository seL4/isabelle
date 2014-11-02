(*  Title:      HOL/Datatype_Examples/Misc_N2M.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2014

Miscellaneous tests for the nested-to-mutual reduction.
*)

section \<open>Miscellaneous Tests for the Nested-to-Mutual Reduction\<close>

theory Misc_N2M
imports "~~/src/HOL/Library/BNF_Axiomatization"
begin

locale misc
begin

datatype 'a li = Ni | Co 'a "'a li"
datatype 'a tr = Tr "'a \<Rightarrow> 'a tr li"

primrec (nonexhaustive)
  f_tl :: "'a \<Rightarrow> 'a tr li \<Rightarrow> nat" and
  f_t :: "'a \<Rightarrow> 'a tr \<Rightarrow> nat"
where
  "f_tl _ Ni = 0" |
  "f_t a (Tr ts) = 1 + f_tl a (ts a)"

datatype ('a, 'b) l = N | C 'a 'b "('a, 'b) l"
datatype ('a, 'b) t = T "(('a, 'b) t, 'a) l" "(('a, 'b) t, 'b) l"

primrec (nonexhaustive)
  f_tl2 :: "(('a, 'a) t, 'a) l \<Rightarrow> nat" and
  f_t2 :: "('a, 'a) t \<Rightarrow> nat"
where
  "f_tl2 N = 0" |
  "f_t2 (T ts us) = f_tl2 ts + f_tl2 us"

primrec  (nonexhaustive)
  g_tla :: "(('a, 'b) t, 'a) l \<Rightarrow> nat" and
  g_tlb :: "(('a, 'b) t, 'b) l \<Rightarrow> nat" and
  g_t :: "('a, 'b) t \<Rightarrow> nat"
where
  "g_tla N = 0" |
  "g_tlb N = 1" |
  "g_t (T ts us) = g_tla ts + g_tlb us"


datatype
  'a l1 = N1 | C1 'a "'a l1"

datatype
  ('a, 'b) t1 = T1 'a 'b "('a, 'b) t1 l1" "(nat \<times> ('a, 'b) t1) l1" and
  ('a, 'b) t2 = T2 "('a, 'b) t1"

primrec
  h1_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  h1_natl1 :: "(nat \<times> (nat, 'a) t1) l1 \<Rightarrow> nat" and
  h1_t1 :: "(nat, 'a) t1 \<Rightarrow> nat"
where
  "h1_tl1 N1 = 0" |
  "h1_tl1 (C1 t ts) = h1_t1 t + h1_tl1 ts" |
  "h1_natl1 N1 = Suc 0" |
  "h1_natl1 (C1 n ts) = fst n + h1_natl1 ts" |
  "h1_t1 (T1 n _ ts _) = n + h1_tl1 ts"

end


bnf_axiomatization ('a, 'b) M0 [wits: "('a, 'b) M0"]
bnf_axiomatization ('a, 'b) N0 [wits: "('a, 'b) N0"]
bnf_axiomatization ('a, 'b) K0 [wits: "('a, 'b) K0"]
bnf_axiomatization ('a, 'b) L0 [wits: "('a, 'b) L0"]
bnf_axiomatization ('a, 'b, 'c) G0 [wits: "('a, 'b, 'c) G0"]

locale (*co*)mplicated
begin

datatype 'a M = CM "('a, 'a M) M0"
datatype 'a N = CN "('a N, 'a) N0"
datatype ('a, 'b) K = CK "('a, ('a, 'b) L) K0"
         and ('a, 'b) L = CL "('b, ('a, 'b) K) L0"
datatype 'a G = CG "('a, ('a G, 'a G N) K, ('a G M, 'a G) L) G0"

primrec
    fG :: "'a G \<Rightarrow> 'a G"
and fK :: "('a G, 'a G N) K \<Rightarrow> ('a G, 'a G N) K"
and fL :: "('a G, 'a G N) L \<Rightarrow> ('a G, 'a G N) L"
and fM :: "'a G M \<Rightarrow> 'a G M" where
  "fG (CG x) = CG (map_G0 id fK (map_L fM fG) x)"
| "fK (CK y) = CK (map_K0 fG fL y)"
| "fL (CL z) = CL (map_L0 (map_N fG) fK z)"
| "fM (CM w) = CM (map_M0 fG fM w)"
thm fG_def fK_def fL_def fM_def fG.simps fK.simps fL.simps fM.simps

end

locale complicated
begin

codatatype 'a M = CM "('a, 'a M) M0"
codatatype 'a N = CN "('a N, 'a) N0"
codatatype ('a, 'b) K = CK "('a, ('a, 'b) L) K0"
         and ('a, 'b) L = CL "('b, ('a, 'b) K) L0"
codatatype 'a G = CG "('a, ('a G, 'a G N) K, ('a G M, 'a G) L) G0"

primcorec
    fG :: "'a G \<Rightarrow> 'a G"
and fK :: "('a G, 'a G N) K \<Rightarrow> ('a G, 'a G N) K"
and fL :: "('a G, 'a G N) L \<Rightarrow> ('a G, 'a G N) L"
and fM :: "'a G M \<Rightarrow> 'a G M" where
  "fG x = CG (map_G0 id fK (map_L fM fG) (un_CG x))"
| "fK y = CK (map_K0 fG fL (un_CK y))"
| "fL z = CL (map_L0 (map_N fG) fK (un_CL z))"
| "fM w = CM (map_M0 fG fM (un_CM w))"
thm fG_def fK_def fL_def fM_def fG.simps fK.simps fL.simps fM.simps

end

datatype ('a, 'b) F1 = F1 'a 'b
datatype F2 = F2 "((unit, nat) F1, F2) F1" | F2'
datatype 'a kk1 = K1 'a | K2 "'a kk2" and 'a kk2 = K3 "'a kk1"
datatype 'a ll1 = L1 'a | L2 "'a ll2 kk2" and 'a ll2 = L3 "'a ll1"

datatype_compat F1
datatype_compat F2
datatype_compat kk1 kk2
datatype_compat ll1 ll2


subsection \<open>Deep Nesting\<close>

datatype 'a tree = Empty | Node 'a "'a tree list"
datatype_compat tree

datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"
datatype_compat ttree

datatype 'a tttree = TEmpty | TNode 'a "'a tttree list ttree list tree"
datatype_compat tttree
(*
datatype 'a ttttree = TEmpty | TNode 'a "'a ttttree list tttree list ttree list tree"
datatype_compat ttttree
*)

datatype ('a,'b)complex = 
  C1 nat "'a ttree" 
| C2 "('a,'b)complex list tree tree" 'b "('a,'b)complex" "('a,'b)complex2 ttree list"
and ('a,'b)complex2 = D1 "('a,'b)complex ttree"
datatype_compat complex complex2

datatype 'a F = F1 'a | F2 "'a F"
datatype 'a G = G1 'a | G2 "'a G F"
datatype H = H1 | H2 "H G"

datatype_compat F
datatype_compat G
datatype_compat H


subsection \<open>Primrec cache\<close>

datatype 'a l = N | C 'a "'a l"
datatype ('a, 'b) t = T 'a 'b "('a, 'b) t l"

context linorder
begin

(* slow *)
primrec
  f1_tl :: "(nat, 'a) t l \<Rightarrow> nat" and
  f1_t :: "(nat, 'a) t \<Rightarrow> nat"
where
  "f1_tl N = 0" |
  "f1_tl (C t ts) = f1_t t + f1_tl ts" |
  "f1_t (T n _ ts) = n + f1_tl ts"

(* should be fast *)
primrec
  f2_t :: "(nat, 'b) t \<Rightarrow> nat" and
  f2_tl :: "(nat, 'b) t l \<Rightarrow> nat"
where
  "f2_tl N = 0" |
  "f2_tl (C t ts) = f2_t t + f2_tl ts" |
  "f2_t (T n _ ts) = n + f2_tl ts"

end

(* should be fast *)
primrec
  g1_t :: "('a, int) t \<Rightarrow> nat" and
  g1_tl :: "('a, int) t l \<Rightarrow> nat"
where
  "g1_t (T _ _ ts) = g1_tl ts" |
  "g1_tl N = 0" |
  "g1_tl (C _ ts) = g1_tl ts"

(* should be fast *)
primrec
  g2_t :: "(int, int) t \<Rightarrow> nat" and
  g2_tl :: "(int, int) t l \<Rightarrow> nat"
where
  "g2_t (T _ _ ts) = g2_tl ts" |
  "g2_tl N = 0" |
  "g2_tl (C _ ts) = g2_tl ts"


datatype
  'a l1 = N1 | C1 'a "'a l2" and
  'a l2 = N2 | C2 'a "'a l1"

primrec
  sum_l1 :: "'a::{zero,plus} l1 \<Rightarrow> 'a" and
  sum_l2 :: "'a::{zero,plus} l2 \<Rightarrow> 'a"
where
  "sum_l1 N1 = 0" |
  "sum_l1 (C1 n ns) = n + sum_l2 ns" |
  "sum_l2 N2 = 0" |
  "sum_l2 (C2 n ns) = n + sum_l1 ns"

datatype
  ('a, 'b) t1 = T1 'a 'b "('a, 'b) t1 l1" and
  ('a, 'b) t2 = T2 "('a, 'b) t1"

(* slow *)
primrec
  h1_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  h1_tl2 :: "(nat, 'a) t1 l2 \<Rightarrow> nat" and
  h1_t1 :: "(nat, 'a) t1 \<Rightarrow> nat"
where
  "h1_tl1 N1 = 0" |
  "h1_tl1 (C1 t ts) = h1_t1 t + h1_tl2 ts" |
  "h1_tl2 N2 = 0" |
  "h1_tl2 (C2 t ts) = h1_t1 t + h1_tl1 ts" |
  "h1_t1 (T1 n _ ts) = n + h1_tl1 ts"

(* should be fast *)
primrec
  h2_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  h2_tl2 :: "(nat, 'a) t1 l2 \<Rightarrow> nat" and
  h2_t1 :: "(nat, 'a) t1 \<Rightarrow> nat"
where
  "h2_tl1 N1 = 0" |
  "h2_tl1 (C1 t ts) = h2_t1 t + h2_tl2 ts" |
  "h2_tl2 N2 = 0" |
  "h2_tl2 (C2 t ts) = h2_t1 t + h2_tl1 ts" |
  "h2_t1 (T1 n _ ts) = n + h2_tl1 ts"

(* should be fast *)
primrec
  h3_tl2 :: "(nat, 'a) t1 l2 \<Rightarrow> nat" and
  h3_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  h3_t1 :: "(nat, 'a) t1 \<Rightarrow> nat"
where
  "h3_tl1 N1 = 0" |
  "h3_tl1 (C1 t ts) = h3_t1 t + h3_tl2 ts" |
  "h3_tl2 N2 = 0" |
  "h3_tl2 (C2 t ts) = h3_t1 t + h3_tl1 ts" |
  "h3_t1 (T1 n _ ts) = n + h3_tl1 ts"

(* should be fast *)
primrec
  i1_tl2 :: "(nat, 'a) t1 l2 \<Rightarrow> nat" and
  i1_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  i1_t1 :: "(nat, 'a) t1 \<Rightarrow> nat" and
  i1_t2 :: "(nat, 'a) t2 \<Rightarrow> nat"
where
  "i1_tl1 N1 = 0" |
  "i1_tl1 (C1 t ts) = i1_t1 t + i1_tl2 ts" |
  "i1_tl2 N2 = 0" |
  "i1_tl2 (C2 t ts) = i1_t1 t + i1_tl1 ts" |
  "i1_t1 (T1 n _ ts) = n + i1_tl1 ts" |
  "i1_t2 (T2 t) = i1_t1 t"

(* should be fast *)
primrec
  j1_t2 :: "(nat, 'a) t2 \<Rightarrow> nat" and
  j1_t1 :: "(nat, 'a) t1 \<Rightarrow> nat" and
  j1_tl1 :: "(nat, 'a) t1 l1 \<Rightarrow> nat" and
  j1_tl2 :: "(nat, 'a) t1 l2 \<Rightarrow> nat"
where
  "j1_tl1 N1 = 0" |
  "j1_tl1 (C1 t ts) = j1_t1 t + j1_tl2 ts" |
  "j1_tl2 N2 = 0" |
  "j1_tl2 (C2 t ts) = j1_t1 t + j1_tl1 ts" |
  "j1_t1 (T1 n _ ts) = n + j1_tl1 ts" |
  "j1_t2 (T2 t) = j1_t1 t"


datatype 'a l3 = N3 | C3 'a "'a l3"
datatype 'a l4 = N4 | C4 'a "'a l4"
datatype ('a, 'b) t3 = T3 'a 'b "('a, 'b) t3 l3" "('a, 'b) t3 l4"

(* slow *)
primrec
  k1_tl3 :: "(nat, 'a) t3 l3 \<Rightarrow> nat" and
  k1_tl4 :: "(nat, 'a) t3 l4 \<Rightarrow> nat" and
  k1_t3 :: "(nat, 'a) t3 \<Rightarrow> nat"
where
  "k1_tl3 N3 = 0" |
  "k1_tl3 (C3 t ts) = k1_t3 t + k1_tl3 ts" |
  "k1_tl4 N4 = 0" |
  "k1_tl4 (C4 t ts) = k1_t3 t + k1_tl4 ts" |
  "k1_t3 (T3 n _ ts us) = n + k1_tl3 ts + k1_tl4 us"

(* should be fast *)
primrec
  k2_tl4 :: "(nat, int) t3 l4 \<Rightarrow> nat" and
  k2_tl3 :: "(nat, int) t3 l3 \<Rightarrow> nat" and
  k2_t3 :: "(nat, int) t3 \<Rightarrow> nat"
where
  "k2_tl4 N4 = 0" |
  "k2_tl4 (C4 t ts) = k2_t3 t + k2_tl4 ts" |
  "k2_tl3 N3 = 0" |
  "k2_tl3 (C3 t ts) = k2_t3 t + k2_tl3 ts" |
  "k2_t3 (T3 n _ ts us) = n + k2_tl3 ts + k2_tl4 us"


datatype ('a, 'b) l5 = N5 | C5 'a 'b "('a, 'b) l5"
datatype ('a, 'b) l6 = N6 | C6 'a 'b "('a, 'b) l6"
datatype ('a, 'b, 'c) t4 = T4 'a 'b "(('a, 'b, 'c) t4, 'b) l5" "(('a, 'b, 'c) t4, 'c) l6"

(* slow *)
primrec
  l1_tl5 :: "((nat, 'a, 'b) t4, 'a) l5 \<Rightarrow> nat" and
  l1_tl6 :: "((nat, 'a, 'b) t4, 'b) l6 \<Rightarrow> nat" and
  l1_t4 :: "(nat, 'a, 'b) t4 \<Rightarrow> nat"
where
  "l1_tl5 N5 = 0" |
  "l1_tl5 (C5 t _ ts) = l1_t4 t + l1_tl5 ts" |
  "l1_tl6 N6 = 0" |
  "l1_tl6 (C6 t _ ts) = l1_t4 t + l1_tl6 ts" |
  "l1_t4 (T4 n _ ts us) = n + l1_tl5 ts + l1_tl6 us"


subsection \<open>Primcorec Cache\<close>

codatatype 'a col = N | C 'a "'a col"
codatatype ('a, 'b) cot = T 'a 'b "('a, 'b) cot col"

context linorder
begin

(* slow *)
primcorec
  f1_cotcol :: "nat \<Rightarrow> (nat, 'a) cot col" and
  f1_cot :: "nat \<Rightarrow> (nat, 'a) cot"
where
  "n = 0 \<Longrightarrow> f1_cotcol n = N" |
  "_ \<Longrightarrow> f1_cotcol n = C (f1_cot n) (f1_cotcol n)" |
  "f1_cot n = T n undefined (f1_cotcol n)"

(* should be fast *)
primcorec
  f2_cotcol :: "nat \<Rightarrow> (nat, 'b) cot col" and
  f2_cot :: "nat \<Rightarrow> (nat, 'b) cot"
where
  "n = 0 \<Longrightarrow> f2_cotcol n = N" |
  "_ \<Longrightarrow> f2_cotcol n = C (f2_cot n) (f2_cotcol n)" |
  "f2_cot n = T n undefined (f2_cotcol n)"

end

(* should be fast *)
primcorec
  g1_cot :: "int \<Rightarrow> (int, 'a) cot" and
  g1_cotcol :: "int \<Rightarrow> (int, 'a) cot col"
where
  "g1_cot n = T n undefined (g1_cotcol n)" |
  "n = 0 \<Longrightarrow> g1_cotcol n = N" |
  "_ \<Longrightarrow> g1_cotcol n = C (g1_cot n) (g1_cotcol n)"

(* should be fast *)
primcorec
  g2_cot :: "int \<Rightarrow> (int, int) cot" and
  g2_cotcol :: "int \<Rightarrow> (int, int) cot col"
where
  "g2_cot n = T n undefined (g2_cotcol n)" |
  "n = 0 \<Longrightarrow> g2_cotcol n = N" |
  "_ \<Longrightarrow> g2_cotcol n = C (g2_cot n) (g2_cotcol n)"


codatatype
  'a col1 = N1 | C1 'a "'a col2" and
  'a col2 = N2 | C2 'a "'a col1"

codatatype
  ('a, 'b) cot1 = T1 'a 'b "('a, 'b) cot1 col1" and
  ('a, 'b) cot2 = T2 "('a, 'b) cot1"

(* slow *)
primcorec
  h1_cotcol1 :: "nat \<Rightarrow> (nat, 'a) cot1 col1" and
  h1_cotcol2 :: "nat \<Rightarrow> (nat, 'a) cot1 col2" and
  h1_cot1 :: "nat \<Rightarrow> (nat, 'a) cot1"
where
  "h1_cotcol1 n = C1 (h1_cot1 n) (h1_cotcol2 n)" |
  "h1_cotcol2 n = C2 (h1_cot1 n) (h1_cotcol1 n)" |
  "h1_cot1 n = T1 n undefined (h1_cotcol1 n)"

(* should be fast *)
primcorec
  h2_cotcol1 :: "nat \<Rightarrow> (nat, 'a) cot1 col1" and
  h2_cotcol2 :: "nat \<Rightarrow> (nat, 'a) cot1 col2" and
  h2_cot1 :: "nat \<Rightarrow> (nat, 'a) cot1"
where
  "h2_cotcol1 n = C1 (h2_cot1 n) (h2_cotcol2 n)" |
  "h2_cotcol2 n = C2 (h2_cot1 n) (h2_cotcol1 n)" |
  "h2_cot1 n = T1 n undefined (h2_cotcol1 n)"

(* should be fast *)
primcorec
  h3_cotcol2 :: "nat \<Rightarrow> (nat, 'a) cot1 col2" and
  h3_cotcol1 :: "nat \<Rightarrow> (nat, 'a) cot1 col1" and
  h3_cot1 :: "nat \<Rightarrow> (nat, 'a) cot1"
where
  "h3_cotcol1 n = C1 (h3_cot1 n) (h3_cotcol2 n)" |
  "h3_cotcol2 n = C2 (h3_cot1 n) (h3_cotcol1 n)" |
  "h3_cot1 n = T1 n undefined (h3_cotcol1 n)"

(* should be fast *)
primcorec
  i1_cotcol2 :: "nat \<Rightarrow> (nat, 'a) cot1 col2" and
  i1_cotcol1 :: "nat \<Rightarrow> (nat, 'a) cot1 col1" and
  i1_cot1 :: "nat \<Rightarrow> (nat, 'a) cot1" and
  i1_cot2 :: "nat \<Rightarrow> (nat, 'a) cot2"
where
  "i1_cotcol1 n = C1 (i1_cot1 n) (i1_cotcol2 n)" |
  "i1_cotcol2 n = C2 (i1_cot1 n) (i1_cotcol1 n)" |
  "i1_cot1 n = T1 n undefined (i1_cotcol1 n)" |
  "i1_cot2 n = T2 (i1_cot1 n)"

(* should be fast *)
primcorec
  j1_cot2 :: "nat \<Rightarrow> (nat, 'a) cot2" and
  j1_cot1 :: "nat \<Rightarrow> (nat, 'a) cot1" and
  j1_cotcol1 :: "nat \<Rightarrow> (nat, 'a) cot1 col1" and
  j1_cotcol2 :: "nat \<Rightarrow> (nat, 'a) cot1 col2"
where
  "j1_cotcol1 n = C1 (j1_cot1 n) (j1_cotcol2 n)" |
  "j1_cotcol2 n = C2 (j1_cot1 n) (j1_cotcol1 n)" |
  "j1_cot1 n = T1 n undefined (j1_cotcol1 n)" |
  "j1_cot2 n = T2 (j1_cot1 n)"


codatatype 'a col3 = N3 | C3 'a "'a col3"
codatatype 'a col4 = N4 | C4 'a "'a col4"
codatatype ('a, 'b) cot3 = T3 'a 'b "('a, 'b) cot3 col3" "('a, 'b) cot3 col4"

(* slow *)
primcorec
  k1_cotcol3 :: "nat \<Rightarrow> (nat, 'a) cot3 col3" and
  k1_cotcol4 :: "nat \<Rightarrow> (nat, 'a) cot3 col4" and
  k1_cot3 :: "nat \<Rightarrow> (nat, 'a) cot3"
where
  "k1_cotcol3 n = C3 (k1_cot3 n) (k1_cotcol3 n)" |
  "k1_cotcol4 n = C4 (k1_cot3 n) (k1_cotcol4 n)" |
  "k1_cot3 n = T3 n undefined (k1_cotcol3 n) (k1_cotcol4 n)"

(* should be fast *)
primcorec
  k2_cotcol4 :: "nat \<Rightarrow> (nat, 'a) cot3 col4" and
  k2_cotcol3 :: "nat \<Rightarrow> (nat, 'a) cot3 col3" and
  k2_cot3 :: "nat \<Rightarrow> (nat, 'a) cot3"
where
  "k2_cotcol4 n = C4 (k2_cot3 n) (k2_cotcol4 n)" |
  "k2_cotcol3 n = C3 (k2_cot3 n) (k2_cotcol3 n)" |
  "k2_cot3 n = T3 n undefined (k2_cotcol3 n) (k2_cotcol4 n)"

end
