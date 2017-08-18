(*  Title:      HOL/Corec_Examples/Tests/Stream_Friends.thy
    Author:     Aymeric Bouzy, Ecole polytechnique
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2015, 2016

Friendly functions on streams.
*)

section \<open>Friendly Functions on Streams\<close>

theory Stream_Friends
imports "HOL-Library.BNF_Corec"
begin

codatatype 'a stream = SCons (shd: 'a) (stl: "'a stream")

corec pls :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" where
  "pls s s' = SCons (shd s + shd s') (pls (stl s) (stl s'))"

friend_of_corec pls :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" where
  "pls s s' = SCons (shd s + shd s') (pls (stl s) (stl s'))"
  sorry

corec onetwo :: "nat stream" where
  "onetwo = SCons 1 (SCons 2 onetwo)"

corec prd :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" where
  "prd xs ys = SCons (shd xs * shd ys) (pls (prd xs (stl ys)) (prd (stl xs) ys))"

friend_of_corec prd  where
  "prd xs ys = SCons (shd xs * shd ys) (pls (prd xs (stl ys)) (prd (stl xs) ys))"
  sorry

corec Exp :: "nat stream \<Rightarrow> nat stream" where
  "Exp xs = SCons (2 ^^ shd xs) (prd (stl xs) (Exp xs))"

friend_of_corec Exp where
  "Exp xs = SCons (2 ^^ shd xs) (prd (stl xs) (Exp xs))"
  sorry

corec prd2 :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" where
  "prd2 xs ys = SCons (shd xs * shd ys) (pls (prd xs (stl ys)) (prd2 (stl xs) ys))"

fun sthe_default :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a stream option \<Rightarrow> 'a stream" where
  "sthe_default s _ None = s"
| "sthe_default _ _ (Some t) = t"

(* FIXME:
friend_of_corec sthe_default where
  "sthe_default s n opt = SCons (shd (case opt of None \<Rightarrow> s | Some t \<Rightarrow> t)) (stl (case opt of None \<Rightarrow> s | Some t \<Rightarrow> t))"
  sorry

corec funky0 :: "nat \<Rightarrow> nat stream" where
  "funky0 n = SCons 0 (sthe_default undefined n (map_option funky0 undefined))"

consts funky0' :: "nat stream \<Rightarrow> nat stream"

friend_of_corec funky0' :: "nat stream \<Rightarrow> nat stream" where
  "funky0' ns = SCons 0 (sthe_default undefined (shd ns) (map_option funky0' undefined))"
  sorry

corec funky :: "nat \<Rightarrow> nat stream" where
  "funky n = SCons 0 (sthe_default (funky (n + 1)) n (map_option funky (Some (n + 2))))"

corec funky' :: "nat \<Rightarrow> nat \<Rightarrow> nat stream" where
  "funky' m n = SCons 0 (sthe_default (funky' (m - 1) (n + 1)) m (map_option (%(x, y). funky' (Suc x) (Suc y)) (Some (m - 2, n + 2))))"

corec funky'' :: "nat \<Rightarrow> nat stream" where
  "funky'' n = SCons 0 (sthe_default (funky'' (n + 1)) n (Some (funky'' (n + 2))))" 

corec phunky0 :: "nat \<Rightarrow> nat stream" where
  "phunky0 n = sthe_default undefined n undefined"

fun lthe_default :: "'a stream \<Rightarrow> 'a stream option \<Rightarrow> 'a stream" where
  "lthe_default s None = s"
| "lthe_default _ (Some t) = t"

friend_of_corec lthe_default where
  "lthe_default s opt = SCons (shd (case opt of None \<Rightarrow> s | Some t \<Rightarrow> t)) (stl (case opt of None \<Rightarrow> s | Some t \<Rightarrow> t))"
  sorry

corec phunky_debug :: "'a \<Rightarrow> 'a stream" where
  "phunky_debug n = lthe_default (SCons n (lthe_default undefined (map_option phunky_debug undefined))) undefined"

corec phunky1 :: "nat \<Rightarrow> nat stream" where
  "phunky1 n = sthe_default (SCons 0 (sthe_default (phunky1 (n + 1)) n (map_option phunky1 (Some (n + 2))))) n undefined"

corec phunky2 :: "nat \<Rightarrow> nat stream" where
  "phunky2 n = sthe_default (SCons 0 (sthe_default (phunky2 (n + 1)) n (map_option phunky2 (Some (n + 2))))) n
     (map_option (%m. SCons m (sthe_default (phunky2 (n + 1)) n (map_option phunky2 (Some (n + 2))))) (Some n))"

corec phunky3 :: "nat \<Rightarrow> nat stream" where
  "phunky3 n = sthe_default (SCons 0 (sthe_default (phunky3 (n + 1)) n (map_option phunky3 (Some (n + 3))))) n
     (Some (SCons n (sthe_default (phunky3 (n + 1)) n (map_option phunky3 (Some (n + 3))))))"
*)

end
