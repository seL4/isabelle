(*  Title:      HOL/SPARK/Examples/RIPEMD-160/RMD.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory RMD
imports "HOL-Library.Word"
begin


\<comment> \<open>all operations are defined on 32-bit words\<close>

type_synonym word32 = "32 word"
type_synonym byte = "8 word"
type_synonym perm = "nat \<Rightarrow> nat"
type_synonym chain = "word32 * word32 * word32 * word32 * word32"
type_synonym block = "nat \<Rightarrow> word32"
type_synonym message = "nat \<Rightarrow> block"

\<comment> \<open>nonlinear functions at bit level\<close>

definition f::"[nat, word32, word32, word32] => word32"
where
"f j x y z =
      (if ( 0 <= j & j <= 15) then x XOR y XOR z
  else if (16 <= j & j <= 31) then (x AND y) OR (NOT x AND z)
  else if (32 <= j & j <= 47) then (x OR NOT y) XOR z
  else if (48 <= j & j <= 63) then (x AND z) OR (y AND NOT z)
  else if (64 <= j & j <= 79) then x XOR (y OR NOT z)
  else 0)"


\<comment> \<open>added constants (hexadecimal)\<close>

definition K::"nat => word32"
where
"K j =
      (if ( 0 <= j & j <= 15) then 0x00000000
  else if (16 <= j & j <= 31) then 0x5A827999
  else if (32 <= j & j <= 47) then 0x6ED9EBA1
  else if (48 <= j & j <= 63) then 0x8F1BBCDC
  else if (64 <= j & j <= 79) then 0xA953FD4E
  else 0)"

definition K'::"nat => word32"
where
"K' j =
      (if ( 0 <= j & j <= 15) then 0x50A28BE6
  else if (16 <= j & j <= 31) then 0x5C4DD124
  else if (32 <= j & j <= 47) then 0x6D703EF3
  else if (48 <= j & j <= 63) then 0x7A6D76E9
  else if (64 <= j & j <= 79) then 0x00000000
  else 0)"


\<comment> \<open>selection of message word\<close>

definition r_list :: "nat list"
  where "r_list = [
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
  ]"

definition r'_list :: "nat list"
  where "r'_list = [
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
  ]"

definition r :: perm
  where "r j = r_list ! j"

definition r' :: perm
  where "r' j = r'_list ! j"


\<comment> \<open>amount for rotate left (rol)\<close>

definition s_list :: "nat list"
  where "s_list = [
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
  ]"

definition s'_list :: "nat list"
  where "s'_list = [
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
  ]"

definition s :: perm
  where "s j = s_list ! j"

definition s' :: perm
  where "s' j = s'_list ! j"


\<comment> \<open>Initial value (hexadecimal)\<close>

definition h0_0::word32 where "h0_0 = 0x67452301"
definition h1_0::word32 where "h1_0 = 0xEFCDAB89"
definition h2_0::word32 where "h2_0 = 0x98BADCFE"
definition h3_0::word32 where "h3_0 = 0x10325476"
definition h4_0::word32 where "h4_0 = 0xC3D2E1F0"
definition h_0::chain where "h_0 = (h0_0, h1_0, h2_0, h3_0, h4_0)"


definition step_l ::
  "[ block,
     chain,
     nat
  ] => chain"
  where
  "step_l X c j =
    (let (A, B, C, D, E) = c in
    (\<comment> \<open>\<open>A:\<close>\<close> E,
     \<comment> \<open>\<open>B:\<close>\<close> word_rotl (s j) (A + f j B C D + X (r j) + K j) + E,
     \<comment> \<open>\<open>C:\<close>\<close> B,
     \<comment> \<open>\<open>D:\<close>\<close> word_rotl 10 C,
     \<comment> \<open>\<open>E:\<close>\<close> D))"

definition step_r ::
  "[ block,
     chain,
     nat
   ] \<Rightarrow> chain"
where
  "step_r X c' j =
    (let (A', B', C', D', E') = c' in
    (\<comment> \<open>\<open>A':\<close>\<close> E',
     \<comment> \<open>\<open>B':\<close>\<close> word_rotl (s' j) (A' + f (79 - j) B' C' D' + X (r' j) + K' j) + E',
     \<comment> \<open>\<open>C':\<close>\<close> B',
     \<comment> \<open>\<open>D':\<close>\<close> word_rotl 10 C',
     \<comment> \<open>\<open>E':\<close>\<close> D'))"

definition step_both ::
  "[ block, chain * chain, nat ] \<Rightarrow> chain * chain"
  where
  "step_both X cc j = (case cc of (c, c') \<Rightarrow>
  (step_l X c j, step_r X c' j))"

definition steps::"[ block, chain * chain, nat] \<Rightarrow> chain * chain"
  where "steps X cc i = foldl (step_both X) cc [0..<i]"

definition round::"[ block, chain ] \<Rightarrow> chain"
  where "round X h =
    (let (h0, h1, h2, h3, h4) = h in
     let ((A, B, C, D, E), (A', B', C', D', E')) = steps X (h, h) 80 in
      (\<comment> \<open>\<open>h0:\<close>\<close> h1 + C + D',
       \<comment> \<open>\<open>h1:\<close>\<close> h2 + D + E',
       \<comment> \<open>\<open>h2:\<close>\<close> h3 + E + A',
       \<comment> \<open>\<open>h3:\<close>\<close> h4 + A + B',
       \<comment> \<open>\<open>h4:\<close>\<close> h0 + B + C'))"

definition rmd_body::"[ message, chain, nat ] => chain"
where
  "rmd_body X h i = round (X i) h"

definition rounds::"message \<Rightarrow> chain \<Rightarrow> nat \<Rightarrow> chain"
where
  "rounds X h i = foldl (rmd_body X) h_0 [0..<i]"

definition rmd :: "message \<Rightarrow> nat \<Rightarrow> chain"
where
  "rmd X len = rounds X h_0 len"

end
