(*  Title:      HOL/Proofs/Extraction/Higman_Extraction.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Monika Seisenberger, LMU Muenchen
*)

(*<*)
theory Higman_Extraction
imports Higman "~~/src/HOL/Library/State_Monad" Random
begin
(*>*)

subsection {* Extracting the program *}

declare R.induct [ind_realizer]
declare T.induct [ind_realizer]
declare L.induct [ind_realizer]
declare good.induct [ind_realizer]
declare bar.induct [ind_realizer]

extract higman_idx

text {*
  Program extracted from the proof of @{text higman_idx}:
  @{thm [display] higman_idx_def [no_vars]}
  Corresponding correctness theorem:
  @{thm [display] higman_idx_correctness [no_vars]}
  Program extracted from the proof of @{text higman}:
  @{thm [display] higman_def [no_vars]}
  Program extracted from the proof of @{text prop1}:
  @{thm [display] prop1_def [no_vars]}
  Program extracted from the proof of @{text prop2}:
  @{thm [display] prop2_def [no_vars]}
  Program extracted from the proof of @{text prop3}:
  @{thm [display] prop3_def [no_vars]}
*}


subsection {* Some examples *}

instantiation LT and TT :: default
begin

definition "default = L0 [] []"

definition "default = T0 A [] [] [] R0"

instance ..

end

function mk_word_aux :: "nat \<Rightarrow> Random.seed \<Rightarrow> letter list \<times> Random.seed" where
  "mk_word_aux k = exec {
     i \<leftarrow> Random.range 10;
     (if i > 7 \<and> k > 2 \<or> k > 1000 then Pair []
     else exec {
       let l = (if i mod 2 = 0 then A else B);
       ls \<leftarrow> mk_word_aux (Suc k);
       Pair (l # ls)
     })}"
by pat_completeness auto
termination by (relation "measure ((op -) 1001)") auto

definition mk_word :: "Random.seed \<Rightarrow> letter list \<times> Random.seed" where
  "mk_word = mk_word_aux 0"

primrec mk_word_s :: "nat \<Rightarrow> Random.seed \<Rightarrow> letter list \<times> Random.seed" where
  "mk_word_s 0 = mk_word"
  | "mk_word_s (Suc n) = exec {
       _ \<leftarrow> mk_word;
       mk_word_s n
     }"

definition g1 :: "nat \<Rightarrow> letter list" where
  "g1 s = fst (mk_word_s s (20000, 1))"

definition g2 :: "nat \<Rightarrow> letter list" where
  "g2 s = fst (mk_word_s s (50000, 1))"

fun f1 :: "nat \<Rightarrow> letter list" where
  "f1 0 = [A, A]"
  | "f1 (Suc 0) = [B]"
  | "f1 (Suc (Suc 0)) = [A, B]"
  | "f1 _ = []"

fun f2 :: "nat \<Rightarrow> letter list" where
  "f2 0 = [A, A]"
  | "f2 (Suc 0) = [B]"
  | "f2 (Suc (Suc 0)) = [B, A]"
  | "f2 _ = []"

ML {*
local
  val higman_idx = @{code higman_idx};
  val g1 = @{code g1};
  val g2 = @{code g2};
  val f1 = @{code f1};
  val f2 = @{code f2};
in
  val (i1, j1) = higman_idx g1;
  val (v1, w1) = (g1 i1, g1 j1);
  val (i2, j2) = higman_idx g2;
  val (v2, w2) = (g2 i2, g2 j2);
  val (i3, j3) = higman_idx f1;
  val (v3, w3) = (f1 i3, f1 j3);
  val (i4, j4) = higman_idx f2;
  val (v4, w4) = (f2 i4, f2 j4);
end;
*}

end
