(*  Title:      HOL/Nitpick_Examples/Special_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick's "specialize" optimization.
*)

header {* Examples Featuring Nitpick's \textit{specialize} Optimization *}

theory Special_Nits
imports Main
begin

nitpick_params [verbose, card = 4, sat_solver = MiniSat_JNI, max_threads = 1,
                timeout = 240]

fun f1 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"f1 a b c d e = a + b + c + d + e"

lemma "f1 0 0 0 0 0 = f1 0 0 0 0 (1 - 1)"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "f1 u v w x y = f1 y x w v u"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

fun f2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"f2 a b c d (Suc e) = a + b + c + d + e"

lemma "f2 0 0 0 0 0 = f2 (1 - 1) 0 0 0 0"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "f2 0 (v - v) 0 (x - x) 0 = f2 (u - u) 0 (w - w) 0 (y - y)"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "f2 1 0 0 0 0 = f2 0 1 0 0 0"
nitpick [expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

lemma "f2 0 0 0 0 0 = f2 0 0 0 0 0"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

fun f3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"f3 (Suc a) b 0 d (Suc e) = a + b + d + e" |
"f3 0 b 0 d 0 = b + d"

lemma "f3 a b c d e = f3 e d c b a"
nitpick [expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

lemma "f3 a b c d a = f3 a d c d a"
nitpick [expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

lemma "\<lbrakk>c < 1; a \<ge> e; e \<ge> a\<rbrakk> \<Longrightarrow> f3 a b c d a = f3 e d c b e"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "(\<forall>u. a = u \<longrightarrow> f3 a a a a a = f3 u u u u u)
       \<and> (\<forall>u. b = u \<longrightarrow> f3 b b u b b = f3 u u b u u)"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

function f4 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"f4 x x = 1" |
"f4 y z = (if y = z then 1 else 0)"
by auto
termination by lexicographic_order

lemma "f4 a b = f4 b a"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "f4 a (Suc a) = f4 a a"
nitpick [expect = genuine]
nitpick [dont_specialize, expect = genuine]
oops

fun f5 :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"f5 f (Suc a) = f a"

lemma "\<exists>one \<in> {1}. \<exists>two \<in> {2}.
       f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) (Suc x) = x"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "\<exists>two \<in> {2}. \<exists>one \<in> {1}.
       f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) (Suc x) = x"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "\<exists>one \<in> {1}. \<exists>two \<in> {2}.
       f5 (\<lambda>a. if a = one then 2 else if a = two then 1 else a) (Suc x) = x"
nitpick [expect = genuine]
oops

lemma "\<exists>two \<in> {2}. \<exists>one \<in> {1}.
       f5 (\<lambda>a. if a = one then 2 else if a = two then 1 else a) (Suc x) = x"
nitpick [expect = genuine]
oops

lemma "\<forall>a. g a = a
       \<Longrightarrow> \<exists>one \<in> {1}. \<exists>two \<in> {2}. f5 g x =
                      f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) x"
nitpick [expect = none]
nitpick [dont_specialize, expect = none]
sorry

lemma "\<forall>a. g a = a
       \<Longrightarrow> \<exists>one \<in> {2}. \<exists>two \<in> {1}. f5 g x =
                      f5 (\<lambda>a. if a = one then 1 else if a = two then 2 else a) x"
nitpick [expect = potential]
nitpick [dont_specialize, expect = potential]
sorry

lemma "\<forall>a. g a = a
       \<Longrightarrow> \<exists>b\<^isub>1 b\<^isub>2 b\<^isub>3 b\<^isub>4 b\<^isub>5 b\<^isub>6 b\<^isub>7 b\<^isub>8 b\<^isub>9 b\<^isub>10 (b\<^isub>11\<Colon>nat).
           b\<^isub>1 < b\<^isub>11 \<and> f5 g x = f5 (\<lambda>a. if b\<^isub>1 < b\<^isub>11 then a else h b\<^isub>2) x"
nitpick [expect = potential]
nitpick [dont_specialize, expect = none]
nitpick [dont_box, expect = none]
nitpick [dont_box, dont_specialize, expect = none]
sorry

lemma "\<forall>a. g a = a
       \<Longrightarrow> \<exists>b\<^isub>1 b\<^isub>2 b\<^isub>3 b\<^isub>4 b\<^isub>5 b\<^isub>6 b\<^isub>7 b\<^isub>8 b\<^isub>9 b\<^isub>10 (b\<^isub>11\<Colon>nat).
           b\<^isub>1 < b\<^isub>11
           \<and> f5 g x = f5 (\<lambda>a. if b\<^isub>1 < b\<^isub>11 then
                                a
                              else
                                h b\<^isub>2 + h b\<^isub>3 + h b\<^isub>4 + h b\<^isub>5 + h b\<^isub>6 + h b\<^isub>7 + h b\<^isub>8
                                + h b\<^isub>9 + h b\<^isub>10) x"
nitpick [card nat = 2, card 'a = 1, expect = none]
nitpick [card nat = 2, card 'a = 1, dont_box, expect = none]
nitpick [card nat = 2, card 'a = 1, dont_specialize, expect = none]
nitpick [card nat = 2, card 'a = 1, dont_box, dont_specialize, expect = none]
sorry

lemma "\<forall>a. g a = a
       \<Longrightarrow> \<exists>b\<^isub>1 b\<^isub>2 b\<^isub>3 b\<^isub>4 b\<^isub>5 b\<^isub>6 b\<^isub>7 b\<^isub>8 b\<^isub>9 b\<^isub>10 (b\<^isub>11\<Colon>nat).
           b\<^isub>1 < b\<^isub>11
           \<and> f5 g x = f5 (\<lambda>a. if b\<^isub>1 \<ge> b\<^isub>11 then
                                a
                              else
                                h b\<^isub>2 + h b\<^isub>3 + h b\<^isub>4 + h b\<^isub>5 + h b\<^isub>6 + h b\<^isub>7 + h b\<^isub>8
                                + h b\<^isub>9 + h b\<^isub>10) x"
nitpick [card nat = 2, card 'a = 1, expect = potential]
nitpick [card nat = 2, card 'a = 1, dont_box, expect = potential]
nitpick [card nat = 2, card 'a = 1, dont_specialize, expect = potential]
nitpick [card nat = 2, card 'a = 1, dont_box, dont_specialize,
         expect = potential]
oops

end
