(*  Title:      HOL/TPTP/THF_Arith.thy
    Author:     Jasmin Blanchette
    Copyright   2011, 2012

Experimental setup for THF arithmetic. This is not connected with the TPTP
parser yet.
*)

theory THF_Arith
imports Complex_Main
begin

consts
  is_int :: "'a \<Rightarrow> bool"
  is_rat :: "'a \<Rightarrow> bool"

overloading rat_is_int \<equiv> "is_int :: rat \<Rightarrow> bool"
begin
  definition "rat_is_int (q\<Colon>rat) \<longleftrightarrow> (\<exists>n\<Colon>int. q = of_int n)"
end

overloading real_is_int \<equiv> "is_int :: real \<Rightarrow> bool"
begin
  definition "real_is_int (x\<Colon>real) \<longleftrightarrow> x \<in> \<int>"
end

overloading real_is_rat \<equiv> "is_rat :: real \<Rightarrow> bool"
begin
  definition "real_is_rat (x\<Colon>real) \<longleftrightarrow> x \<in> \<rat>"
end

consts
  to_int :: "'a \<Rightarrow> int"
  to_rat :: "'a \<Rightarrow> rat"
  to_real :: "'a \<Rightarrow> real"

overloading rat_to_int \<equiv> "to_int :: rat \<Rightarrow> int"
begin
  definition "rat_to_int (q\<Colon>rat) = floor q"
end

overloading real_to_int \<equiv> "to_int :: real \<Rightarrow> int"
begin
  definition "real_to_int (x\<Colon>real) = floor x"
end

overloading int_to_rat \<equiv> "to_rat :: int \<Rightarrow> rat"
begin
  definition "int_to_rat (n\<Colon>int) = (of_int n\<Colon>rat)"
end

overloading real_to_rat \<equiv> "to_rat :: real \<Rightarrow> rat"
begin
  definition "real_to_rat (x\<Colon>real) = (inv real x\<Colon>rat)"
end

overloading int_to_real \<equiv> "to_real :: int \<Rightarrow> real"
begin
  definition "int_to_real (n\<Colon>int) = real n"
end

overloading rat_to_real \<equiv> "to_real :: rat \<Rightarrow> real"
begin
  definition "rat_to_real (x\<Colon>rat) = (of_rat x\<Colon>real)"
end

declare
  rat_is_int_def [simp]
  real_is_int_def [simp]
  real_is_rat_def [simp]
  rat_to_int_def [simp]
  real_to_int_def [simp]
  int_to_rat_def [simp]
  real_to_rat_def [simp]
  int_to_real_def [simp]
  rat_to_real_def [simp]

lemma to_rat_is_int [intro, simp]: "is_int (to_rat (n\<Colon>int))"
by (metis int_to_rat_def rat_is_int_def)

lemma to_real_is_int [intro, simp]: "is_int (to_real (n\<Colon>int))"
by (metis Ints_real_of_int int_to_real_def real_is_int_def)

lemma to_real_is_rat [intro, simp]: "is_rat (to_real (q\<Colon>rat))"
by (metis Rats_of_rat rat_to_real_def real_is_rat_def)

lemma inj_of_rat [intro, simp]: "inj (of_rat\<Colon>rat\<Rightarrow>real)"
by (metis injI of_rat_eq_iff rat_to_real_def)

end
