(*  Title:      HOL/Library/Field_as_Ring.thy
    Author:     Manuel Eberl
*)

theory Field_as_Ring
imports 
  Complex_Main
  "~~/src/HOL/Number_Theory/Euclidean_Algorithm"
begin

context field
begin

subclass idom_divide ..

definition normalize_field :: "'a \<Rightarrow> 'a" 
  where [simp]: "normalize_field x = (if x = 0 then 0 else 1)"
definition unit_factor_field :: "'a \<Rightarrow> 'a" 
  where [simp]: "unit_factor_field x = x"
definition euclidean_size_field :: "'a \<Rightarrow> nat" 
  where [simp]: "euclidean_size_field x = (if x = 0 then 0 else 1)"
definition mod_field :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where [simp]: "mod_field x y = (if y = 0 then x else 0)"

end

instantiation real :: euclidean_ring
begin

definition [simp]: "normalize_real = (normalize_field :: real \<Rightarrow> _)"
definition [simp]: "unit_factor_real = (unit_factor_field :: real \<Rightarrow> _)"
definition [simp]: "euclidean_size_real = (euclidean_size_field :: real \<Rightarrow> _)"
definition [simp]: "modulo_real = (mod_field :: real \<Rightarrow> _)"

instance by standard (simp_all add: dvd_field_iff divide_simps)
end

instantiation real :: euclidean_ring_gcd
begin

definition gcd_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  "gcd_real = gcd_eucl"
definition lcm_real :: "real \<Rightarrow> real \<Rightarrow> real" where
  "lcm_real = lcm_eucl"
definition Gcd_real :: "real set \<Rightarrow> real" where
 "Gcd_real = Gcd_eucl"
definition Lcm_real :: "real set \<Rightarrow> real" where
 "Lcm_real = Lcm_eucl"

instance by standard (simp_all add: gcd_real_def lcm_real_def Gcd_real_def Lcm_real_def)

end

instantiation rat :: euclidean_ring
begin

definition [simp]: "normalize_rat = (normalize_field :: rat \<Rightarrow> _)"
definition [simp]: "unit_factor_rat = (unit_factor_field :: rat \<Rightarrow> _)"
definition [simp]: "euclidean_size_rat = (euclidean_size_field :: rat \<Rightarrow> _)"
definition [simp]: "modulo_rat = (mod_field :: rat \<Rightarrow> _)"

instance by standard (simp_all add: dvd_field_iff divide_simps)
end

instantiation rat :: euclidean_ring_gcd
begin

definition gcd_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "gcd_rat = gcd_eucl"
definition lcm_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "lcm_rat = lcm_eucl"
definition Gcd_rat :: "rat set \<Rightarrow> rat" where
 "Gcd_rat = Gcd_eucl"
definition Lcm_rat :: "rat set \<Rightarrow> rat" where
 "Lcm_rat = Lcm_eucl"

instance by standard (simp_all add: gcd_rat_def lcm_rat_def Gcd_rat_def Lcm_rat_def)

end

instantiation complex :: euclidean_ring
begin

definition [simp]: "normalize_complex = (normalize_field :: complex \<Rightarrow> _)"
definition [simp]: "unit_factor_complex = (unit_factor_field :: complex \<Rightarrow> _)"
definition [simp]: "euclidean_size_complex = (euclidean_size_field :: complex \<Rightarrow> _)"
definition [simp]: "modulo_complex = (mod_field :: complex \<Rightarrow> _)"

instance by standard (simp_all add: dvd_field_iff divide_simps)
end

instantiation complex :: euclidean_ring_gcd
begin

definition gcd_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "gcd_complex = gcd_eucl"
definition lcm_complex :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "lcm_complex = lcm_eucl"
definition Gcd_complex :: "complex set \<Rightarrow> complex" where
 "Gcd_complex = Gcd_eucl"
definition Lcm_complex :: "complex set \<Rightarrow> complex" where
 "Lcm_complex = Lcm_eucl"

instance by standard (simp_all add: gcd_complex_def lcm_complex_def Gcd_complex_def Lcm_complex_def)

end

end
