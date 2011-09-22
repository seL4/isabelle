theory Complex_Types
imports SPARK
begin

datatype day = Mon | Tue | Wed | Thu | Fri | Sat | Sun

record two_fields =
  Field1 :: "int \<times> day \<Rightarrow> int"
  Field2 :: int

spark_types
  complex_types__day = day
  complex_types__record_type = two_fields

definition
  initialized3 :: "(int \<times> day \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "initialized3 A i k = (\<forall>j\<in>{0..<k}. A (i, val j) = 0)"

definition
  initialized2 :: "(int \<times> day \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> bool" where
  "initialized2 A i = (\<forall>j\<in>{0..<i}. initialized3 A j 7)"

definition
  initialized :: "(int \<Rightarrow> two_fields) \<Rightarrow> int \<Rightarrow> bool" where
  "initialized A i = (\<forall>j\<in>{0..<i}.
     initialized2 (Field1 (A j)) 10 \<and> Field2 (A j) = 0)"

spark_proof_functions
  complex_types__initialized = initialized
  complex_types__initialized2 = initialized2
  complex_types__initialized3 = initialized3

(*<*)
spark_open "complex_types_app/initialize.siv"

spark_vc procedure_initialize_1
  by (simp add: initialized_def)

spark_vc procedure_initialize_2
proof -
  from
    `initialized a loop__1__i`
    `initialized2 (Field1 (a loop__1__i)) 9`
    `initialized3 (Field1 (a loop__1__i)) 9 (pos Sun)`
  show ?C1
    apply (auto simp add: initialized_def initialized2_def initialized3_def)
    apply (case_tac "j = 9")
    apply auto
    apply (case_tac "ja = 6")
    apply auto
    done
  from H5
  show ?C2 by simp
qed

spark_vc procedure_initialize_3
  by (simp add: initialized2_def)

spark_vc procedure_initialize_4
proof -
  from `initialized a loop__1__i`
  show ?C1 by (simp add: initialized_def)
  from
    `initialized2 (Field1 (a loop__1__i)) loop__2__j`
    `initialized3 (Field1 (a loop__1__i)) loop__2__j (pos Sun)`
  show ?C2
    apply (auto simp add: initialized2_def initialized3_def)
    apply (case_tac "j = loop__2__j")
    apply auto
    apply (case_tac "ja = 6")
    apply auto
    done
  from H5
  show ?C3 by simp
qed

spark_vc procedure_initialize_5
  by (simp add: initialized3_def)

spark_vc procedure_initialize_6
proof -
  from `initialized a loop__1__i`
  show ?C1 by (simp add: initialized_def)
  from `initialized2 (Field1 (a loop__1__i)) loop__2__j`
  show ?C2 by (simp add: initialized2_def initialized3_def)
  from
    `initialized3 (Field1 (a loop__1__i)) loop__2__j (pos loop__3__k)`
    `loop__3__k < Sun`
    rangeI [of pos loop__3__k]
  show ?C3
    apply (auto simp add: initialized3_def succ_def less_pos pos_val range_pos)
    apply (case_tac "j = pos loop__3__k")
    apply (auto simp add: val_pos)
    done
  from H5
  show ?C4 by simp
qed

spark_vc procedure_initialize_9
  using
    `initialized a 9`
    `initialized2 (Field1 (a 9)) 9`
    `initialized3 (Field1 (a 9)) 9 (pos Sun)`
  apply (auto simp add: initialized_def initialized2_def initialized3_def)
  apply (case_tac "j = 9")
  apply auto
  apply (case_tac "ja = 6")
  apply auto
  done

spark_end
(*>*)

end
