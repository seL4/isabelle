(*  Title:      HOL/MicroJava/J/Exceptions.thy
    Author:     Gerwin Klein, Martin Strecker
    Copyright   2002 Technische Universitaet Muenchen
*)

theory Exceptions imports State begin

text \<open>a new, blank object with default values in all fields:\<close>
definition blank :: "'c prog \<Rightarrow> cname \<Rightarrow> obj" where
  "blank G C \<equiv> (C,init_vars (fields(G,C)))" 

definition start_heap :: "'c prog \<Rightarrow> aheap" where
  "start_heap G \<equiv> Map.empty (XcptRef NullPointer \<mapsto> blank G (Xcpt NullPointer))
                        (XcptRef ClassCast \<mapsto> blank G (Xcpt ClassCast))
                        (XcptRef OutOfMemory \<mapsto> blank G (Xcpt OutOfMemory))"


abbreviation
  cname_of :: "aheap \<Rightarrow> val \<Rightarrow> cname"
  where "cname_of hp v == fst (the (hp (the_Addr v)))"


definition preallocated :: "aheap \<Rightarrow> bool" where
  "preallocated hp \<equiv> \<forall>x. \<exists>fs. hp (XcptRef x) = Some (Xcpt x, fs)"

lemma preallocatedD:
  "preallocated hp \<Longrightarrow> \<exists>fs. hp (XcptRef x) = Some (Xcpt x, fs)"
  by (unfold preallocated_def) fast

lemma preallocatedE [elim?]:
  "preallocated hp \<Longrightarrow> (\<And>fs. hp (XcptRef x) = Some (Xcpt x, fs) \<Longrightarrow> P hp) \<Longrightarrow> P hp"
  by (fast dest: preallocatedD)

lemma cname_of_xcp:
  "raise_if b x None = Some xcp \<Longrightarrow> preallocated hp 
  \<Longrightarrow> cname_of (hp::aheap) xcp = Xcpt x"
proof -
  assume "raise_if b x None = Some xcp"
  hence "xcp = Addr (XcptRef x)"
    by (simp add: raise_if_def split: if_split_asm)
  moreover
  assume "preallocated hp" 
  then obtain fs where "hp (XcptRef x) = Some (Xcpt x, fs)" ..
  ultimately
  show ?thesis by simp
qed

lemma preallocated_start:
  "preallocated (start_heap G)"
  apply (unfold preallocated_def)
  apply (unfold start_heap_def)
  apply (rule allI)
  apply (case_tac x)
  apply (auto simp add: blank_def)
  done



end

