theory Isar = Sets:

section{*A Taste of Structured Proofs in Isar*}

lemma [intro?]: "mono f \<Longrightarrow> x \<in> f (lfp f) \<Longrightarrow> x \<in> lfp f"
  by(simp only: lfp_unfold [symmetric])

lemma "lfp(\<lambda>T. A \<union> M\<inverse> `` T) = {s. \<exists>t. (s,t) \<in> M\<^sup>* \<and> t \<in> A}"
      (is "lfp ?F = ?toA")
proof
  show "lfp ?F \<subseteq> ?toA"
  by (blast intro!: lfp_lowerbound intro:rtrancl_trans)

  show "?toA \<subseteq> lfp ?F"
  proof
    fix s assume "s \<in> ?toA"
    then obtain t where stM: "(s,t) \<in> M\<^sup>*" and tA: "t \<in> A"
         by blast
    from stM show "s \<in> lfp ?F"
    proof (rule converse_rtrancl_induct)
      from tA have "t \<in> ?F (lfp ?F)" by blast
      with mono_ef show "t \<in> lfp ?F" ..
      fix s s' assume "(s,s') \<in> M" and "(s',t) \<in> M\<^sup>*"
                  and "s' \<in> lfp ?F"
      then have "s \<in> ?F (lfp ?F)" by blast
      with mono_ef show "s \<in> lfp ?F" ..
    qed
  qed
qed

end

