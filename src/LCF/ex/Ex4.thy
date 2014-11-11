
section {* Prefixpoints *}

theory Ex4
imports "../LCF"
begin

lemma example:
  assumes asms: "f(p) << p"  "\<And>q. f(q) << q \<Longrightarrow> p << q"
  shows "FIX(f)=p"
  apply (unfold eq_def)
  apply (rule conjI)
  apply (induct f)
  apply (rule minimal)
  apply (intro strip)
  apply (rule less_trans)
  prefer 2
  apply (rule asms)
  apply (erule less_ap_term)
  apply (rule asms)
  apply (rule FIX_eq [THEN eq_imp_less1])
  done

end
