theory Forward = Primes:

text{*\noindent
Forward proof material: of, OF, THEN, simplify, rule_format.
*}

text{*\noindent
SKIP most developments...
*}

(** Commutativity **)

lemma is_gcd_commute: "is_gcd k m n = is_gcd k n m"
apply (auto simp add: is_gcd_def);
done

lemma gcd_commute: "gcd(m,n) = gcd(n,m)"
apply (rule is_gcd_unique)
apply (rule is_gcd)
apply (subst is_gcd_commute)
apply (simp add: is_gcd)
done

lemma gcd_1 [simp]: "gcd(m, Suc 0) = Suc 0"
apply simp
done

lemma gcd_1_left [simp]: "gcd(Suc 0, m) = Suc 0"
apply (simp add: gcd_commute [of "Suc 0"])
done

text{*\noindent
as far as HERE.
*}


text {*
@{thm[display] gcd_1}
\rulename{gcd_1}

@{thm[display] gcd_1_left}
\rulename{gcd_1_left}
*};

text{*\noindent
SKIP THIS PROOF
*}

lemma gcd_mult_distrib2: "k * gcd(m,n) = gcd(k*m, k*n)"
apply (induct_tac m n rule: gcd.induct)
apply (case_tac "n=0")
apply simp
apply (case_tac "k=0")
apply (simp_all add: mod_geq gcd_non_0 mod_mult_distrib2)
done

text {*
@{thm[display] gcd_mult_distrib2}
\rulename{gcd_mult_distrib2}
*};

text{*\noindent
of, simplified
*}


lemmas gcd_mult_0 = gcd_mult_distrib2 [of k 1];
lemmas gcd_mult_1 = gcd_mult_0 [simplified];

text {*
@{thm[display] gcd_mult_distrib2 [of _ 1]}

@{thm[display] gcd_mult_0}
\rulename{gcd_mult_0}

@{thm[display] gcd_mult_1}
\rulename{gcd_mult_1}

@{thm[display] sym}
\rulename{sym}
*};

lemmas gcd_mult = gcd_mult_1 [THEN sym];

lemmas gcd_mult = gcd_mult_distrib2 [of k 1, simplified, THEN sym];
      (*better in one step!*)

text {*
more legible
*};

lemma gcd_mult [simp]: "gcd(k, k*n) = k"
by (rule gcd_mult_distrib2 [of k 1, simplified, THEN sym])


lemmas gcd_self = gcd_mult [of k 1, simplified];


text {*
Rules handy with THEN

@{thm[display] iffD1}
\rulename{iffD1}

@{thm[display] iffD2}
\rulename{iffD2}
*};


text {*
again: more legible
*};

lemma gcd_self [simp]: "gcd(k,k) = k"
by (rule gcd_mult [of k 1, simplified])


text{*
NEXT SECTION: Methods for Forward Proof

NEW

theorem arg_cong, useful in forward steps
@{thm[display] arg_cong[no_vars]}
\rulename{arg_cong}
*}

lemma "2 \<le> u \<Longrightarrow> u*m \<noteq> Suc(u*n)"
apply intro
txt{*
before using arg_cong
@{subgoals[display,indent=0,margin=65]}
*};
apply (drule_tac f="\<lambda>x. x mod u" in arg_cong)
txt{*
after using arg_cong
@{subgoals[display,indent=0,margin=65]}
*};
apply (simp add: mod_Suc)
done

text{*
have just used this rule:
@{thm[display] mod_Suc[no_vars]}
\rulename{mod_Suc}

@{thm[display] mult_le_mono1[no_vars]}
\rulename{mult_le_mono1}
*}


text{*
example of "insert"
*}

lemma relprime_dvd_mult: 
      "\<lbrakk> gcd(k,n)=1; k dvd m*n \<rbrakk> \<Longrightarrow> k dvd m"
apply (insert gcd_mult_distrib2 [of m k n])
apply simp
apply (erule_tac t="m" in ssubst);
apply simp
done


text {*
Another example of "insert"

@{thm[display] mod_div_equality}
\rulename{mod_div_equality}
*};

(*MOVED to Force.thy, which now depends only on Divides.thy
lemma div_mult_self_is_m: "0<n \<Longrightarrow> (m*n) div n = (m::nat)"
*)

lemma relprime_dvd_mult_iff: "gcd(k,n)=1 \<Longrightarrow> (k dvd m*n) = (k dvd m)";
by (blast intro: relprime_dvd_mult dvd_trans)


lemma relprime_20_81: "gcd(20,81) = 1";
by (simp add: gcd.simps)

text {*
Examples of 'OF'

@{thm[display] relprime_dvd_mult}
\rulename{relprime_dvd_mult}

@{thm[display] relprime_dvd_mult [OF relprime_20_81]}

@{thm[display] dvd_refl}
\rulename{dvd_refl}

@{thm[display] dvd_add}
\rulename{dvd_add}

@{thm[display] dvd_add [OF dvd_refl dvd_refl]}

@{thm[display] dvd_add [OF _ dvd_refl]}
*};

lemma "\<lbrakk>(z::int) < 37; 66 < 2*z; z*z \<noteq> 1225; Q(34); Q(36)\<rbrakk> \<Longrightarrow> Q(z)";
apply (subgoal_tac "z = 34 \<or> z = 36")
txt{*
the tactic leaves two subgoals:
@{subgoals[display,indent=0,margin=65]}
*};
apply blast
apply (subgoal_tac "z \<noteq> 35")
txt{*
the tactic leaves two subgoals:
@{subgoals[display,indent=0,margin=65]}
*};
apply arith
apply force
done


end
