(* EXTRACT from HOL/ex/Primes.thy*)

theory Primes = Main:
consts
  gcd     :: "nat*nat \<Rightarrow> nat"               (*Euclid's algorithm *)

recdef gcd "measure ((\<lambda>(m,n).n) ::nat*nat \<Rightarrow> nat)"
    "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))"


ML "Pretty.setmargin 64"
ML "IsarOutput.indent := 5"  (*that is, Doc/TutorialI/settings.ML*)


text {*
\begin{quote}
@{thm[display]"dvd_def"}
\rulename{dvd_def}
\end{quote}
*};


(*** Euclid's Algorithm ***)

lemma gcd_0 [simp]: "gcd(m,0) = m"
  apply (simp);
  done

lemma gcd_non_0 [simp]: "0<n \<Longrightarrow> gcd(m,n) = gcd (n, m mod n)"
  apply (simp)
  done;

declare gcd.simps [simp del];

(*gcd(m,n) divides m and n.  The conjunctions don't seem provable separately*)
lemma gcd_dvd_both: "(gcd(m,n) dvd m) \<and> (gcd(m,n) dvd n)"
  apply (induct_tac m n rule: gcd.induct)
  apply (case_tac "n=0")
  apply (simp_all)
  apply (blast dest: dvd_mod_imp_dvd)
  done


text {*
@{thm[display] dvd_mod_imp_dvd}
\rulename{dvd_mod_imp_dvd}

@{thm[display] dvd_trans}
\rulename{dvd_trans}

\begin{isabelle}
proof\ (prove):\ step\ 3\isanewline
\isanewline
goal\ (lemma\ gcd_dvd_both):\isanewline
gcd\ (m,\ n)\ dvd\ m\ \isasymand \ gcd\ (m,\ n)\ dvd\ n\isanewline
\ 1.\ \isasymAnd m\ n.\ \isasymlbrakk 0\ <\ n;\ gcd\ (n,\ m\ mod\ n)\ dvd\ n\ \isasymand \ gcd\ (n,\ m\ mod\ n)\ dvd\ (m\ mod\ n)\isasymrbrakk \isanewline
\ \ \ \ \ \ \ \ \ \ \isasymLongrightarrow \ gcd\ (n,\ m\ mod\ n)\ dvd\ m
\end{isabelle}
*};


lemmas gcd_dvd1 [iff] = gcd_dvd_both [THEN conjunct1]
lemmas gcd_dvd2 [iff] = gcd_dvd_both [THEN conjunct2];


text {*
\begin{quote}
@{thm[display] gcd_dvd1}
\rulename{gcd_dvd1}

@{thm[display] gcd_dvd2}
\rulename{gcd_dvd2}
\end{quote}
*};

(*Maximality: for all m,n,k naturals, 
                if k divides m and k divides n then k divides gcd(m,n)*)
lemma gcd_greatest [rule_format]:
      "(k dvd m) \<longrightarrow> (k dvd n) \<longrightarrow> k dvd gcd(m,n)"
  apply (induct_tac m n rule: gcd.induct)
  apply (case_tac "n=0")
  apply (simp_all add: dvd_mod);
  done;

theorem gcd_greatest_iff [iff]: 
        "k dvd gcd(m,n) = (k dvd m \<and> k dvd n)"
  apply (blast intro!: gcd_greatest intro: dvd_trans);
  done;


constdefs
  is_gcd  :: "[nat,nat,nat] \<Rightarrow> bool"        (*gcd as a relation*)
    "is_gcd p m n == p dvd m  \<and>  p dvd n  \<and>
                     (ALL d. d dvd m \<and> d dvd n \<longrightarrow> d dvd p)"

(*Function gcd yields the Greatest Common Divisor*)
lemma is_gcd: "is_gcd (gcd(m,n)) m n"
  apply (simp add: is_gcd_def gcd_greatest);
  done

(*uniqueness of GCDs*)
lemma is_gcd_unique: "\<lbrakk> is_gcd m a b; is_gcd n a b \<rbrakk> \<Longrightarrow> m=n"
  apply (simp add: is_gcd_def);
  apply (blast intro: dvd_anti_sym)
  done


text {*
@{thm[display] dvd_anti_sym}
\rulename{dvd_anti_sym}

\begin{isabelle}
proof\ (prove):\ step\ 1\isanewline
\isanewline
goal\ (lemma\ is_gcd_unique):\isanewline
\isasymlbrakk is_gcd\ m\ a\ b;\ is_gcd\ n\ a\ b\isasymrbrakk \ \isasymLongrightarrow \ m\ =\ n\isanewline
\ 1.\ \isasymlbrakk m\ dvd\ a\ \isasymand \ m\ dvd\ b\ \isasymand \ (\isasymforall d.\ d\ dvd\ a\ \isasymand \ d\ dvd\ b\ \isasymlongrightarrow \ d\ dvd\ m);\isanewline
\ \ \ \ \ \ \ n\ dvd\ a\ \isasymand \ n\ dvd\ b\ \isasymand \ (\isasymforall d.\ d\ dvd\ a\ \isasymand \ d\ dvd\ b\ \isasymlongrightarrow \ d\ dvd\ n)\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ m\ =\ n
\end{isabelle}
*};

lemma gcd_assoc: "gcd(gcd(k,m),n) = gcd(k,gcd(m,n))"
  apply (rule is_gcd_unique)
  apply (rule is_gcd)
  apply (simp add: is_gcd_def);
  apply (blast intro: dvd_trans);
  done 

text{*
\begin{isabelle}
proof\ (prove):\ step\ 3\isanewline
\isanewline
goal\ (lemma\ gcd_assoc):\isanewline
gcd\ (gcd\ (k,\ m),\ n)\ =\ gcd\ (k,\ gcd\ (m,\ n))\isanewline
\ 1.\ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ k\ \isasymand \isanewline
\ \ \ \ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ m\ \isasymand \ gcd\ (k,\ gcd\ (m,\ n))\ dvd\ n
\end{isabelle}
*}


lemma gcd_dvd_gcd_mult: "gcd(m,n) dvd gcd(k*m, n)"
  apply (blast intro: dvd_trans);
  done

(*This is half of the proof (by dvd_anti_sym) of*)
lemma gcd_mult_cancel: "gcd(k,n) = 1 \<Longrightarrow> gcd(k*m, n) = gcd(m,n)"
  oops



text{*\noindent
Forward proof material: of, OF, THEN, simplify.
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

lemma gcd_1 [simp]: "gcd(m,1) = 1"
  apply (simp)
  done

lemma gcd_1_left [simp]: "gcd(1,m) = 1"
  apply (simp add: gcd_commute [of 1])
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
  apply (simp)
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
  apply (rule gcd_mult_distrib2 [of k 1, simplified, THEN sym])
  done

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
  apply (rule gcd_mult [of k 1, simplified])
  done

lemma relprime_dvd_mult: 
      "\<lbrakk> gcd(k,n)=1; k dvd (m*n) \<rbrakk> \<Longrightarrow> k dvd m";
  apply (insert gcd_mult_distrib2 [of m k n])
  apply (simp)
  apply (erule_tac t="m" in ssubst);
  apply (simp)
  done


text {*
Another example of "insert"

@{thm[display] mod_div_equality}
\rulename{mod_div_equality}
*};

lemma div_mult_self_is_m: 
      "0<n \<Longrightarrow> (m*n) div n = (m::nat)"
  apply (insert mod_div_equality [of "m*n" n])
  apply (simp)
  done

lemma relprime_dvd_mult_iff: "gcd(k,n)=1 \<Longrightarrow> k dvd (m*n) = k dvd m";
  apply (blast intro: relprime_dvd_mult dvd_trans)
  done

lemma relprime_20_81: "gcd(#20,#81) = 1";
  apply (simp add: gcd.simps)
  done


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

lemma "\<lbrakk>(z::int) < #37; #66 < #2*z; z*z \<noteq> #1225; Q(#34); Q(#36)\<rbrakk> \<Longrightarrow> Q(z)";
apply (subgoal_tac "z = #34 \<or> z = #36")
apply blast
apply (subgoal_tac "z \<noteq> #35")
apply arith
apply force
done

text
{*
proof\ (prove):\ step\ 1\isanewline
\isanewline
goal\ (lemma):\isanewline
\isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36\isasymrbrakk \ \isasymLongrightarrow \ Q\ z\isanewline
\ 1.\ \isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36;\isanewline
\ \ \ \ \ \ \ z\ =\ \#34\ \isasymor \ z\ =\ \#36\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ Q\ z\isanewline
\ 2.\ \isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ z\ =\ \#34\ \isasymor \ z\ =\ \#36



proof\ (prove):\ step\ 3\isanewline
\isanewline
goal\ (lemma):\isanewline
\isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36\isasymrbrakk \ \isasymLongrightarrow \ Q\ z\isanewline
\ 1.\ \isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36;\isanewline
\ \ \ \ \ \ \ z\ \isasymnoteq \ \#35\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ z\ =\ \#34\ \isasymor \ z\ =\ \#36\isanewline
\ 2.\ \isasymlbrakk z\ <\ \#37;\ \#66\ <\ \#2\ *\ z;\ z\ *\ z\ \isasymnoteq \ \#1225;\ Q\ \#34;\ Q\ \#36\isasymrbrakk \isanewline
\ \ \ \ \isasymLongrightarrow \ z\ \isasymnoteq \ \#35
*}


end
