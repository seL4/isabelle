(*  Title:      HOL/Extraction/Pigeonhole.thy
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
*)

header {* The pigeonhole principle *}

theory Pigeonhole imports EfficientNat begin

text {*
We formalize two proofs of the pigeonhole principle, which lead
to extracted programs of quite different complexity. The original
formalization of these proofs in {\sc Nuprl} is due to
Aleksey Nogin \cite{Nogin-ENTCS-2000}.

We need decidability of equality on natural numbers:
*}

lemma nat_eq_dec: "\<And>n::nat. m = n \<or> m \<noteq> n"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] n)
  apply (simp only: nat.simps, iprover?)+
  done

text {*
We can decide whether an array @{term "f"} of length @{term "l"}
contains an element @{term "x"}.
*}

lemma search: "(\<exists>j<(l::nat). (x::nat) = f j) \<or> \<not> (\<exists>j<l. x = f j)"
proof (induct l)
  case 0
  have "\<not> (\<exists>j<0. x = f j)"
  proof
    assume "\<exists>j<0. x = f j"
    then obtain j where j: "j < (0::nat)" by iprover
    thus "False" by simp
  qed
  thus ?case ..
next
  case (Suc l)
  thus ?case
  proof
    assume "\<exists>j<l. x = f j"
    then obtain j where j: "j < l"
      and eq: "x = f j" by iprover
    from j have "j < Suc l" by simp
    with eq show ?case by iprover
  next
    assume nex: "\<not> (\<exists>j<l. x = f j)"
    from nat_eq_dec show ?case
    proof
      assume eq: "x = f l"
      have "l < Suc l" by simp
      with eq show ?case by iprover
    next
      assume neq: "x \<noteq> f l"
      have "\<not> (\<exists>j<Suc l. x = f j)"
      proof
	assume "\<exists>j<Suc l. x = f j"
	then obtain j where j: "j < Suc l"
	  and eq: "x = f j" by iprover
	show False
	proof cases
	  assume "j = l"
	  with eq have "x = f l" by simp
	  with neq show False ..
	next
	  assume "j \<noteq> l"
	  with j have "j < l" by simp
	  with nex and eq show False by iprover
	qed
      qed
      thus ?case ..
    qed
  qed
qed

text {*
This proof yields a polynomial program.
*}

theorem pigeonhole:
  "\<And>f. (\<And>i. i \<le> Suc n \<Longrightarrow> f i \<le> n) \<Longrightarrow> \<exists>i j. i \<le> Suc n \<and> j < i \<and> f i = f j"
proof (induct n)
  case 0
  hence "Suc 0 \<le> Suc 0 \<and> 0 < Suc 0 \<and> f (Suc 0) = f 0" by simp
  thus ?case by iprover
next
  case (Suc n)
  {
    fix k
    have
      "k \<le> Suc (Suc n) \<Longrightarrow>
      (\<And>i j. Suc k \<le> i \<Longrightarrow> i \<le> Suc (Suc n) \<Longrightarrow> j < i \<Longrightarrow> f i \<noteq> f j) \<Longrightarrow>
      (\<exists>i j. i \<le> k \<and> j < i \<and> f i = f j)"
    proof (induct k)
      case 0
      let ?f = "\<lambda>i. if f i = Suc n then f (Suc (Suc n)) else f i"
      have "\<not> (\<exists>i j. i \<le> Suc n \<and> j < i \<and> ?f i = ?f j)"
      proof
	assume "\<exists>i j. i \<le> Suc n \<and> j < i \<and> ?f i = ?f j"
      	then obtain i j where i: "i \<le> Suc n" and j: "j < i"
	  and f: "?f i = ?f j" by iprover
      	from j have i_nz: "Suc 0 \<le> i" by simp
      	from i have iSSn: "i \<le> Suc (Suc n)" by simp
      	have S0SSn: "Suc 0 \<le> Suc (Suc n)" by simp
      	show False
      	proof cases
	  assume fi: "f i = Suc n"
	  show False
	  proof cases
	    assume fj: "f j = Suc n"
	    from i_nz and iSSn and j have "f i \<noteq> f j" by (rule 0)
	    moreover from fi have "f i = f j"
	      by (simp add: fj [symmetric])
	    ultimately show ?thesis ..
	  next
	    from i and j have "j < Suc (Suc n)" by simp
	    with S0SSn and le_refl have "f (Suc (Suc n)) \<noteq> f j"
	      by (rule 0)
	    moreover assume "f j \<noteq> Suc n"
	    with fi and f have "f (Suc (Suc n)) = f j" by simp
	    ultimately show False ..
	  qed
      	next
	  assume fi: "f i \<noteq> Suc n"
	  show False
	  proof cases
	    from i have "i < Suc (Suc n)" by simp
	    with S0SSn and le_refl have "f (Suc (Suc n)) \<noteq> f i"
	      by (rule 0)
	    moreover assume "f j = Suc n"
	    with fi and f have "f (Suc (Suc n)) = f i" by simp
	    ultimately show False ..
	  next
	    from i_nz and iSSn and j
	    have "f i \<noteq> f j" by (rule 0)
	    moreover assume "f j \<noteq> Suc n"
	    with fi and f have "f i = f j" by simp
	    ultimately show False ..
	  qed
      	qed
      qed
      moreover have "\<And>i. i \<le> Suc n \<Longrightarrow> ?f i \<le> n"
      proof -
	fix i assume "i \<le> Suc n"
	hence i: "i < Suc (Suc n)" by simp
	have "f (Suc (Suc n)) \<noteq> f i"
	  by (rule 0) (simp_all add: i)
	moreover have "f (Suc (Suc n)) \<le> Suc n"
	  by (rule Suc) simp
	moreover from i have "i \<le> Suc (Suc n)" by simp
	hence "f i \<le> Suc n" by (rule Suc)
	ultimately show "?thesis i"
	  by simp
      qed
      hence "\<exists>i j. i \<le> Suc n \<and> j < i \<and> ?f i = ?f j"
      	by (rule Suc)
      ultimately show ?case ..
    next
      case (Suc k)
      from search show ?case
      proof
	assume "\<exists>j<Suc k. f (Suc k) = f j"
	thus ?case by (iprover intro: le_refl)
      next
	assume nex: "\<not> (\<exists>j<Suc k. f (Suc k) = f j)"
	have "\<exists>i j. i \<le> k \<and> j < i \<and> f i = f j"
	proof (rule Suc)
	  from Suc show "k \<le> Suc (Suc n)" by simp
	  fix i j assume k: "Suc k \<le> i" and i: "i \<le> Suc (Suc n)"
	    and j: "j < i"
	  show "f i \<noteq> f j"
	  proof cases
	    assume eq: "i = Suc k"
	    show ?thesis
	    proof
	      assume "f i = f j"
	      hence "f (Suc k) = f j" by (simp add: eq)
	      with nex and j and eq show False by iprover
	    qed
	  next
	    assume "i \<noteq> Suc k"
	    with k have "Suc (Suc k) \<le> i" by simp
	    thus ?thesis using i and j by (rule Suc)
	  qed
	qed
	thus ?thesis by (iprover intro: le_SucI)
      qed
    qed
  }
  note r = this
  show ?case by (rule r) simp_all
qed

text {*
The following proof, although quite elegant from a mathematical point of view,
leads to an exponential program:
*}

theorem pigeonhole_slow:
  "\<And>f. (\<And>i. i \<le> Suc n \<Longrightarrow> f i \<le> n) \<Longrightarrow> \<exists>i j. i \<le> Suc n \<and> j < i \<and> f i = f j"
proof (induct n)
  case 0
  have "Suc 0 \<le> Suc 0" ..
  moreover have "0 < Suc 0" ..
  moreover from 0 have "f (Suc 0) = f 0" by simp
  ultimately show ?case by iprover
next
  case (Suc n)
  from search show ?case
  proof
    assume "\<exists>j < Suc (Suc n). f (Suc (Suc n)) = f j"
    thus ?case by (iprover intro: le_refl)
  next
    assume "\<not> (\<exists>j < Suc (Suc n). f (Suc (Suc n)) = f j)"
    hence nex: "\<forall>j < Suc (Suc n). f (Suc (Suc n)) \<noteq> f j" by iprover
    let ?f = "\<lambda>i. if f i = Suc n then f (Suc (Suc n)) else f i"
    have "\<And>i. i \<le> Suc n \<Longrightarrow> ?f i \<le> n"
    proof -
      fix i assume i: "i \<le> Suc n"
      show "?thesis i"
      proof (cases "f i = Suc n")
	case True
	from i and nex have "f (Suc (Suc n)) \<noteq> f i" by simp
	with True have "f (Suc (Suc n)) \<noteq> Suc n" by simp
	moreover from Suc have "f (Suc (Suc n)) \<le> Suc n" by simp
	ultimately have "f (Suc (Suc n)) \<le> n" by simp
	with True show ?thesis by simp
      next
	case False
	from Suc and i have "f i \<le> Suc n" by simp
	with False show ?thesis by simp
      qed
    qed
    hence "\<exists>i j. i \<le> Suc n \<and> j < i \<and> ?f i = ?f j" by (rule Suc)
    then obtain i j where i: "i \<le> Suc n" and ji: "j < i" and f: "?f i = ?f j"
      by iprover
    have "f i = f j"
    proof (cases "f i = Suc n")
      case True
      show ?thesis
      proof (cases "f j = Suc n")
	assume "f j = Suc n"
	with True show ?thesis by simp
      next
	assume "f j \<noteq> Suc n"
	moreover from i ji nex have "f (Suc (Suc n)) \<noteq> f j" by simp
	ultimately show ?thesis using True f by simp
      qed
    next
      case False
      show ?thesis
      proof (cases "f j = Suc n")
	assume "f j = Suc n"
	moreover from i nex have "f (Suc (Suc n)) \<noteq> f i" by simp
	ultimately show ?thesis using False f by simp
      next
	assume "f j \<noteq> Suc n"
	with False f show ?thesis by simp
      qed
    qed
    moreover from i have "i \<le> Suc (Suc n)" by simp
    ultimately show ?thesis using ji by iprover
  qed
qed

extract pigeonhole pigeonhole_slow

text {*
The programs extracted from the above proofs look as follows:
@{thm [display] pigeonhole_def}
@{thm [display] pigeonhole_slow_def}
The program for searching for an element in an array is
@{thm [display,eta_contract=false] search_def}
The correctness statement for @{term "pigeonhole"} is
@{thm [display] pigeonhole_correctness [no_vars]}

In order to analyze the speed of the above programs,
we generate ML code from them.
*}

consts_code
  arbitrary :: "nat \<times> nat" ("{* (0::nat, 0::nat) *}")

code_module PH
contains
  test = "\<lambda>n. pigeonhole n (\<lambda>m. m - 1)"
  test' = "\<lambda>n. pigeonhole_slow n (\<lambda>m. m - 1)"
  sel = "op !"

ML "timeit (fn () => PH.test 10)"
ML "timeit (fn () => PH.test' 10)"
ML "timeit (fn () => PH.test 20)"
ML "timeit (fn () => PH.test' 20)"
ML "timeit (fn () => PH.test 25)"
ML "timeit (fn () => PH.test' 25)"
ML "timeit (fn () => PH.test 500)"

ML "PH.pigeonhole 8 (PH.sel [0,1,2,3,4,5,6,3,7,8])"

end
