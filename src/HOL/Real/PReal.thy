(*  Title       : PReal.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive reals as Dedekind sections of positive
         rationals. Fundamentals of Abstract Analysis [Gleason- p. 121]
                  provides some of the definitions.
*)

theory PReal = Rational:

text{*Could be generalized and moved to @{text Ring_and_Field}*}
lemma add_eq_exists: "\<exists>x. a+x = (b::rat)"
by (rule_tac x="b-a" in exI, simp)

text{*As a special case, the sum of two positives is positive.  One of the
premises could be weakened to the relation @{text "\<le>"}.*}
lemma pos_add_strict: "[|0<a; b<c|] ==> b < a + (c::'a::ordered_semidom)"
by (insert add_strict_mono [of 0 a b c], simp)

lemma interval_empty_iff:
     "({y::'a::ordered_field. x < y & y < z} = {}) = (~(x < z))"
by (blast dest: dense intro: order_less_trans)


constdefs
  cut :: "rat set => bool"
    "cut A == {} \<subset> A &
              A < {r. 0 < r} &
              (\<forall>y \<in> A. ((\<forall>z. 0<z & z < y --> z \<in> A) & (\<exists>u \<in> A. y < u)))"


lemma cut_of_rat: 
  assumes q: "0 < q" shows "cut {r::rat. 0 < r & r < q}"
proof -
  let ?A = "{r::rat. 0 < r & r < q}"
  from q have pos: "?A < {r. 0 < r}" by force
  have nonempty: "{} \<subset> ?A"
  proof
    show "{} \<subseteq> ?A" by simp
    show "{} \<noteq> ?A"
      by (force simp only: q eq_commute [of "{}"] interval_empty_iff)
  qed
  show ?thesis
    by (simp add: cut_def pos nonempty,
        blast dest: dense intro: order_less_trans)
qed


typedef preal = "{A. cut A}"
  by (blast intro: cut_of_rat [OF zero_less_one])

instance preal :: "{ord, plus, minus, times, inverse}" ..

constdefs
  preal_of_rat :: "rat => preal"
     "preal_of_rat q == Abs_preal({x::rat. 0 < x & x < q})"

  psup       :: "preal set => preal"
    "psup(P)   == Abs_preal(\<Union>X \<in> P. Rep_preal(X))"

  add_set :: "[rat set,rat set] => rat set"
    "add_set A B == {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x + y}"

  diff_set :: "[rat set,rat set] => rat set"
    "diff_set A B == {w. \<exists>x. 0 < w & 0 < x & x \<notin> B & x + w \<in> A}"

  mult_set :: "[rat set,rat set] => rat set"
    "mult_set A B == {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x * y}"

  inverse_set :: "rat set => rat set"
    "inverse_set A == {x. \<exists>y. 0 < x & x < y & inverse y \<notin> A}"


defs (overloaded)

  preal_less_def:
    "R < (S::preal) == Rep_preal R < Rep_preal S"

  preal_le_def:
    "R \<le> (S::preal) == Rep_preal R \<subseteq> Rep_preal S"

  preal_add_def:
    "R + S == Abs_preal (add_set (Rep_preal R) (Rep_preal S))"

  preal_diff_def:
    "R - S == Abs_preal (diff_set (Rep_preal R) (Rep_preal S))"

  preal_mult_def:
    "R * S == Abs_preal(mult_set (Rep_preal R) (Rep_preal S))"

  preal_inverse_def:
    "inverse R == Abs_preal(inverse_set (Rep_preal R))"


lemma inj_on_Abs_preal: "inj_on Abs_preal preal"
apply (rule inj_on_inverseI)
apply (erule Abs_preal_inverse)
done

declare inj_on_Abs_preal [THEN inj_on_iff, simp]

lemma inj_Rep_preal: "inj(Rep_preal)"
apply (rule inj_on_inverseI)
apply (rule Rep_preal_inverse)
done

lemma preal_nonempty: "A \<in> preal ==> \<exists>x\<in>A. 0 < x"
by (unfold preal_def cut_def, blast)

lemma preal_imp_psubset_positives: "A \<in> preal ==> A < {r. 0 < r}"
by (force simp add: preal_def cut_def)

lemma preal_exists_bound: "A \<in> preal ==> \<exists>x. 0 < x & x \<notin> A"
by (drule preal_imp_psubset_positives, auto)

lemma preal_exists_greater: "[| A \<in> preal; y \<in> A |] ==> \<exists>u \<in> A. y < u"
by (unfold preal_def cut_def, blast)

lemma mem_Rep_preal_Ex: "\<exists>x. x \<in> Rep_preal X"
apply (insert Rep_preal [of X])
apply (unfold preal_def cut_def, blast)
done

declare Abs_preal_inverse [simp]

lemma preal_downwards_closed: "[| A \<in> preal; y \<in> A; 0 < z; z < y |] ==> z \<in> A"
by (unfold preal_def cut_def, blast)

text{*Relaxing the final premise*}
lemma preal_downwards_closed':
     "[| A \<in> preal; y \<in> A; 0 < z; z \<le> y |] ==> z \<in> A"
apply (simp add: order_le_less)
apply (blast intro: preal_downwards_closed)
done

lemma Rep_preal_exists_bound: "\<exists>x. 0 < x & x \<notin> Rep_preal X"
apply (cut_tac x = X in Rep_preal)
apply (drule preal_imp_psubset_positives)
apply (auto simp add: psubset_def)
done


subsection{*@{term preal_of_prat}: the Injection from prat to preal*}

lemma rat_less_set_mem_preal: "0 < y ==> {u::rat. 0 < u & u < y} \<in> preal"
apply (auto simp add: preal_def cut_def intro: order_less_trans)
apply (force simp only: eq_commute [of "{}"] interval_empty_iff)
apply (blast dest: dense intro: order_less_trans)
done

lemma rat_subset_imp_le:
     "[|{u::rat. 0 < u & u < x} \<subseteq> {u. 0 < u & u < y}; 0<x|] ==> x \<le> y"
apply (simp add: linorder_not_less [symmetric])
apply (blast dest: dense intro: order_less_trans)
done

lemma rat_set_eq_imp_eq:
     "[|{u::rat. 0 < u & u < x} = {u. 0 < u & u < y};
        0 < x; 0 < y|] ==> x = y"
by (blast intro: rat_subset_imp_le order_antisym)



subsection{*Theorems for Ordering*}

text{*A positive fraction not in a positive real is an upper bound.
 Gleason p. 122 - Remark (1)*}

lemma not_in_preal_ub:
     assumes A: "A \<in> preal"
         and notx: "x \<notin> A"
         and y: "y \<in> A"
         and pos: "0 < x"
        shows "y < x"
proof (cases rule: linorder_cases)
  assume "x<y"
  with notx show ?thesis
    by (simp add:  preal_downwards_closed [OF A y] pos)
next
  assume "x=y"
  with notx and y show ?thesis by simp
next
  assume "y<x"
  thus ?thesis by assumption
qed

lemmas not_in_Rep_preal_ub = not_in_preal_ub [OF Rep_preal]


subsection{*The @{text "\<le>"} Ordering*}

lemma preal_le_refl: "w \<le> (w::preal)"
by (simp add: preal_le_def)

lemma preal_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::preal)"
by (force simp add: preal_le_def)

lemma preal_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::preal)"
apply (simp add: preal_le_def)
apply (rule Rep_preal_inject [THEN iffD1], blast)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma preal_less_le: "((w::preal) < z) = (w \<le> z & w \<noteq> z)"
by (simp add: preal_le_def preal_less_def Rep_preal_inject psubset_def)

instance preal :: order
  by intro_classes
    (assumption |
      rule preal_le_refl preal_le_trans preal_le_anti_sym preal_less_le)+

lemma preal_imp_pos: "[|A \<in> preal; r \<in> A|] ==> 0 < r"
by (insert preal_imp_psubset_positives, blast)

lemma preal_le_linear: "x <= y | y <= (x::preal)"
apply (auto simp add: preal_le_def)
apply (rule ccontr)
apply (blast dest: not_in_Rep_preal_ub intro: preal_imp_pos [OF Rep_preal]
             elim: order_less_asym)
done

instance preal :: linorder
  by intro_classes (rule preal_le_linear)



subsection{*Properties of Addition*}

lemma preal_add_commute: "(x::preal) + y = y + x"
apply (unfold preal_add_def add_set_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (force simp add: add_commute)
done

text{*Lemmas for proving that addition of two positive reals gives
 a positive real*}

lemma empty_psubset_nonempty: "a \<in> A ==> {} \<subset> A"
by blast

text{*Part 1 of Dedekind sections definition*}
lemma add_set_not_empty:
     "[|A \<in> preal; B \<in> preal|] ==> {} \<subset> add_set A B"
apply (insert preal_nonempty [of A] preal_nonempty [of B]) 
apply (auto simp add: add_set_def)
done

text{*Part 2 of Dedekind sections definition.  A structured version of
this proof is @{text preal_not_mem_mult_set_Ex} below.*}
lemma preal_not_mem_add_set_Ex:
     "[|A \<in> preal; B \<in> preal|] ==> \<exists>q. 0 < q & q \<notin> add_set A B"
apply (insert preal_exists_bound [of A] preal_exists_bound [of B], auto) 
apply (rule_tac x = "x+xa" in exI)
apply (simp add: add_set_def, clarify)
apply (drule not_in_preal_ub, assumption+)+
apply (force dest: add_strict_mono)
done

lemma add_set_not_rat_set:
   assumes A: "A \<in> preal" 
       and B: "B \<in> preal"
     shows "add_set A B < {r. 0 < r}"
proof
  from preal_imp_pos [OF A] preal_imp_pos [OF B]
  show "add_set A B \<subseteq> {r. 0 < r}" by (force simp add: add_set_def) 
next
  show "add_set A B \<noteq> {r. 0 < r}"
    by (insert preal_not_mem_add_set_Ex [OF A B], blast) 
qed

text{*Part 3 of Dedekind sections definition*}
lemma add_set_lemma3:
     "[|A \<in> preal; B \<in> preal; u \<in> add_set A B; 0 < z; z < u|] 
      ==> z \<in> add_set A B"
proof (unfold add_set_def, clarify)
  fix x::rat and y::rat
  assume A: "A \<in> preal" 
     and B: "B \<in> preal"
     and [simp]: "0 < z"
     and zless: "z < x + y"
     and x:  "x \<in> A"
     and y:  "y \<in> B"
  have xpos [simp]: "0<x" by (rule preal_imp_pos [OF A x])
  have ypos [simp]: "0<y" by (rule preal_imp_pos [OF B y])
  have xypos [simp]: "0 < x+y" by (simp add: pos_add_strict)
  let ?f = "z/(x+y)"
  have fless: "?f < 1" by (simp add: zless pos_divide_less_eq)
  show "\<exists>x' \<in> A. \<exists>y'\<in>B. z = x' + y'"
  proof
    show "\<exists>y' \<in> B. z = x*?f + y'"
    proof
      show "z = x*?f + y*?f"
	by (simp add: left_distrib [symmetric] divide_inverse mult_ac
		      order_less_imp_not_eq2)
    next
      show "y * ?f \<in> B"
      proof (rule preal_downwards_closed [OF B y])
        show "0 < y * ?f"
          by (simp add: divide_inverse zero_less_mult_iff)
      next
        show "y * ?f < y"
          by (insert mult_strict_left_mono [OF fless ypos], simp)
      qed
    qed
  next
    show "x * ?f \<in> A"
    proof (rule preal_downwards_closed [OF A x])
      show "0 < x * ?f"
	by (simp add: divide_inverse zero_less_mult_iff)
    next
      show "x * ?f < x"
	by (insert mult_strict_left_mono [OF fless xpos], simp)
    qed
  qed
qed

text{*Part 4 of Dedekind sections definition*}
lemma add_set_lemma4:
     "[|A \<in> preal; B \<in> preal; y \<in> add_set A B|] ==> \<exists>u \<in> add_set A B. y < u"
apply (auto simp add: add_set_def)
apply (frule preal_exists_greater [of A], auto) 
apply (rule_tac x="u + y" in exI)
apply (auto intro: add_strict_left_mono)
done

lemma mem_add_set:
     "[|A \<in> preal; B \<in> preal|] ==> add_set A B \<in> preal"
apply (simp (no_asm_simp) add: preal_def cut_def)
apply (blast intro!: add_set_not_empty add_set_not_rat_set
                     add_set_lemma3 add_set_lemma4)
done

lemma preal_add_assoc: "((x::preal) + y) + z = x + (y + z)"
apply (simp add: preal_add_def mem_add_set Rep_preal)
apply (force simp add: add_set_def add_ac)
done

lemma preal_add_left_commute: "x + (y + z) = y + ((x + z)::preal)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule preal_add_assoc)
  apply (rule preal_add_commute)
  done

text{* Positive Real addition is an AC operator *}
lemmas preal_add_ac = preal_add_assoc preal_add_commute preal_add_left_commute


subsection{*Properties of Multiplication*}

text{*Proofs essentially same as for addition*}

lemma preal_mult_commute: "(x::preal) * y = y * x"
apply (unfold preal_mult_def mult_set_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (force simp add: mult_commute)
done

text{*Multiplication of two positive reals gives a positive real.}

text{*Lemmas for proving positive reals multiplication set in @{typ preal}*}

text{*Part 1 of Dedekind sections definition*}
lemma mult_set_not_empty:
     "[|A \<in> preal; B \<in> preal|] ==> {} \<subset> mult_set A B"
apply (insert preal_nonempty [of A] preal_nonempty [of B]) 
apply (auto simp add: mult_set_def)
done

text{*Part 2 of Dedekind sections definition*}
lemma preal_not_mem_mult_set_Ex:
   assumes A: "A \<in> preal" 
       and B: "B \<in> preal"
     shows "\<exists>q. 0 < q & q \<notin> mult_set A B"
proof -
  from preal_exists_bound [OF A]
  obtain x where [simp]: "0 < x" "x \<notin> A" by blast
  from preal_exists_bound [OF B]
  obtain y where [simp]: "0 < y" "y \<notin> B" by blast
  show ?thesis
  proof (intro exI conjI)
    show "0 < x*y" by (simp add: mult_pos)
    show "x * y \<notin> mult_set A B"
    proof -
      { fix u::rat and v::rat
	      assume "u \<in> A" and "v \<in> B" and "x*y = u*v"
	      moreover
	      with prems have "u<x" and "v<y" by (blast dest: not_in_preal_ub)+
	      moreover
	      with prems have "0\<le>v"
	        by (blast intro: preal_imp_pos [OF B]  order_less_imp_le prems)
	      moreover
        from calculation
	      have "u*v < x*y" by (blast intro: mult_strict_mono prems)
	      ultimately have False by force }
      thus ?thesis by (auto simp add: mult_set_def)
    qed
  qed
qed

lemma mult_set_not_rat_set:
   assumes A: "A \<in> preal" 
       and B: "B \<in> preal"
     shows "mult_set A B < {r. 0 < r}"
proof
  show "mult_set A B \<subseteq> {r. 0 < r}"
    by (force simp add: mult_set_def
              intro: preal_imp_pos [OF A] preal_imp_pos [OF B] mult_pos)
next
  show "mult_set A B \<noteq> {r. 0 < r}"
    by (insert preal_not_mem_mult_set_Ex [OF A B], blast)
qed



text{*Part 3 of Dedekind sections definition*}
lemma mult_set_lemma3:
     "[|A \<in> preal; B \<in> preal; u \<in> mult_set A B; 0 < z; z < u|] 
      ==> z \<in> mult_set A B"
proof (unfold mult_set_def, clarify)
  fix x::rat and y::rat
  assume A: "A \<in> preal" 
     and B: "B \<in> preal"
     and [simp]: "0 < z"
     and zless: "z < x * y"
     and x:  "x \<in> A"
     and y:  "y \<in> B"
  have [simp]: "0<y" by (rule preal_imp_pos [OF B y])
  show "\<exists>x' \<in> A. \<exists>y' \<in> B. z = x' * y'"
  proof
    show "\<exists>y'\<in>B. z = (z/y) * y'"
    proof
      show "z = (z/y)*y"
	by (simp add: divide_inverse mult_commute [of y] mult_assoc
		      order_less_imp_not_eq2)
      show "y \<in> B" .
    qed
  next
    show "z/y \<in> A"
    proof (rule preal_downwards_closed [OF A x])
      show "0 < z/y"
	by (simp add: zero_less_divide_iff)
      show "z/y < x" by (simp add: pos_divide_less_eq zless)
    qed
  qed
qed

text{*Part 4 of Dedekind sections definition*}
lemma mult_set_lemma4:
     "[|A \<in> preal; B \<in> preal; y \<in> mult_set A B|] ==> \<exists>u \<in> mult_set A B. y < u"
apply (auto simp add: mult_set_def)
apply (frule preal_exists_greater [of A], auto) 
apply (rule_tac x="u * y" in exI)
apply (auto intro: preal_imp_pos [of A] preal_imp_pos [of B] 
                   mult_strict_right_mono)
done


lemma mem_mult_set:
     "[|A \<in> preal; B \<in> preal|] ==> mult_set A B \<in> preal"
apply (simp (no_asm_simp) add: preal_def cut_def)
apply (blast intro!: mult_set_not_empty mult_set_not_rat_set
                     mult_set_lemma3 mult_set_lemma4)
done

lemma preal_mult_assoc: "((x::preal) * y) * z = x * (y * z)"
apply (simp add: preal_mult_def mem_mult_set Rep_preal)
apply (force simp add: mult_set_def mult_ac)
done

lemma preal_mult_left_commute: "x * (y * z) = y * ((x * z)::preal)"
  apply (rule mk_left_commute [of "op *"])
  apply (rule preal_mult_assoc)
  apply (rule preal_mult_commute)
  done


text{* Positive Real multiplication is an AC operator *}
lemmas preal_mult_ac =
       preal_mult_assoc preal_mult_commute preal_mult_left_commute


text{* Positive real 1 is the multiplicative identity element *}

lemma rat_mem_preal: "0 < q ==> {r::rat. 0 < r & r < q} \<in> preal"
by (simp add: preal_def cut_of_rat)

lemma preal_mult_1: "(preal_of_rat 1) * z = z"
proof (induct z)
  fix A :: "rat set"
  assume A: "A \<in> preal"
  have "{w. \<exists>u. 0 < u \<and> u < 1 & (\<exists>v \<in> A. w = u * v)} = A" (is "?lhs = A")
  proof
    show "?lhs \<subseteq> A"
    proof clarify
      fix x::rat and u::rat and v::rat
      assume upos: "0<u" and "u<1" and v: "v \<in> A"
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      hence "u*v < 1*v" by (simp only: mult_strict_right_mono prems)
      thus "u * v \<in> A"
        by (force intro: preal_downwards_closed [OF A v] mult_pos upos vpos)
    qed
  next
    show "A \<subseteq> ?lhs"
    proof clarify
      fix x::rat
      assume x: "x \<in> A"
      have xpos: "0<x" by (rule preal_imp_pos [OF A x])
      from preal_exists_greater [OF A x]
      obtain v where v: "v \<in> A" and xlessv: "x < v" ..
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      show "\<exists>u. 0 < u \<and> u < 1 \<and> (\<exists>v\<in>A. x = u * v)"
      proof (intro exI conjI)
        show "0 < x/v"
          by (simp add: zero_less_divide_iff xpos vpos)
	show "x / v < 1"
          by (simp add: pos_divide_less_eq vpos xlessv)
        show "\<exists>v'\<in>A. x = (x / v) * v'"
        proof
          show "x = (x/v)*v"
	    by (simp add: divide_inverse mult_assoc vpos
                          order_less_imp_not_eq2)
          show "v \<in> A" .
        qed
      qed
    qed
  qed
  thus "preal_of_rat 1 * Abs_preal A = Abs_preal A"
    by (simp add: preal_of_rat_def preal_mult_def mult_set_def 
                  rat_mem_preal A)
qed


lemma preal_mult_1_right: "z * (preal_of_rat 1) = z"
apply (rule preal_mult_commute [THEN subst])
apply (rule preal_mult_1)
done


subsection{*Distribution of Multiplication across Addition*}

lemma mem_Rep_preal_add_iff:
      "(z \<in> Rep_preal(R+S)) = (\<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. z = x + y)"
apply (simp add: preal_add_def mem_add_set Rep_preal)
apply (simp add: add_set_def) 
done

lemma mem_Rep_preal_mult_iff:
      "(z \<in> Rep_preal(R*S)) = (\<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. z = x * y)"
apply (simp add: preal_mult_def mem_mult_set Rep_preal)
apply (simp add: mult_set_def) 
done

lemma distrib_subset1:
     "Rep_preal (w * (x + y)) \<subseteq> Rep_preal (w * x + w * y)"
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_mult_iff)
apply (force simp add: right_distrib)
done

lemma linorder_le_cases [case_names le ge]:
    "((x::'a::linorder) <= y ==> P) ==> (y <= x ==> P) ==> P"
  apply (insert linorder_linear, blast)
  done

lemma preal_add_mult_distrib_mean:
  assumes a: "a \<in> Rep_preal w"
      and b: "b \<in> Rep_preal w"
      and d: "d \<in> Rep_preal x"
      and e: "e \<in> Rep_preal y"
     shows "\<exists>c \<in> Rep_preal w. a * d + b * e = c * (d + e)"
proof
  let ?c = "(a*d + b*e)/(d+e)"
  have [simp]: "0<a" "0<b" "0<d" "0<e" "0<d+e"
    by (blast intro: preal_imp_pos [OF Rep_preal] a b d e pos_add_strict)+
  have cpos: "0 < ?c"
    by (simp add: zero_less_divide_iff zero_less_mult_iff pos_add_strict)
  show "a * d + b * e = ?c * (d + e)"
    by (simp add: divide_inverse mult_assoc order_less_imp_not_eq2)
  show "?c \<in> Rep_preal w"
    proof (cases rule: linorder_le_cases)
      assume "a \<le> b"
      hence "?c \<le> b"
	by (simp add: pos_divide_le_eq right_distrib mult_right_mono
                      order_less_imp_le)
      thus ?thesis by (rule preal_downwards_closed' [OF Rep_preal b cpos])
    next
      assume "b \<le> a"
      hence "?c \<le> a"
	by (simp add: pos_divide_le_eq right_distrib mult_right_mono
                      order_less_imp_le)
      thus ?thesis by (rule preal_downwards_closed' [OF Rep_preal a cpos])
    qed
  qed

lemma distrib_subset2:
     "Rep_preal (w * x + w * y) \<subseteq> Rep_preal (w * (x + y))"
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_mult_iff)
apply (drule_tac w=w and x=x and y=y in preal_add_mult_distrib_mean, auto)
done

lemma preal_add_mult_distrib2: "(w * ((x::preal) + y)) = (w * x) + (w * y)"
apply (rule inj_Rep_preal [THEN injD])
apply (rule equalityI [OF distrib_subset1 distrib_subset2])
done

lemma preal_add_mult_distrib: "(((x::preal) + y) * w) = (x * w) + (y * w)"
by (simp add: preal_mult_commute preal_add_mult_distrib2)


subsection{*Existence of Inverse, a Positive Real*}

lemma mem_inv_set_ex:
  assumes A: "A \<in> preal" shows "\<exists>x y. 0 < x & x < y & inverse y \<notin> A"
proof -
  from preal_exists_bound [OF A]
  obtain x where [simp]: "0<x" "x \<notin> A" by blast
  show ?thesis
  proof (intro exI conjI)
    show "0 < inverse (x+1)"
      by (simp add: order_less_trans [OF _ less_add_one]) 
    show "inverse(x+1) < inverse x"
      by (simp add: less_imp_inverse_less less_add_one)
    show "inverse (inverse x) \<notin> A"
      by (simp add: order_less_imp_not_eq2)
  qed
qed

text{*Part 1 of Dedekind sections definition*}
lemma inverse_set_not_empty:
     "A \<in> preal ==> {} \<subset> inverse_set A"
apply (insert mem_inv_set_ex [of A])
apply (auto simp add: inverse_set_def)
done

text{*Part 2 of Dedekind sections definition*}

lemma preal_not_mem_inverse_set_Ex:
   assumes A: "A \<in> preal"  shows "\<exists>q. 0 < q & q \<notin> inverse_set A"
proof -
  from preal_nonempty [OF A]
  obtain x where x: "x \<in> A" and  xpos [simp]: "0<x" ..
  show ?thesis
  proof (intro exI conjI)
    show "0 < inverse x" by simp
    show "inverse x \<notin> inverse_set A"
    proof -
      { fix y::rat 
	assume ygt: "inverse x < y"
	have [simp]: "0 < y" by (simp add: order_less_trans [OF _ ygt])
	have iyless: "inverse y < x" 
	  by (simp add: inverse_less_imp_less [of x] ygt)
	have "inverse y \<in> A"
	  by (simp add: preal_downwards_closed [OF A x] iyless)}
     thus ?thesis by (auto simp add: inverse_set_def)
    qed
  qed
qed

lemma inverse_set_not_rat_set:
   assumes A: "A \<in> preal"  shows "inverse_set A < {r. 0 < r}"
proof
  show "inverse_set A \<subseteq> {r. 0 < r}"  by (force simp add: inverse_set_def)
next
  show "inverse_set A \<noteq> {r. 0 < r}"
    by (insert preal_not_mem_inverse_set_Ex [OF A], blast)
qed

text{*Part 3 of Dedekind sections definition*}
lemma inverse_set_lemma3:
     "[|A \<in> preal; u \<in> inverse_set A; 0 < z; z < u|] 
      ==> z \<in> inverse_set A"
apply (auto simp add: inverse_set_def)
apply (auto intro: order_less_trans)
done

text{*Part 4 of Dedekind sections definition*}
lemma inverse_set_lemma4:
     "[|A \<in> preal; y \<in> inverse_set A|] ==> \<exists>u \<in> inverse_set A. y < u"
apply (auto simp add: inverse_set_def)
apply (drule dense [of y]) 
apply (blast intro: order_less_trans)
done


lemma mem_inverse_set:
     "A \<in> preal ==> inverse_set A \<in> preal"
apply (simp (no_asm_simp) add: preal_def cut_def)
apply (blast intro!: inverse_set_not_empty inverse_set_not_rat_set
                     inverse_set_lemma3 inverse_set_lemma4)
done


subsection{*Gleason's Lemma 9-3.4, page 122*}

lemma Gleason9_34_exists:
  assumes A: "A \<in> preal"
      and "\<forall>x\<in>A. x + u \<in> A"
      and "0 \<le> z"
     shows "\<exists>b\<in>A. b + (of_int z) * u \<in> A"
proof (cases z rule: int_cases)
  case (nonneg n)
  show ?thesis
  proof (simp add: prems, induct n)
    case 0
      from preal_nonempty [OF A]
      show ?case  by force 
    case (Suc k)
      from this obtain b where "b \<in> A" "b + of_int (int k) * u \<in> A" ..
      hence "b + of_int (int k)*u + u \<in> A" by (simp add: prems)
      thus ?case by (force simp add: left_distrib add_ac prems) 
  qed
next
  case (neg n)
  with prems show ?thesis by simp
qed

lemma Gleason9_34_contra:
  assumes A: "A \<in> preal"
    shows "[|\<forall>x\<in>A. x + u \<in> A; 0 < u; 0 < y; y \<notin> A|] ==> False"
proof (induct u, induct y)
  fix a::int and b::int
  fix c::int and d::int
  assume bpos [simp]: "0 < b"
     and dpos [simp]: "0 < d"
     and closed: "\<forall>x\<in>A. x + (Fract c d) \<in> A"
     and upos: "0 < Fract c d"
     and ypos: "0 < Fract a b"
     and notin: "Fract a b \<notin> A"
  have cpos [simp]: "0 < c" 
    by (simp add: zero_less_Fract_iff [OF dpos, symmetric] upos) 
  have apos [simp]: "0 < a" 
    by (simp add: zero_less_Fract_iff [OF bpos, symmetric] ypos) 
  let ?k = "a*d"
  have frle: "Fract a b \<le> Fract ?k 1 * (Fract c d)" 
  proof -
    have "?thesis = ((a * d * b * d) \<le> c * b * (a * d * b * d))"
      by (simp add: mult_rat le_rat order_less_imp_not_eq2 mult_ac) 
    moreover
    have "(1 * (a * d * b * d)) \<le> c * b * (a * d * b * d)"
      by (rule mult_mono, 
          simp_all add: int_one_le_iff_zero_less zero_less_mult_iff 
                        order_less_imp_le)
    ultimately
    show ?thesis by simp
  qed
  have k: "0 \<le> ?k" by (simp add: order_less_imp_le zero_less_mult_iff)  
  from Gleason9_34_exists [OF A closed k]
  obtain z where z: "z \<in> A" 
             and mem: "z + of_int ?k * Fract c d \<in> A" ..
  have less: "z + of_int ?k * Fract c d < Fract a b"
    by (rule not_in_preal_ub [OF A notin mem ypos])
  have "0<z" by (rule preal_imp_pos [OF A z])
  with frle and less show False by (simp add: Fract_of_int_eq) 
qed


lemma Gleason9_34:
  assumes A: "A \<in> preal"
      and upos: "0 < u"
    shows "\<exists>r \<in> A. r + u \<notin> A"
proof (rule ccontr, simp)
  assume closed: "\<forall>r\<in>A. r + u \<in> A"
  from preal_exists_bound [OF A]
  obtain y where y: "y \<notin> A" and ypos: "0 < y" by blast
  show False
    by (rule Gleason9_34_contra [OF A closed upos ypos y])
qed



subsection{*Gleason's Lemma 9-3.6*}

lemma lemma_gleason9_36:
  assumes A: "A \<in> preal"
      and x: "1 < x"
    shows "\<exists>r \<in> A. r*x \<notin> A"
proof -
  from preal_nonempty [OF A]
  obtain y where y: "y \<in> A" and  ypos: "0<y" ..
  show ?thesis 
  proof (rule classical)
    assume "~(\<exists>r\<in>A. r * x \<notin> A)"
    with y have ymem: "y * x \<in> A" by blast 
    from ypos mult_strict_left_mono [OF x]
    have yless: "y < y*x" by simp 
    let ?d = "y*x - y"
    from yless have dpos: "0 < ?d" and eq: "y + ?d = y*x" by auto
    from Gleason9_34 [OF A dpos]
    obtain r where r: "r\<in>A" and notin: "r + ?d \<notin> A" ..
    have rpos: "0<r" by (rule preal_imp_pos [OF A r])
    with dpos have rdpos: "0 < r + ?d" by arith
    have "~ (r + ?d \<le> y + ?d)"
    proof
      assume le: "r + ?d \<le> y + ?d" 
      from ymem have yd: "y + ?d \<in> A" by (simp add: eq)
      have "r + ?d \<in> A" by (rule preal_downwards_closed' [OF A yd rdpos le])
      with notin show False by simp
    qed
    hence "y < r" by simp
    with ypos have  dless: "?d < (r * ?d)/y"
      by (simp add: pos_less_divide_eq mult_commute [of ?d]
                    mult_strict_right_mono dpos)
    have "r + ?d < r*x"
    proof -
      have "r + ?d < r + (r * ?d)/y" by (simp add: dless)
      also with ypos have "... = (r/y) * (y + ?d)"
	by (simp only: right_distrib divide_inverse mult_ac, simp)
      also have "... = r*x" using ypos
	by simp
      finally show "r + ?d < r*x" .
    qed
    with r notin rdpos
    show "\<exists>r\<in>A. r * x \<notin> A" by (blast dest:  preal_downwards_closed [OF A])
  qed  
qed

subsection{*Existence of Inverse: Part 2*}

lemma mem_Rep_preal_inverse_iff:
      "(z \<in> Rep_preal(inverse R)) = 
       (0 < z \<and> (\<exists>y. z < y \<and> inverse y \<notin> Rep_preal R))"
apply (simp add: preal_inverse_def mem_inverse_set Rep_preal)
apply (simp add: inverse_set_def) 
done

lemma Rep_preal_of_rat:
     "0 < q ==> Rep_preal (preal_of_rat q) = {x. 0 < x \<and> x < q}"
by (simp add: preal_of_rat_def rat_mem_preal) 

lemma subset_inverse_mult_lemma:
      assumes xpos: "0 < x" and xless: "x < 1"
         shows "\<exists>r u y. 0 < r & r < y & inverse y \<notin> Rep_preal R & 
                        u \<in> Rep_preal R & x = r * u"
proof -
  from xpos and xless have "1 < inverse x" by (simp add: one_less_inverse_iff)
  from lemma_gleason9_36 [OF Rep_preal this]
  obtain r where r: "r \<in> Rep_preal R" 
             and notin: "r * (inverse x) \<notin> Rep_preal R" ..
  have rpos: "0<r" by (rule preal_imp_pos [OF Rep_preal r])
  from preal_exists_greater [OF Rep_preal r]
  obtain u where u: "u \<in> Rep_preal R" and rless: "r < u" ..
  have upos: "0<u" by (rule preal_imp_pos [OF Rep_preal u])
  show ?thesis
  proof (intro exI conjI)
    show "0 < x/u" using xpos upos
      by (simp add: zero_less_divide_iff)  
    show "x/u < x/r" using xpos upos rpos
      by (simp add: divide_inverse mult_less_cancel_left rless) 
    show "inverse (x / r) \<notin> Rep_preal R" using notin
      by (simp add: divide_inverse mult_commute) 
    show "u \<in> Rep_preal R" by (rule u) 
    show "x = x / u * u" using upos 
      by (simp add: divide_inverse mult_commute) 
  qed
qed

lemma subset_inverse_mult: 
     "Rep_preal(preal_of_rat 1) \<subseteq> Rep_preal(inverse R * R)"
apply (auto simp add: Bex_def Rep_preal_of_rat mem_Rep_preal_inverse_iff 
                      mem_Rep_preal_mult_iff)
apply (blast dest: subset_inverse_mult_lemma) 
done

lemma inverse_mult_subset_lemma:
     assumes rpos: "0 < r" 
         and rless: "r < y"
         and notin: "inverse y \<notin> Rep_preal R"
         and q: "q \<in> Rep_preal R"
     shows "r*q < 1"
proof -
  have "q < inverse y" using rpos rless
    by (simp add: not_in_preal_ub [OF Rep_preal notin] q)
  hence "r * q < r/y" using rpos
    by (simp add: divide_inverse mult_less_cancel_left)
  also have "... \<le> 1" using rpos rless
    by (simp add: pos_divide_le_eq)
  finally show ?thesis .
qed

lemma inverse_mult_subset:
     "Rep_preal(inverse R * R) \<subseteq> Rep_preal(preal_of_rat 1)"
apply (auto simp add: Bex_def Rep_preal_of_rat mem_Rep_preal_inverse_iff 
                      mem_Rep_preal_mult_iff)
apply (simp add: zero_less_mult_iff preal_imp_pos [OF Rep_preal]) 
apply (blast intro: inverse_mult_subset_lemma) 
done

lemma preal_mult_inverse:
     "inverse R * R = (preal_of_rat 1)"
apply (rule inj_Rep_preal [THEN injD])
apply (rule equalityI [OF inverse_mult_subset subset_inverse_mult]) 
done

lemma preal_mult_inverse_right:
     "R * inverse R = (preal_of_rat 1)"
apply (rule preal_mult_commute [THEN subst])
apply (rule preal_mult_inverse)
done


text{*Theorems needing @{text Gleason9_34}*}

lemma Rep_preal_self_subset: "Rep_preal (R) \<subseteq> Rep_preal(R + S)"
proof 
  fix r
  assume r: "r \<in> Rep_preal R"
  have rpos: "0<r" by (rule preal_imp_pos [OF Rep_preal r])
  from mem_Rep_preal_Ex 
  obtain y where y: "y \<in> Rep_preal S" ..
  have ypos: "0<y" by (rule preal_imp_pos [OF Rep_preal y])
  have ry: "r+y \<in> Rep_preal(R + S)" using r y
    by (auto simp add: mem_Rep_preal_add_iff)
  show "r \<in> Rep_preal(R + S)" using r ypos rpos 
    by (simp add:  preal_downwards_closed [OF Rep_preal ry]) 
qed

lemma Rep_preal_sum_not_subset: "~ Rep_preal (R + S) \<subseteq> Rep_preal(R)"
proof -
  from mem_Rep_preal_Ex 
  obtain y where y: "y \<in> Rep_preal S" ..
  have ypos: "0<y" by (rule preal_imp_pos [OF Rep_preal y])
  from  Gleason9_34 [OF Rep_preal ypos]
  obtain r where r: "r \<in> Rep_preal R" and notin: "r + y \<notin> Rep_preal R" ..
  have "r + y \<in> Rep_preal (R + S)" using r y
    by (auto simp add: mem_Rep_preal_add_iff)
  thus ?thesis using notin by blast
qed

lemma Rep_preal_sum_not_eq: "Rep_preal (R + S) \<noteq> Rep_preal(R)"
by (insert Rep_preal_sum_not_subset, blast)

text{*at last, Gleason prop. 9-3.5(iii) page 123*}
lemma preal_self_less_add_left: "(R::preal) < R + S"
apply (unfold preal_less_def psubset_def)
apply (simp add: Rep_preal_self_subset Rep_preal_sum_not_eq [THEN not_sym])
done

lemma preal_self_less_add_right: "(R::preal) < S + R"
by (simp add: preal_add_commute preal_self_less_add_left)

lemma preal_not_eq_self: "x \<noteq> x + (y::preal)"
by (insert preal_self_less_add_left [of x y], auto)


subsection{*Subtraction for Positive Reals*}

text{*Gleason prop. 9-3.5(iv), page 123: proving @{term "A < B ==> \<exists>D. A + D =
B"}. We define the claimed @{term D} and show that it is a positive real*}

text{*Part 1 of Dedekind sections definition*}
lemma diff_set_not_empty:
     "R < S ==> {} \<subset> diff_set (Rep_preal S) (Rep_preal R)"
apply (auto simp add: preal_less_def diff_set_def elim!: equalityE) 
apply (frule_tac x1 = S in Rep_preal [THEN preal_exists_greater])
apply (drule preal_imp_pos [OF Rep_preal], clarify)
apply (cut_tac a=x and b=u in add_eq_exists, force) 
done

text{*Part 2 of Dedekind sections definition*}
lemma diff_set_nonempty:
     "\<exists>q. 0 < q & q \<notin> diff_set (Rep_preal S) (Rep_preal R)"
apply (cut_tac X = S in Rep_preal_exists_bound)
apply (erule exE)
apply (rule_tac x = x in exI, auto)
apply (simp add: diff_set_def) 
apply (auto dest: Rep_preal [THEN preal_downwards_closed])
done

lemma diff_set_not_rat_set:
     "diff_set (Rep_preal S) (Rep_preal R) < {r. 0 < r}" (is "?lhs < ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" by (auto simp add: diff_set_def) 
  show "?lhs \<noteq> ?rhs" using diff_set_nonempty by blast
qed

text{*Part 3 of Dedekind sections definition*}
lemma diff_set_lemma3:
     "[|R < S; u \<in> diff_set (Rep_preal S) (Rep_preal R); 0 < z; z < u|] 
      ==> z \<in> diff_set (Rep_preal S) (Rep_preal R)"
apply (auto simp add: diff_set_def) 
apply (rule_tac x=x in exI) 
apply (drule Rep_preal [THEN preal_downwards_closed], auto)
done

text{*Part 4 of Dedekind sections definition*}
lemma diff_set_lemma4:
     "[|R < S; y \<in> diff_set (Rep_preal S) (Rep_preal R)|] 
      ==> \<exists>u \<in> diff_set (Rep_preal S) (Rep_preal R). y < u"
apply (auto simp add: diff_set_def) 
apply (drule Rep_preal [THEN preal_exists_greater], clarify) 
apply (cut_tac a="x+y" and b=u in add_eq_exists, clarify)  
apply (rule_tac x="y+xa" in exI) 
apply (auto simp add: add_ac)
done

lemma mem_diff_set:
     "R < S ==> diff_set (Rep_preal S) (Rep_preal R) \<in> preal"
apply (unfold preal_def cut_def)
apply (blast intro!: diff_set_not_empty diff_set_not_rat_set
                     diff_set_lemma3 diff_set_lemma4)
done

lemma mem_Rep_preal_diff_iff:
      "R < S ==>
       (z \<in> Rep_preal(S-R)) = 
       (\<exists>x. 0 < x & 0 < z & x \<notin> Rep_preal R & x + z \<in> Rep_preal S)"
apply (simp add: preal_diff_def mem_diff_set Rep_preal)
apply (force simp add: diff_set_def) 
done


text{*proving that @{term "R + D \<le> S"}*}

lemma less_add_left_lemma:
  assumes Rless: "R < S"
      and a: "a \<in> Rep_preal R"
      and cb: "c + b \<in> Rep_preal S"
      and "c \<notin> Rep_preal R"
      and "0 < b"
      and "0 < c"
  shows "a + b \<in> Rep_preal S"
proof -
  have "0<a" by (rule preal_imp_pos [OF Rep_preal a])
  moreover
  have "a < c" using prems
    by (blast intro: not_in_Rep_preal_ub ) 
  ultimately show ?thesis using prems
    by (simp add: preal_downwards_closed [OF Rep_preal cb]) 
qed

lemma less_add_left_le1:
       "R < (S::preal) ==> R + (S-R) \<le> S"
apply (auto simp add: Bex_def preal_le_def mem_Rep_preal_add_iff 
                      mem_Rep_preal_diff_iff)
apply (blast intro: less_add_left_lemma) 
done

subsection{*proving that @{term "S \<le> R + D"} --- trickier*}

lemma lemma_sum_mem_Rep_preal_ex:
     "x \<in> Rep_preal S ==> \<exists>e. 0 < e & x + e \<in> Rep_preal S"
apply (drule Rep_preal [THEN preal_exists_greater], clarify) 
apply (cut_tac a=x and b=u in add_eq_exists, auto) 
done

lemma less_add_left_lemma2:
  assumes Rless: "R < S"
      and x:     "x \<in> Rep_preal S"
      and xnot: "x \<notin>  Rep_preal R"
  shows "\<exists>u v z. 0 < v & 0 < z & u \<in> Rep_preal R & z \<notin> Rep_preal R & 
                     z + v \<in> Rep_preal S & x = u + v"
proof -
  have xpos: "0<x" by (rule preal_imp_pos [OF Rep_preal x])
  from lemma_sum_mem_Rep_preal_ex [OF x]
  obtain e where epos: "0 < e" and xe: "x + e \<in> Rep_preal S" by blast
  from  Gleason9_34 [OF Rep_preal epos]
  obtain r where r: "r \<in> Rep_preal R" and notin: "r + e \<notin> Rep_preal R" ..
  with x xnot xpos have rless: "r < x" by (blast intro: not_in_Rep_preal_ub)
  from add_eq_exists [of r x]
  obtain y where eq: "x = r+y" by auto
  show ?thesis 
  proof (intro exI conjI)
    show "r \<in> Rep_preal R" by (rule r)
    show "r + e \<notin> Rep_preal R" by (rule notin)
    show "r + e + y \<in> Rep_preal S" using xe eq by (simp add: add_ac)
    show "x = r + y" by (simp add: eq)
    show "0 < r + e" using epos preal_imp_pos [OF Rep_preal r]
      by simp
    show "0 < y" using rless eq by arith
  qed
qed

lemma less_add_left_le2: "R < (S::preal) ==> S \<le> R + (S-R)"
apply (auto simp add: preal_le_def)
apply (case_tac "x \<in> Rep_preal R")
apply (cut_tac Rep_preal_self_subset [of R], force)
apply (auto simp add: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_diff_iff)
apply (blast dest: less_add_left_lemma2)
done

lemma less_add_left: "R < (S::preal) ==> R + (S-R) = S"
by (blast intro: preal_le_anti_sym [OF less_add_left_le1 less_add_left_le2])

lemma less_add_left_Ex: "R < (S::preal) ==> \<exists>D. R + D = S"
by (fast dest: less_add_left)

lemma preal_add_less2_mono1: "R < (S::preal) ==> R + T < S + T"
apply (auto dest!: less_add_left_Ex simp add: preal_add_assoc)
apply (rule_tac y1 = D in preal_add_commute [THEN subst])
apply (auto intro: preal_self_less_add_left simp add: preal_add_assoc [symmetric])
done

lemma preal_add_less2_mono2: "R < (S::preal) ==> T + R < T + S"
by (auto intro: preal_add_less2_mono1 simp add: preal_add_commute [of T])

lemma preal_add_right_less_cancel: "R + T < S + T ==> R < (S::preal)"
apply (insert linorder_less_linear [of R S], auto)
apply (drule_tac R = S and T = T in preal_add_less2_mono1)
apply (blast dest: order_less_trans) 
done

lemma preal_add_left_less_cancel: "T + R < T + S ==> R <  (S::preal)"
by (auto elim: preal_add_right_less_cancel simp add: preal_add_commute [of T])

lemma preal_add_less_cancel_right: "((R::preal) + T < S + T) = (R < S)"
by (blast intro: preal_add_less2_mono1 preal_add_right_less_cancel)

lemma preal_add_less_cancel_left: "(T + (R::preal) < T + S) = (R < S)"
by (blast intro: preal_add_less2_mono2 preal_add_left_less_cancel)

lemma preal_add_le_cancel_right: "((R::preal) + T \<le> S + T) = (R \<le> S)"
by (simp add: linorder_not_less [symmetric] preal_add_less_cancel_right) 

lemma preal_add_le_cancel_left: "(T + (R::preal) \<le> T + S) = (R \<le> S)"
by (simp add: linorder_not_less [symmetric] preal_add_less_cancel_left) 

lemma preal_add_less_mono:
     "[| x1 < y1; x2 < y2 |] ==> x1 + x2 < y1 + (y2::preal)"
apply (auto dest!: less_add_left_Ex simp add: preal_add_ac)
apply (rule preal_add_assoc [THEN subst])
apply (rule preal_self_less_add_right)
done

lemma preal_add_right_cancel: "(R::preal) + T = S + T ==> R = S"
apply (insert linorder_less_linear [of R S], safe)
apply (drule_tac [!] T = T in preal_add_less2_mono1, auto)
done

lemma preal_add_left_cancel: "C + A = C + B ==> A = (B::preal)"
by (auto intro: preal_add_right_cancel simp add: preal_add_commute)

lemma preal_add_left_cancel_iff: "(C + A = C + B) = ((A::preal) = B)"
by (fast intro: preal_add_left_cancel)

lemma preal_add_right_cancel_iff: "(A + C = B + C) = ((A::preal) = B)"
by (fast intro: preal_add_right_cancel)

lemmas preal_cancels =
    preal_add_less_cancel_right preal_add_less_cancel_left
    preal_add_le_cancel_right preal_add_le_cancel_left
    preal_add_left_cancel_iff preal_add_right_cancel_iff


subsection{*Completeness of type @{typ preal}*}

text{*Prove that supremum is a cut*}

text{*Part 1 of Dedekind sections definition*}

lemma preal_sup_set_not_empty:
     "P \<noteq> {} ==> {} \<subset> (\<Union>X \<in> P. Rep_preal(X))"
apply auto
apply (cut_tac X = x in mem_Rep_preal_Ex, auto)
done


text{*Part 2 of Dedekind sections definition*}

lemma preal_sup_not_exists:
     "\<forall>X \<in> P. X \<le> Y ==> \<exists>q. 0 < q & q \<notin> (\<Union>X \<in> P. Rep_preal(X))"
apply (cut_tac X = Y in Rep_preal_exists_bound)
apply (auto simp add: preal_le_def)
done

lemma preal_sup_set_not_rat_set:
     "\<forall>X \<in> P. X \<le> Y ==> (\<Union>X \<in> P. Rep_preal(X)) < {r. 0 < r}"
apply (drule preal_sup_not_exists)
apply (blast intro: preal_imp_pos [OF Rep_preal])  
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_sup_set_lemma3:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y; u \<in> (\<Union>X \<in> P. Rep_preal(X)); 0 < z; z < u|]
      ==> z \<in> (\<Union>X \<in> P. Rep_preal(X))"
by (auto elim: Rep_preal [THEN preal_downwards_closed])

text{*Part 4 of Dedekind sections definition*}
lemma preal_sup_set_lemma4:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y; y \<in> (\<Union>X \<in> P. Rep_preal(X)) |]
          ==> \<exists>u \<in> (\<Union>X \<in> P. Rep_preal(X)). y < u"
by (blast dest: Rep_preal [THEN preal_exists_greater])

lemma preal_sup:
     "[|P \<noteq> {}; \<forall>X \<in> P. X \<le> Y|] ==> (\<Union>X \<in> P. Rep_preal(X)) \<in> preal"
apply (unfold preal_def cut_def)
apply (blast intro!: preal_sup_set_not_empty preal_sup_set_not_rat_set
                     preal_sup_set_lemma3 preal_sup_set_lemma4)
done

lemma preal_psup_le:
     "[| \<forall>X \<in> P. X \<le> Y;  x \<in> P |] ==> x \<le> psup P"
apply (simp (no_asm_simp) add: preal_le_def) 
apply (subgoal_tac "P \<noteq> {}") 
apply (auto simp add: psup_def preal_sup) 
done

lemma psup_le_ub: "[| P \<noteq> {}; \<forall>X \<in> P. X \<le> Y |] ==> psup P \<le> Y"
apply (simp (no_asm_simp) add: preal_le_def)
apply (simp add: psup_def preal_sup) 
apply (auto simp add: preal_le_def)
done

text{*Supremum property*}
lemma preal_complete:
     "[| P \<noteq> {}; \<forall>X \<in> P. X \<le> Y |] ==> (\<exists>X \<in> P. Z < X) = (Z < psup P)"
apply (simp add: preal_less_def psup_def preal_sup)
apply (auto simp add: preal_le_def)
apply (rename_tac U) 
apply (cut_tac x = U and y = Z in linorder_less_linear)
apply (auto simp add: preal_less_def)
done


subsection{*The Embadding from @{typ rat} into @{typ preal}*}

lemma preal_of_rat_add_lemma1:
     "[|x < y + z; 0 < x; 0 < y|] ==> x * y * inverse (y + z) < (y::rat)"
apply (frule_tac c = "y * inverse (y + z) " in mult_strict_right_mono)
apply (simp add: zero_less_mult_iff) 
apply (simp add: mult_ac)
done

lemma preal_of_rat_add_lemma2:
  assumes "u < x + y"
      and "0 < x"
      and "0 < y"
      and "0 < u"
  shows "\<exists>v w::rat. w < y & 0 < v & v < x & 0 < w & u = v + w"
proof (intro exI conjI)
  show "u * x * inverse(x+y) < x" using prems 
    by (simp add: preal_of_rat_add_lemma1) 
  show "u * y * inverse(x+y) < y" using prems 
    by (simp add: preal_of_rat_add_lemma1 add_commute [of x]) 
  show "0 < u * x * inverse (x + y)" using prems
    by (simp add: zero_less_mult_iff) 
  show "0 < u * y * inverse (x + y)" using prems
    by (simp add: zero_less_mult_iff) 
  show "u = u * x * inverse (x + y) + u * y * inverse (x + y)" using prems
    by (simp add: left_distrib [symmetric] right_distrib [symmetric] mult_ac)
qed

lemma preal_of_rat_add:
     "[| 0 < x; 0 < y|] 
      ==> preal_of_rat ((x::rat) + y) = preal_of_rat x + preal_of_rat y"
apply (unfold preal_of_rat_def preal_add_def)
apply (simp add: rat_mem_preal) 
apply (rule_tac f = Abs_preal in arg_cong)
apply (auto simp add: add_set_def) 
apply (blast dest: preal_of_rat_add_lemma2) 
done

lemma preal_of_rat_mult_lemma1:
     "[|x < y; 0 < x; 0 < z|] ==> x * z * inverse y < (z::rat)"
apply (frule_tac c = "z * inverse y" in mult_strict_right_mono)
apply (simp add: zero_less_mult_iff)
apply (subgoal_tac "y * (z * inverse y) = z * (y * inverse y)")
apply (simp_all add: mult_ac)
done

lemma preal_of_rat_mult_lemma2: 
  assumes xless: "x < y * z"
      and xpos: "0 < x"
      and ypos: "0 < y"
  shows "x * z * inverse y * inverse z < (z::rat)"
proof -
  have "0 < y * z" using prems by simp
  hence zpos:  "0 < z" using prems by (simp add: zero_less_mult_iff)
  have "x * z * inverse y * inverse z = x * inverse y * (z * inverse z)"
    by (simp add: mult_ac)
  also have "... = x/y" using zpos
    by (simp add: divide_inverse)
  also have "... < z"
    by (simp add: pos_divide_less_eq [OF ypos] mult_commute) 
  finally show ?thesis .
qed

lemma preal_of_rat_mult_lemma3:
  assumes uless: "u < x * y"
      and "0 < x"
      and "0 < y"
      and "0 < u"
  shows "\<exists>v w::rat. v < x & w < y & 0 < v & 0 < w & u = v * w"
proof -
  from dense [OF uless] 
  obtain r where "u < r" "r < x * y" by blast
  thus ?thesis
  proof (intro exI conjI)
  show "u * x * inverse r < x" using prems 
    by (simp add: preal_of_rat_mult_lemma1) 
  show "r * y * inverse x * inverse y < y" using prems
    by (simp add: preal_of_rat_mult_lemma2)
  show "0 < u * x * inverse r" using prems
    by (simp add: zero_less_mult_iff) 
  show "0 < r * y * inverse x * inverse y" using prems
    by (simp add: zero_less_mult_iff) 
  have "u * x * inverse r * (r * y * inverse x * inverse y) =
        u * (r * inverse r) * (x * inverse x) * (y * inverse y)"
    by (simp only: mult_ac)
  thus "u = u * x * inverse r * (r * y * inverse x * inverse y)" using prems
    by simp
  qed
qed

lemma preal_of_rat_mult:
     "[| 0 < x; 0 < y|] 
      ==> preal_of_rat ((x::rat) * y) = preal_of_rat x * preal_of_rat y"
apply (unfold preal_of_rat_def preal_mult_def)
apply (simp add: rat_mem_preal) 
apply (rule_tac f = Abs_preal in arg_cong)
apply (auto simp add: zero_less_mult_iff mult_strict_mono mult_set_def) 
apply (blast dest: preal_of_rat_mult_lemma3) 
done

lemma preal_of_rat_less_iff:
      "[| 0 < x; 0 < y|] ==> (preal_of_rat x < preal_of_rat y) = (x < y)"
by (force simp add: preal_of_rat_def preal_less_def rat_mem_preal) 

lemma preal_of_rat_le_iff:
      "[| 0 < x; 0 < y|] ==> (preal_of_rat x \<le> preal_of_rat y) = (x \<le> y)"
by (simp add: preal_of_rat_less_iff linorder_not_less [symmetric]) 

lemma preal_of_rat_eq_iff:
      "[| 0 < x; 0 < y|] ==> (preal_of_rat x = preal_of_rat y) = (x = y)"
by (simp add: preal_of_rat_le_iff order_eq_iff) 


ML
{*
val inj_on_Abs_preal = thm"inj_on_Abs_preal";
val inj_Rep_preal = thm"inj_Rep_preal";
val mem_Rep_preal_Ex = thm"mem_Rep_preal_Ex";
val preal_add_commute = thm"preal_add_commute";
val preal_add_assoc = thm"preal_add_assoc";
val preal_add_left_commute = thm"preal_add_left_commute";
val preal_mult_commute = thm"preal_mult_commute";
val preal_mult_assoc = thm"preal_mult_assoc";
val preal_mult_left_commute = thm"preal_mult_left_commute";
val preal_add_mult_distrib2 = thm"preal_add_mult_distrib2";
val preal_add_mult_distrib = thm"preal_add_mult_distrib";
val preal_self_less_add_left = thm"preal_self_less_add_left";
val preal_self_less_add_right = thm"preal_self_less_add_right";
val less_add_left = thm"less_add_left";
val preal_add_less2_mono1 = thm"preal_add_less2_mono1";
val preal_add_less2_mono2 = thm"preal_add_less2_mono2";
val preal_add_right_less_cancel = thm"preal_add_right_less_cancel";
val preal_add_left_less_cancel = thm"preal_add_left_less_cancel";
val preal_add_right_cancel = thm"preal_add_right_cancel";
val preal_add_left_cancel = thm"preal_add_left_cancel";
val preal_add_left_cancel_iff = thm"preal_add_left_cancel_iff";
val preal_add_right_cancel_iff = thm"preal_add_right_cancel_iff";
val preal_psup_le = thm"preal_psup_le";
val psup_le_ub = thm"psup_le_ub";
val preal_complete = thm"preal_complete";
val preal_of_rat_add = thm"preal_of_rat_add";
val preal_of_rat_mult = thm"preal_of_rat_mult";

val preal_add_ac = thms"preal_add_ac";
val preal_mult_ac = thms"preal_mult_ac";
*}

end
