(*  Title:      ZF/Constructible/Relative.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
                With modifications by E. Gunther, M. Pagano, 
                and P. Sánchez Terraf
*)

section \<open>Relativization and Absoluteness\<close>

theory Relative imports ZF begin

subsection\<open>Relativized versions of standard set-theoretic concepts\<close>

definition
  empty :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "empty(M,z) \<equiv> \<forall>x[M]. x \<notin> z"

definition
  subset :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "subset(M,A,B) \<equiv> \<forall>x[M]. x\<in>A \<longrightarrow> x \<in> B"

definition
  upair :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "upair(M,a,b,z) \<equiv> a \<in> z \<and> b \<in> z \<and> (\<forall>x[M]. x\<in>z \<longrightarrow> x = a \<or> x = b)"

definition
  pair :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "pair(M,a,b,z) \<equiv> \<exists>x[M]. upair(M,a,a,x) \<and>
                     (\<exists>y[M]. upair(M,a,b,y) \<and> upair(M,x,y,z))"


definition
  union :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "union(M,a,b,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> a \<or> x \<in> b"

definition
  is_cons :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "is_cons(M,a,b,z) \<equiv> \<exists>x[M]. upair(M,a,a,x) \<and> union(M,x,b,z)"

definition
  successor :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "successor(M,a,z) \<equiv> is_cons(M,a,a,z)"

definition
  number1 :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "number1(M,a) \<equiv> \<exists>x[M]. empty(M,x) \<and> successor(M,x,a)"

definition
  number2 :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "number2(M,a) \<equiv> \<exists>x[M]. number1(M,x) \<and> successor(M,x,a)"

definition
  number3 :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "number3(M,a) \<equiv> \<exists>x[M]. number2(M,x) \<and> successor(M,x,a)"

definition
  powerset :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "powerset(M,A,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> subset(M,x,A)"

definition
  is_Collect :: "[i\<Rightarrow>o,i,i\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_Collect(M,A,P,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> A \<and> P(x)"

definition
  is_Replace :: "[i\<Rightarrow>o,i,[i,i]\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_Replace(M,A,P,z) \<equiv> \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> P(x,u))"

definition
  inter :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "inter(M,a,b,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> a \<and> x \<in> b"

definition
  setdiff :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "setdiff(M,a,b,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> x \<in> a \<and> x \<notin> b"

definition
  big_union :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "big_union(M,A,z) \<equiv> \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>y[M]. y\<in>A \<and> x \<in> y)"

definition
  big_inter :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "big_inter(M,A,z) \<equiv>
             (A=0 \<longrightarrow> z=0) \<and>
             (A\<noteq>0 \<longrightarrow> (\<forall>x[M]. x \<in> z \<longleftrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow> x \<in> y)))"

definition
  cartprod :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "cartprod(M,A,B,z) \<equiv>
        \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> (\<exists>y[M]. y\<in>B \<and> pair(M,x,y,u)))"

definition
  is_sum :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "is_sum(M,A,B,Z) \<equiv>
       \<exists>A0[M]. \<exists>n1[M]. \<exists>s1[M]. \<exists>B1[M].
       number1(M,n1) \<and> cartprod(M,n1,A,A0) \<and> upair(M,n1,n1,s1) \<and>
       cartprod(M,s1,B,B1) \<and> union(M,A0,B1,Z)"

definition
  is_Inl :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "is_Inl(M,a,z) \<equiv> \<exists>zero[M]. empty(M,zero) \<and> pair(M,zero,a,z)"

definition
  is_Inr :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "is_Inr(M,a,z) \<equiv> \<exists>n1[M]. number1(M,n1) \<and> pair(M,n1,a,z)"

definition
  is_converse :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "is_converse(M,r,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow>
             (\<exists>w[M]. w\<in>r \<and> (\<exists>u[M]. \<exists>v[M]. pair(M,u,v,w) \<and> pair(M,v,u,x)))"

definition
  pre_image :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "pre_image(M,r,A,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>y[M]. y\<in>A \<and> pair(M,x,y,w)))"

definition
  is_domain :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "is_domain(M,r,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>y[M]. pair(M,x,y,w)))"

definition
  image :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "image(M,r,A,z) \<equiv>
        \<forall>y[M]. y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>x[M]. x\<in>A \<and> pair(M,x,y,w)))"

definition
  is_range :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    \<comment> \<open>the cleaner
      \<^term>\<open>\<exists>r'[M]. is_converse(M,r,r') \<and> is_domain(M,r',z)\<close>
      unfortunately needs an instance of separation in order to prove
        \<^term>\<open>M(converse(r))\<close>.\<close>
    "is_range(M,r,z) \<equiv>
        \<forall>y[M]. y \<in> z \<longleftrightarrow> (\<exists>w[M]. w\<in>r \<and> (\<exists>x[M]. pair(M,x,y,w)))"

definition
  is_field :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "is_field(M,r,z) \<equiv>
        \<exists>dr[M]. \<exists>rr[M]. is_domain(M,r,dr) \<and> is_range(M,r,rr) \<and>
                        union(M,dr,rr,z)"

definition
  is_relation :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_relation(M,r) \<equiv>
        (\<forall>z[M]. z\<in>r \<longrightarrow> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,z)))"

definition
  is_function :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_function(M,r) \<equiv>
        \<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M].
           pair(M,x,y,p) \<longrightarrow> pair(M,x,y',p') \<longrightarrow> p\<in>r \<longrightarrow> p'\<in>r \<longrightarrow> y=y'"

definition
  fun_apply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "fun_apply(M,f,x,y) \<equiv>
        (\<exists>xs[M]. \<exists>fxs[M].
         upair(M,x,x,xs) \<and> image(M,f,xs,fxs) \<and> big_union(M,fxs,y))"

definition
  typed_function :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "typed_function(M,A,B,r) \<equiv>
        is_function(M,r) \<and> is_relation(M,r) \<and> is_domain(M,r,A) \<and>
        (\<forall>u[M]. u\<in>r \<longrightarrow> (\<forall>x[M]. \<forall>y[M]. pair(M,x,y,u) \<longrightarrow> y\<in>B))"

definition
  is_funspace :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "is_funspace(M,A,B,F) \<equiv>
        \<forall>f[M]. f \<in> F \<longleftrightarrow> typed_function(M,A,B,f)"

definition
  composition :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "composition(M,r,s,t) \<equiv>
        \<forall>p[M]. p \<in> t \<longleftrightarrow>
               (\<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                pair(M,x,z,p) \<and> pair(M,x,y,xy) \<and> pair(M,y,z,yz) \<and>
                xy \<in> s \<and> yz \<in> r)"

definition
  injection :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "injection(M,A,B,f) \<equiv>
        typed_function(M,A,B,f) \<and>
        (\<forall>x[M]. \<forall>x'[M]. \<forall>y[M]. \<forall>p[M]. \<forall>p'[M].
          pair(M,x,y,p) \<longrightarrow> pair(M,x',y,p') \<longrightarrow> p\<in>f \<longrightarrow> p'\<in>f \<longrightarrow> x=x')"

definition
  surjection :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "surjection(M,A,B,f) \<equiv>
        typed_function(M,A,B,f) \<and>
        (\<forall>y[M]. y\<in>B \<longrightarrow> (\<exists>x[M]. x\<in>A \<and> fun_apply(M,f,x,y)))"

definition
  bijection :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "bijection(M,A,B,f) \<equiv> injection(M,A,B,f) \<and> surjection(M,A,B,f)"

definition
  restriction :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    "restriction(M,r,A,z) \<equiv>
        \<forall>x[M]. x \<in> z \<longleftrightarrow> (x \<in> r \<and> (\<exists>u[M]. u\<in>A \<and> (\<exists>v[M]. pair(M,u,v,x))))"

definition
  transitive_set :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "transitive_set(M,a) \<equiv> \<forall>x[M]. x\<in>a \<longrightarrow> subset(M,x,a)"

definition
  ordinal :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
     \<comment> \<open>an ordinal is a transitive set of transitive sets\<close>
    "ordinal(M,a) \<equiv> transitive_set(M,a) \<and> (\<forall>x[M]. x\<in>a \<longrightarrow> transitive_set(M,x))"

definition
  limit_ordinal :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    \<comment> \<open>a limit ordinal is a non-empty, successor-closed ordinal\<close>
    "limit_ordinal(M,a) \<equiv>
        ordinal(M,a) \<and> \<not> empty(M,a) \<and>
        (\<forall>x[M]. x\<in>a \<longrightarrow> (\<exists>y[M]. y\<in>a \<and> successor(M,x,y)))"

definition
  successor_ordinal :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    \<comment> \<open>a successor ordinal is any ordinal that is neither empty nor limit\<close>
    "successor_ordinal(M,a) \<equiv>
        ordinal(M,a) \<and> \<not> empty(M,a) \<and> \<not> limit_ordinal(M,a)"

definition
  finite_ordinal :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    \<comment> \<open>an ordinal is finite if neither it nor any of its elements are limit\<close>
    "finite_ordinal(M,a) \<equiv>
        ordinal(M,a) \<and> \<not> limit_ordinal(M,a) \<and>
        (\<forall>x[M]. x\<in>a \<longrightarrow> \<not> limit_ordinal(M,x))"

definition
  omega :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    \<comment> \<open>omega is a limit ordinal none of whose elements are limit\<close>
    "omega(M,a) \<equiv> limit_ordinal(M,a) \<and> (\<forall>x[M]. x\<in>a \<longrightarrow> \<not> limit_ordinal(M,x))"

definition
  is_quasinat :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_quasinat(M,z) \<equiv> empty(M,z) \<or> (\<exists>m[M]. successor(M,m,z))"

definition
  is_nat_case :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o, i, i] \<Rightarrow> o" where
    "is_nat_case(M, a, is_b, k, z) \<equiv>
       (empty(M,k) \<longrightarrow> z=a) \<and>
       (\<forall>m[M]. successor(M,m,k) \<longrightarrow> is_b(m,z)) \<and>
       (is_quasinat(M,k) \<or> empty(M,z))"

definition
  relation1 :: "[i\<Rightarrow>o, [i,i]\<Rightarrow>o, i\<Rightarrow>i] \<Rightarrow> o" where
    "relation1(M,is_f,f) \<equiv> \<forall>x[M]. \<forall>y[M]. is_f(x,y) \<longleftrightarrow> y = f(x)"

definition
  Relation1 :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o, i\<Rightarrow>i] \<Rightarrow> o" where
    \<comment> \<open>as above, but typed\<close>
    "Relation1(M,A,is_f,f) \<equiv>
        \<forall>x[M]. \<forall>y[M]. x\<in>A \<longrightarrow> is_f(x,y) \<longleftrightarrow> y = f(x)"

definition
  relation2 :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, [i,i]\<Rightarrow>i] \<Rightarrow> o" where
    "relation2(M,is_f,f) \<equiv> \<forall>x[M]. \<forall>y[M]. \<forall>z[M]. is_f(x,y,z) \<longleftrightarrow> z = f(x,y)"

definition
  Relation2 :: "[i\<Rightarrow>o, i, i, [i,i,i]\<Rightarrow>o, [i,i]\<Rightarrow>i] \<Rightarrow> o" where
    "Relation2(M,A,B,is_f,f) \<equiv>
        \<forall>x[M]. \<forall>y[M]. \<forall>z[M]. x\<in>A \<longrightarrow> y\<in>B \<longrightarrow> is_f(x,y,z) \<longleftrightarrow> z = f(x,y)"

definition
  relation3 :: "[i\<Rightarrow>o, [i,i,i,i]\<Rightarrow>o, [i,i,i]\<Rightarrow>i] \<Rightarrow> o" where
    "relation3(M,is_f,f) \<equiv>
       \<forall>x[M]. \<forall>y[M]. \<forall>z[M]. \<forall>u[M]. is_f(x,y,z,u) \<longleftrightarrow> u = f(x,y,z)"

definition
  Relation3 :: "[i\<Rightarrow>o, i, i, i, [i,i,i,i]\<Rightarrow>o, [i,i,i]\<Rightarrow>i] \<Rightarrow> o" where
    "Relation3(M,A,B,C,is_f,f) \<equiv>
       \<forall>x[M]. \<forall>y[M]. \<forall>z[M]. \<forall>u[M].
         x\<in>A \<longrightarrow> y\<in>B \<longrightarrow> z\<in>C \<longrightarrow> is_f(x,y,z,u) \<longleftrightarrow> u = f(x,y,z)"

definition
  relation4 :: "[i\<Rightarrow>o, [i,i,i,i,i]\<Rightarrow>o, [i,i,i,i]\<Rightarrow>i] \<Rightarrow> o" where
    "relation4(M,is_f,f) \<equiv>
       \<forall>u[M]. \<forall>x[M]. \<forall>y[M]. \<forall>z[M]. \<forall>a[M]. is_f(u,x,y,z,a) \<longleftrightarrow> a = f(u,x,y,z)"


text\<open>Useful when absoluteness reasoning has replaced the predicates by terms\<close>
lemma triv_Relation1:
     "Relation1(M, A, \<lambda>x y. y = f(x), f)"
by (simp add: Relation1_def)

lemma triv_Relation2:
     "Relation2(M, A, B, \<lambda>x y a. a = f(x,y), f)"
by (simp add: Relation2_def)


subsection \<open>The relativized ZF axioms\<close>

definition
  extensionality :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "extensionality(M) \<equiv>
        \<forall>x[M]. \<forall>y[M]. (\<forall>z[M]. z \<in> x \<longleftrightarrow> z \<in> y) \<longrightarrow> x=y"

definition
  separation :: "[i\<Rightarrow>o, i\<Rightarrow>o] \<Rightarrow> o" where
    \<comment> \<open>The formula \<open>P\<close> should only involve parameters
        belonging to \<open>M\<close> and all its quantifiers must be relativized
        to \<open>M\<close>.  We do not have separation as a scheme; every instance
        that we need must be assumed (and later proved) separately.\<close>
    "separation(M,P) \<equiv>
        \<forall>z[M]. \<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x)"

definition
  upair_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "upair_ax(M) \<equiv> \<forall>x[M]. \<forall>y[M]. \<exists>z[M]. upair(M,x,y,z)"

definition
  Union_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "Union_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. big_union(M,x,z)"

definition
  power_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "power_ax(M) \<equiv> \<forall>x[M]. \<exists>z[M]. powerset(M,x,z)"

definition
  univalent :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o] \<Rightarrow> o" where
    "univalent(M,A,P) \<equiv>
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. \<forall>z[M]. P(x,y) \<and> P(x,z) \<longrightarrow> y=z)"

definition
  replacement :: "[i\<Rightarrow>o, [i,i]\<Rightarrow>o] \<Rightarrow> o" where
    "replacement(M,P) \<equiv>
      \<forall>A[M]. univalent(M,A,P) \<longrightarrow>
      (\<exists>Y[M]. \<forall>b[M]. (\<exists>x[M]. x\<in>A \<and> P(x,b)) \<longrightarrow> b \<in> Y)"

definition
  strong_replacement :: "[i\<Rightarrow>o, [i,i]\<Rightarrow>o] \<Rightarrow> o" where
    "strong_replacement(M,P) \<equiv>
      \<forall>A[M]. univalent(M,A,P) \<longrightarrow>
      (\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> P(x,b)))"

definition
  foundation_ax :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "foundation_ax(M) \<equiv>
        \<forall>x[M]. (\<exists>y[M]. y\<in>x) \<longrightarrow> (\<exists>y[M]. y\<in>x \<and> \<not>(\<exists>z[M]. z\<in>x \<and> z \<in> y))"


subsection\<open>A trivial consistency proof for $V_\omega$\<close>

text\<open>We prove that $V_\omega$
      (or \<open>univ\<close> in Isabelle) satisfies some ZF axioms.
     Kunen, Theorem IV 3.13, page 123.\<close>

lemma univ0_downwards_mem: "\<lbrakk>y \<in> x; x \<in> univ(0)\<rbrakk> \<Longrightarrow> y \<in> univ(0)"
apply (insert Transset_univ [OF Transset_0])
apply (simp add: Transset_def, blast)
done

lemma univ0_Ball_abs [simp]:
     "A \<in> univ(0) \<Longrightarrow> (\<forall>x\<in>A. x \<in> univ(0) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x\<in>A. P(x))"
by (blast intro: univ0_downwards_mem)

lemma univ0_Bex_abs [simp]:
     "A \<in> univ(0) \<Longrightarrow> (\<exists>x\<in>A. x \<in> univ(0) \<and> P(x)) \<longleftrightarrow> (\<exists>x\<in>A. P(x))"
by (blast intro: univ0_downwards_mem)

text\<open>Congruence rule for separation: can assume the variable is in \<open>M\<close>\<close>
lemma separation_cong [cong]:
     "(\<And>x. M(x) \<Longrightarrow> P(x) \<longleftrightarrow> P'(x))
      \<Longrightarrow> separation(M, \<lambda>x. P(x)) \<longleftrightarrow> separation(M, \<lambda>x. P'(x))"
by (simp add: separation_def)

lemma univalent_cong [cong]:
     "\<lbrakk>A=A'; \<And>x y. \<lbrakk>x\<in>A; M(x); M(y)\<rbrakk> \<Longrightarrow> P(x,y) \<longleftrightarrow> P'(x,y)\<rbrakk>
      \<Longrightarrow> univalent(M, A, \<lambda>x y. P(x,y)) \<longleftrightarrow> univalent(M, A', \<lambda>x y. P'(x,y))"
by (simp add: univalent_def)

lemma univalent_triv [intro,simp]:
     "univalent(M, A, \<lambda>x y. y = f(x))"
by (simp add: univalent_def)

lemma univalent_conjI2 [intro,simp]:
     "univalent(M,A,Q) \<Longrightarrow> univalent(M, A, \<lambda>x y. P(x,y) \<and> Q(x,y))"
by (simp add: univalent_def, blast)

text\<open>Congruence rule for replacement\<close>
lemma strong_replacement_cong [cong]:
     "\<lbrakk>\<And>x y. \<lbrakk>M(x); M(y)\<rbrakk> \<Longrightarrow> P(x,y) \<longleftrightarrow> P'(x,y)\<rbrakk>
      \<Longrightarrow> strong_replacement(M, \<lambda>x y. P(x,y)) \<longleftrightarrow>
          strong_replacement(M, \<lambda>x y. P'(x,y))"
by (simp add: strong_replacement_def)

text\<open>The extensionality axiom\<close>
lemma "extensionality(\<lambda>x. x \<in> univ(0))"
apply (simp add: extensionality_def)
apply (blast intro: univ0_downwards_mem)
done

text\<open>The separation axiom requires some lemmas\<close>
lemma Collect_in_Vfrom:
     "\<lbrakk>X \<in> Vfrom(A,j);  Transset(A)\<rbrakk> \<Longrightarrow> Collect(X,P) \<in> Vfrom(A, succ(j))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def, blast)
done

lemma Collect_in_VLimit:
     "\<lbrakk>X \<in> Vfrom(A,i);  Limit(i);  Transset(A)\<rbrakk>
      \<Longrightarrow> Collect(X,P) \<in> Vfrom(A,i)"
apply (rule Limit_VfromE, assumption+)
apply (blast intro: Limit_has_succ VfromI Collect_in_Vfrom)
done

lemma Collect_in_univ:
     "\<lbrakk>X \<in> univ(A);  Transset(A)\<rbrakk> \<Longrightarrow> Collect(X,P) \<in> univ(A)"
by (simp add: univ_def Collect_in_VLimit)

lemma "separation(\<lambda>x. x \<in> univ(0), P)"
apply (simp add: separation_def, clarify)
apply (rule_tac x = "Collect(z,P)" in bexI)
apply (blast intro: Collect_in_univ Transset_0)+
done

text\<open>Unordered pairing axiom\<close>
lemma "upair_ax(\<lambda>x. x \<in> univ(0))"
apply (simp add: upair_ax_def upair_def)
apply (blast intro: doubleton_in_univ)
done

text\<open>Union axiom\<close>
lemma "Union_ax(\<lambda>x. x \<in> univ(0))"
apply (simp add: Union_ax_def big_union_def, clarify)
apply (rule_tac x="\<Union>x" in bexI)
 apply (blast intro: univ0_downwards_mem)
apply (blast intro: Union_in_univ Transset_0)
done

text\<open>Powerset axiom\<close>

lemma Pow_in_univ:
     "\<lbrakk>X \<in> univ(A);  Transset(A)\<rbrakk> \<Longrightarrow> Pow(X) \<in> univ(A)"
apply (simp add: univ_def Pow_in_VLimit)
done

lemma "power_ax(\<lambda>x. x \<in> univ(0))"
apply (simp add: power_ax_def powerset_def subset_def, clarify)
apply (rule_tac x="Pow(x)" in bexI)
 apply (blast intro: univ0_downwards_mem)
apply (blast intro: Pow_in_univ Transset_0)
done

text\<open>Foundation axiom\<close>
lemma "foundation_ax(\<lambda>x. x \<in> univ(0))"
apply (simp add: foundation_ax_def, clarify)
apply (cut_tac A=x in foundation)
apply (blast intro: univ0_downwards_mem)
done

lemma "replacement(\<lambda>x. x \<in> univ(0), P)"
apply (simp add: replacement_def, clarify)
oops
text\<open>no idea: maybe prove by induction on the rank of A?\<close>

text\<open>Still missing: Replacement, Choice\<close>

subsection\<open>Lemmas Needed to Reduce Some Set Constructions to Instances
      of Separation\<close>

lemma image_iff_Collect: "r `` A = {y \<in> \<Union>(\<Union>(r)). \<exists>p\<in>r. \<exists>x\<in>A. p=\<langle>x,y\<rangle>}"
apply (rule equalityI, auto)
apply (simp add: Pair_def, blast)
done

lemma vimage_iff_Collect:
     "r -`` A = {x \<in> \<Union>(\<Union>(r)). \<exists>p\<in>r. \<exists>y\<in>A. p=\<langle>x,y\<rangle>}"
apply (rule equalityI, auto)
apply (simp add: Pair_def, blast)
done

text\<open>These two lemmas lets us prove \<open>domain_closed\<close> and
      \<open>range_closed\<close> without new instances of separation\<close>

lemma domain_eq_vimage: "domain(r) = r -`` Union(Union(r))"
apply (rule equalityI, auto)
apply (rule vimageI, assumption)
apply (simp add: Pair_def, blast)
done

lemma range_eq_image: "range(r) = r `` Union(Union(r))"
apply (rule equalityI, auto)
apply (rule imageI, assumption)
apply (simp add: Pair_def, blast)
done

lemma replacementD:
    "\<lbrakk>replacement(M,P); M(A);  univalent(M,A,P)\<rbrakk>
     \<Longrightarrow> \<exists>Y[M]. (\<forall>b[M]. ((\<exists>x[M]. x\<in>A \<and> P(x,b)) \<longrightarrow> b \<in> Y))"
by (simp add: replacement_def)

lemma strong_replacementD:
    "\<lbrakk>strong_replacement(M,P); M(A);  univalent(M,A,P)\<rbrakk>
     \<Longrightarrow> \<exists>Y[M]. (\<forall>b[M]. (b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> P(x,b))))"
by (simp add: strong_replacement_def)

lemma separationD:
    "\<lbrakk>separation(M,P); M(z)\<rbrakk> \<Longrightarrow> \<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> P(x)"
by (simp add: separation_def)


text\<open>More constants, for order types\<close>

definition
  order_isomorphism :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
    "order_isomorphism(M,A,r,B,s,f) \<equiv>
        bijection(M,A,B,f) \<and>
        (\<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow>
          (\<forall>p[M]. \<forall>fx[M]. \<forall>fy[M]. \<forall>q[M].
            pair(M,x,y,p) \<longrightarrow> fun_apply(M,f,x,fx) \<longrightarrow> fun_apply(M,f,y,fy) \<longrightarrow>
            pair(M,fx,fy,q) \<longrightarrow> (p\<in>r \<longleftrightarrow> q\<in>s))))"

definition
  pred_set :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
    "pred_set(M,A,x,r,B) \<equiv>
        \<forall>y[M]. y \<in> B \<longleftrightarrow> (\<exists>p[M]. p\<in>r \<and> y \<in> A \<and> pair(M,y,x,p))"

definition
  membership :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where \<comment> \<open>membership relation\<close>
    "membership(M,A,r) \<equiv>
        \<forall>p[M]. p \<in> r \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> (\<exists>y[M]. y\<in>A \<and> x\<in>y \<and> pair(M,x,y,p)))"


subsection\<open>Introducing a Transitive Class Model\<close>

text\<open>The class M is assumed to be transitive and inhabited\<close>
locale M_trans =
  fixes M
  assumes transM:   "\<lbrakk>y\<in>x; M(x)\<rbrakk> \<Longrightarrow> M(y)"
    and M_inhabited: "\<exists>x . M(x)"

lemma (in M_trans) nonempty [simp]:  "M(0)"
proof -
  have "M(x) \<longrightarrow> M(0)" for x
  proof (rule_tac P="\<lambda>w. M(w) \<longrightarrow> M(0)" in eps_induct)
    {
    fix x
    assume "\<forall>y\<in>x. M(y) \<longrightarrow> M(0)" "M(x)"
    consider (a) "\<exists>y. y\<in>x" | (b) "x=0" by auto
    then 
    have "M(x) \<longrightarrow> M(0)" 
    proof cases
      case a
      then show ?thesis using \<open>\<forall>y\<in>x._\<close> \<open>M(x)\<close> transM by auto
    next
      case b
      then show ?thesis by simp
    qed
  }
  then show "M(x) \<longrightarrow> M(0)" if "\<forall>y\<in>x. M(y) \<longrightarrow> M(0)" for x
    using that by auto
  qed
  with M_inhabited
  show "M(0)" using M_inhabited by blast
qed

text\<open>The class M is assumed to be transitive and to satisfy some
      relativized ZF axioms\<close>
locale M_trivial = M_trans +
  assumes upair_ax:         "upair_ax(M)"
      and Union_ax:         "Union_ax(M)"

lemma (in M_trans) rall_abs [simp]:
     "M(A) \<Longrightarrow> (\<forall>x[M]. x\<in>A \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x\<in>A. P(x))"
by (blast intro: transM)

lemma (in M_trans) rex_abs [simp]:
     "M(A) \<Longrightarrow> (\<exists>x[M]. x\<in>A \<and> P(x)) \<longleftrightarrow> (\<exists>x\<in>A. P(x))"
by (blast intro: transM)

lemma (in M_trans) ball_iff_equiv:
     "M(A) \<Longrightarrow> (\<forall>x[M]. (x\<in>A \<longleftrightarrow> P(x))) \<longleftrightarrow>
               (\<forall>x\<in>A. P(x)) \<and> (\<forall>x. P(x) \<longrightarrow> M(x) \<longrightarrow> x\<in>A)"
by (blast intro: transM)

text\<open>Simplifies proofs of equalities when there's an iff-equality
      available for rewriting, universally quantified over M.
      But it's not the only way to prove such equalities: its
      premises \<^term>\<open>M(A)\<close> and  \<^term>\<open>M(B)\<close> can be too strong.\<close>
lemma (in M_trans) M_equalityI:
     "\<lbrakk>\<And>x. M(x) \<Longrightarrow> x\<in>A \<longleftrightarrow> x\<in>B; M(A); M(B)\<rbrakk> \<Longrightarrow> A=B"
by (blast dest: transM)


subsubsection\<open>Trivial Absoluteness Proofs: Empty Set, Pairs, etc.\<close>

lemma (in M_trans) empty_abs [simp]:
     "M(z) \<Longrightarrow> empty(M,z) \<longleftrightarrow> z=0"
apply (simp add: empty_def)
apply (blast intro: transM)
done

lemma (in M_trans) subset_abs [simp]:
     "M(A) \<Longrightarrow> subset(M,A,B) \<longleftrightarrow> A \<subseteq> B"
apply (simp add: subset_def)
apply (blast intro: transM)
done

lemma (in M_trans) upair_abs [simp]:
     "M(z) \<Longrightarrow> upair(M,a,b,z) \<longleftrightarrow> z={a,b}"
apply (simp add: upair_def)
apply (blast intro: transM)
done

lemma (in M_trivial) upair_in_MI [intro!]:
     " M(a) \<and> M(b) \<Longrightarrow> M({a,b})"
by (insert upair_ax, simp add: upair_ax_def)

lemma (in M_trans) upair_in_MD [dest!]:
     "M({a,b}) \<Longrightarrow> M(a) \<and> M(b)"
  by (blast intro: transM)

lemma (in M_trivial) upair_in_M_iff [simp]:
  "M({a,b}) \<longleftrightarrow> M(a) \<and> M(b)"
  by blast

lemma (in M_trivial) singleton_in_MI [intro!]:
     "M(a) \<Longrightarrow> M({a})"
  by (insert upair_in_M_iff [of a a], simp)

lemma (in M_trans) singleton_in_MD [dest!]:
     "M({a}) \<Longrightarrow> M(a)"
  by (insert upair_in_MD [of a a], simp)

lemma (in M_trivial) singleton_in_M_iff [simp]:
     "M({a}) \<longleftrightarrow> M(a)"
  by blast

lemma (in M_trans) pair_abs [simp]:
     "M(z) \<Longrightarrow> pair(M,a,b,z) \<longleftrightarrow> z=\<langle>a,b\<rangle>"
apply (simp add: pair_def Pair_def)
apply (blast intro: transM)
done

lemma (in M_trans) pair_in_MD [dest!]:
     "M(\<langle>a,b\<rangle>) \<Longrightarrow> M(a) \<and> M(b)"
  by (simp add: Pair_def, blast intro: transM)

lemma (in M_trivial) pair_in_MI [intro!]:
     "M(a) \<and> M(b) \<Longrightarrow> M(\<langle>a,b\<rangle>)"
  by (simp add: Pair_def)

lemma (in M_trivial) pair_in_M_iff [simp]:
     "M(\<langle>a,b\<rangle>) \<longleftrightarrow> M(a) \<and> M(b)"
  by blast

lemma (in M_trans) pair_components_in_M:
     "\<lbrakk>\<langle>x,y\<rangle> \<in> A; M(A)\<rbrakk> \<Longrightarrow> M(x) \<and> M(y)"
  by (blast dest: transM)

lemma (in M_trivial) cartprod_abs [simp]:
     "\<lbrakk>M(A); M(B); M(z)\<rbrakk> \<Longrightarrow> cartprod(M,A,B,z) \<longleftrightarrow> z = A*B"
apply (simp add: cartprod_def)
apply (rule iffI)
 apply (blast intro!: equalityI intro: transM dest!: rspec)
apply (blast dest: transM)
done

subsubsection\<open>Absoluteness for Unions and Intersections\<close>

lemma (in M_trans) union_abs [simp]:
     "\<lbrakk>M(a); M(b); M(z)\<rbrakk> \<Longrightarrow> union(M,a,b,z) \<longleftrightarrow> z = a \<union> b"
  unfolding union_def
  by (blast intro: transM )

lemma (in M_trans) inter_abs [simp]:
     "\<lbrakk>M(a); M(b); M(z)\<rbrakk> \<Longrightarrow> inter(M,a,b,z) \<longleftrightarrow> z = a \<inter> b"
  unfolding inter_def
  by (blast intro: transM)

lemma (in M_trans) setdiff_abs [simp]:
     "\<lbrakk>M(a); M(b); M(z)\<rbrakk> \<Longrightarrow> setdiff(M,a,b,z) \<longleftrightarrow> z = a-b"
  unfolding setdiff_def
  by (blast intro: transM)

lemma (in M_trans) Union_abs [simp]:
     "\<lbrakk>M(A); M(z)\<rbrakk> \<Longrightarrow> big_union(M,A,z) \<longleftrightarrow> z = \<Union>(A)"
  unfolding big_union_def
  by (blast  dest: transM)

lemma (in M_trivial) Union_closed [intro,simp]:
     "M(A) \<Longrightarrow> M(\<Union>(A))"
by (insert Union_ax, simp add: Union_ax_def)

lemma (in M_trivial) Un_closed [intro,simp]:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> M(A \<union> B)"
by (simp only: Un_eq_Union, blast)

lemma (in M_trivial) cons_closed [intro,simp]:
     "\<lbrakk>M(a); M(A)\<rbrakk> \<Longrightarrow> M(cons(a,A))"
by (subst cons_eq [symmetric], blast)

lemma (in M_trivial) cons_abs [simp]:
     "\<lbrakk>M(b); M(z)\<rbrakk> \<Longrightarrow> is_cons(M,a,b,z) \<longleftrightarrow> z = cons(a,b)"
by (simp add: is_cons_def, blast intro: transM)

lemma (in M_trivial) successor_abs [simp]:
     "\<lbrakk>M(a); M(z)\<rbrakk> \<Longrightarrow> successor(M,a,z) \<longleftrightarrow> z = succ(a)"
by (simp add: successor_def, blast)

lemma (in M_trans) succ_in_MD [dest!]:
     "M(succ(a)) \<Longrightarrow> M(a)"
  unfolding succ_def
  by (blast intro: transM)

lemma (in M_trivial) succ_in_MI [intro!]:
     "M(a) \<Longrightarrow> M(succ(a))"
  unfolding succ_def
  by (blast intro: transM)

lemma (in M_trivial) succ_in_M_iff [simp]:
     "M(succ(a)) \<longleftrightarrow> M(a)"
  by blast

subsubsection\<open>Absoluteness for Separation and Replacement\<close>

lemma (in M_trans) separation_closed [intro,simp]:
     "\<lbrakk>separation(M,P); M(A)\<rbrakk> \<Longrightarrow> M(Collect(A,P))"
apply (insert separation, simp add: separation_def)
apply (drule rspec, assumption, clarify)
apply (subgoal_tac "y = Collect(A,P)", blast)
apply (blast dest: transM)
done

lemma separation_iff:
     "separation(M,P) \<longleftrightarrow> (\<forall>z[M]. \<exists>y[M]. is_Collect(M,z,P,y))"
by (simp add: separation_def is_Collect_def)

lemma (in M_trans) Collect_abs [simp]:
     "\<lbrakk>M(A); M(z)\<rbrakk> \<Longrightarrow> is_Collect(M,A,P,z) \<longleftrightarrow> z = Collect(A,P)"
  unfolding is_Collect_def
  by (blast dest: transM)

subsubsection\<open>The Operator \<^term>\<open>is_Replace\<close>\<close>


lemma is_Replace_cong [cong]:
     "\<lbrakk>A=A';
         \<And>x y. \<lbrakk>M(x); M(y)\<rbrakk> \<Longrightarrow> P(x,y) \<longleftrightarrow> P'(x,y);
         z=z'\<rbrakk>
      \<Longrightarrow> is_Replace(M, A, \<lambda>x y. P(x,y), z) \<longleftrightarrow>
          is_Replace(M, A', \<lambda>x y. P'(x,y), z')"
by (simp add: is_Replace_def)

lemma (in M_trans) univalent_Replace_iff:
     "\<lbrakk>M(A); univalent(M,A,P);
         \<And>x y. \<lbrakk>x\<in>A; P(x,y)\<rbrakk> \<Longrightarrow> M(y)\<rbrakk>
      \<Longrightarrow> u \<in> Replace(A,P) \<longleftrightarrow> (\<exists>x. x\<in>A \<and> P(x,u))"
  unfolding Replace_iff univalent_def
  by (blast dest: transM)

(*The last premise expresses that P takes M to M*)
lemma (in M_trans) strong_replacement_closed [intro,simp]:
     "\<lbrakk>strong_replacement(M,P); M(A); univalent(M,A,P);
         \<And>x y. \<lbrakk>x\<in>A; P(x,y)\<rbrakk> \<Longrightarrow> M(y)\<rbrakk> \<Longrightarrow> M(Replace(A,P))"
apply (simp add: strong_replacement_def)
apply (drule_tac x=A in rspec, safe)
apply (subgoal_tac "Replace(A,P) = Y")
 apply simp
apply (rule equality_iffI)
apply (simp add: univalent_Replace_iff)
apply (blast dest: transM)
done

lemma (in M_trans) Replace_abs:
     "\<lbrakk>M(A); M(z); univalent(M,A,P);
         \<And>x y. \<lbrakk>x\<in>A; P(x,y)\<rbrakk> \<Longrightarrow> M(y)\<rbrakk>
      \<Longrightarrow> is_Replace(M,A,P,z) \<longleftrightarrow> z = Replace(A,P)"
apply (simp add: is_Replace_def)
apply (rule iffI)
 apply (rule equality_iffI)
 apply (simp_all add: univalent_Replace_iff)
 apply (blast dest: transM)+
done


(*The first premise can't simply be assumed as a schema.
  It is essential to take care when asserting instances of Replacement.
  Let K be a nonconstructible subset of nat and define
  f(x) = x if x \<in> K and f(x)=0 otherwise.  Then RepFun(nat,f) = cons(0,K), a
  nonconstructible set.  So we cannot assume that M(X) implies M(RepFun(X,f))
  even for f \<in> M -> M.
*)
lemma (in M_trans) RepFun_closed:
     "\<lbrakk>strong_replacement(M, \<lambda>x y. y = f(x)); M(A); \<forall>x\<in>A. M(f(x))\<rbrakk>
      \<Longrightarrow> M(RepFun(A,f))"
apply (simp add: RepFun_def)
done

lemma Replace_conj_eq: "{y . x \<in> A, x\<in>A \<and> y=f(x)} = {y . x\<in>A, y=f(x)}"
by simp

text\<open>Better than \<open>RepFun_closed\<close> when having the formula \<^term>\<open>x\<in>A\<close>
      makes relativization easier.\<close>
lemma (in M_trans) RepFun_closed2:
     "\<lbrakk>strong_replacement(M, \<lambda>x y. x\<in>A \<and> y = f(x)); M(A); \<forall>x\<in>A. M(f(x))\<rbrakk>
      \<Longrightarrow> M(RepFun(A, \<lambda>x. f(x)))"
apply (simp add: RepFun_def)
apply (frule strong_replacement_closed, assumption)
apply (auto dest: transM  simp add: Replace_conj_eq univalent_def)
done

subsubsection \<open>Absoluteness for \<^term>\<open>Lambda\<close>\<close>

definition
 is_lambda :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o, i] \<Rightarrow> o" where
    "is_lambda(M, A, is_b, z) \<equiv>
       \<forall>p[M]. p \<in> z \<longleftrightarrow>
        (\<exists>u[M]. \<exists>v[M]. u\<in>A \<and> pair(M,u,v,p) \<and> is_b(u,v))"

lemma (in M_trivial) lam_closed:
     "\<lbrakk>strong_replacement(M, \<lambda>x y. y = <x,b(x)>); M(A); \<forall>x\<in>A. M(b(x))\<rbrakk>
      \<Longrightarrow> M(\<lambda>x\<in>A. b(x))"
by (simp add: lam_def, blast intro: RepFun_closed dest: transM)

text\<open>Better than \<open>lam_closed\<close>: has the formula \<^term>\<open>x\<in>A\<close>\<close>
lemma (in M_trivial) lam_closed2:
  "\<lbrakk>strong_replacement(M, \<lambda>x y. x\<in>A \<and> y = \<langle>x, b(x)\<rangle>);
     M(A); \<forall>m[M]. m\<in>A \<longrightarrow> M(b(m))\<rbrakk> \<Longrightarrow> M(Lambda(A,b))"
apply (simp add: lam_def)
apply (blast intro: RepFun_closed2 dest: transM)
done

lemma (in M_trivial) lambda_abs2:
     "\<lbrakk>Relation1(M,A,is_b,b); M(A); \<forall>m[M]. m\<in>A \<longrightarrow> M(b(m)); M(z)\<rbrakk>
      \<Longrightarrow> is_lambda(M,A,is_b,z) \<longleftrightarrow> z = Lambda(A,b)"
apply (simp add: Relation1_def is_lambda_def)
apply (rule iffI)
 prefer 2 apply (simp add: lam_def)
apply (rule equality_iffI)
apply (simp add: lam_def)
apply (rule iffI)
 apply (blast dest: transM)
apply (auto simp add: transM [of _ A])
done

lemma is_lambda_cong [cong]:
     "\<lbrakk>A=A';  z=z';
         \<And>x y. \<lbrakk>x\<in>A; M(x); M(y)\<rbrakk> \<Longrightarrow> is_b(x,y) \<longleftrightarrow> is_b'(x,y)\<rbrakk>
      \<Longrightarrow> is_lambda(M, A, \<lambda>x y. is_b(x,y), z) \<longleftrightarrow>
          is_lambda(M, A', \<lambda>x y. is_b'(x,y), z')"
by (simp add: is_lambda_def)

lemma (in M_trans) image_abs [simp]:
     "\<lbrakk>M(r); M(A); M(z)\<rbrakk> \<Longrightarrow> image(M,r,A,z) \<longleftrightarrow> z = r``A"
apply (simp add: image_def)
apply (rule iffI)
 apply (blast intro!: equalityI dest: transM, blast)
done

subsubsection\<open>Relativization of Powerset\<close>

text\<open>What about \<open>Pow_abs\<close>?  Powerset is NOT absolute!
      This result is one direction of absoluteness.\<close>

lemma (in M_trans) powerset_Pow:
     "powerset(M, x, Pow(x))"
by (simp add: powerset_def)

text\<open>But we can't prove that the powerset in \<open>M\<close> includes the
      real powerset.\<close>

lemma (in M_trans) powerset_imp_subset_Pow:
     "\<lbrakk>powerset(M,x,y); M(y)\<rbrakk> \<Longrightarrow> y \<subseteq> Pow(x)"
apply (simp add: powerset_def)
apply (blast dest: transM)
done

lemma (in M_trans) powerset_abs:
  assumes
     "M(y)"
  shows
    "powerset(M,x,y) \<longleftrightarrow> y = {a\<in>Pow(x) . M(a)}"
proof (intro iffI equalityI)
  (* First show the converse implication by double inclusion *)
  assume "powerset(M,x,y)"
  with \<open>M(y)\<close>  
  show "y \<subseteq> {a\<in>Pow(x) . M(a)}"
    using powerset_imp_subset_Pow transM by blast
  from \<open>powerset(M,x,y)\<close>
  show "{a\<in>Pow(x) . M(a)} \<subseteq> y"
    using transM unfolding powerset_def by auto
next (* we show the direct implication *)
  assume
    "y = {a \<in> Pow(x) . M(a)}"
  then
  show "powerset(M, x, y)"
    unfolding powerset_def subset_def using transM by blast
qed

subsubsection\<open>Absoluteness for the Natural Numbers\<close>

lemma (in M_trivial) nat_into_M [intro]:
     "n \<in> nat \<Longrightarrow> M(n)"
by (induct n rule: nat_induct, simp_all)

lemma (in M_trans) nat_case_closed [intro,simp]:
  "\<lbrakk>M(k); M(a); \<forall>m[M]. M(b(m))\<rbrakk> \<Longrightarrow> M(nat_case(a,b,k))"
apply (case_tac "k=0", simp)
apply (case_tac "\<exists>m. k = succ(m)", force)
apply (simp add: nat_case_def)
done

lemma (in M_trivial) quasinat_abs [simp]:
     "M(z) \<Longrightarrow> is_quasinat(M,z) \<longleftrightarrow> quasinat(z)"
by (auto simp add: is_quasinat_def quasinat_def)

lemma (in M_trivial) nat_case_abs [simp]:
     "\<lbrakk>relation1(M,is_b,b); M(k); M(z)\<rbrakk>
      \<Longrightarrow> is_nat_case(M,a,is_b,k,z) \<longleftrightarrow> z = nat_case(a,b,k)"
apply (case_tac "quasinat(k)")
 prefer 2
 apply (simp add: is_nat_case_def non_nat_case)
 apply (force simp add: quasinat_def)
apply (simp add: quasinat_def is_nat_case_def)
apply (elim disjE exE)
 apply (simp_all add: relation1_def)
done

(*NOT for the simplifier.  The assumption M(z') is apparently necessary, but
  causes the error "Failed congruence proof!"  It may be better to replace
  is_nat_case by nat_case before attempting congruence reasoning.*)
lemma is_nat_case_cong:
     "\<lbrakk>a = a'; k = k';  z = z';  M(z');
       \<And>x y. \<lbrakk>M(x); M(y)\<rbrakk> \<Longrightarrow> is_b(x,y) \<longleftrightarrow> is_b'(x,y)\<rbrakk>
      \<Longrightarrow> is_nat_case(M, a, is_b, k, z) \<longleftrightarrow> is_nat_case(M, a', is_b', k', z')"
by (simp add: is_nat_case_def)


subsection\<open>Absoluteness for Ordinals\<close>
text\<open>These results constitute Theorem IV 5.1 of Kunen (page 126).\<close>

lemma (in M_trans) lt_closed:
     "\<lbrakk>j<i; M(i)\<rbrakk> \<Longrightarrow> M(j)"
by (blast dest: ltD intro: transM)

lemma (in M_trans) transitive_set_abs [simp]:
     "M(a) \<Longrightarrow> transitive_set(M,a) \<longleftrightarrow> Transset(a)"
by (simp add: transitive_set_def Transset_def)

lemma (in M_trans) ordinal_abs [simp]:
     "M(a) \<Longrightarrow> ordinal(M,a) \<longleftrightarrow> Ord(a)"
by (simp add: ordinal_def Ord_def)

lemma (in M_trivial) limit_ordinal_abs [simp]:
     "M(a) \<Longrightarrow> limit_ordinal(M,a) \<longleftrightarrow> Limit(a)"
apply (unfold Limit_def limit_ordinal_def)
apply (simp add: Ord_0_lt_iff)
apply (simp add: lt_def, blast)
done

lemma (in M_trivial) successor_ordinal_abs [simp]:
     "M(a) \<Longrightarrow> successor_ordinal(M,a) \<longleftrightarrow> Ord(a) \<and> (\<exists>b[M]. a = succ(b))"
apply (simp add: successor_ordinal_def, safe)
apply (drule Ord_cases_disj, auto)
done

lemma finite_Ord_is_nat:
      "\<lbrakk>Ord(a); \<not> Limit(a); \<forall>x\<in>a. \<not> Limit(x)\<rbrakk> \<Longrightarrow> a \<in> nat"
by (induct a rule: trans_induct3, simp_all)

lemma (in M_trivial) finite_ordinal_abs [simp]:
     "M(a) \<Longrightarrow> finite_ordinal(M,a) \<longleftrightarrow> a \<in> nat"
apply (simp add: finite_ordinal_def)
apply (blast intro: finite_Ord_is_nat intro: nat_into_Ord
             dest: Ord_trans naturals_not_limit)
done

lemma Limit_non_Limit_implies_nat:
     "\<lbrakk>Limit(a); \<forall>x\<in>a. \<not> Limit(x)\<rbrakk> \<Longrightarrow> a = nat"
apply (rule le_anti_sym)
apply (rule all_lt_imp_le, blast, blast intro: Limit_is_Ord)
 apply (simp add: lt_def)
 apply (blast intro: Ord_in_Ord Ord_trans finite_Ord_is_nat)
apply (erule nat_le_Limit)
done

lemma (in M_trivial) omega_abs [simp]:
     "M(a) \<Longrightarrow> omega(M,a) \<longleftrightarrow> a = nat"
apply (simp add: omega_def)
apply (blast intro: Limit_non_Limit_implies_nat dest: naturals_not_limit)
done

lemma (in M_trivial) number1_abs [simp]:
     "M(a) \<Longrightarrow> number1(M,a) \<longleftrightarrow> a = 1"
by (simp add: number1_def)

lemma (in M_trivial) number2_abs [simp]:
     "M(a) \<Longrightarrow> number2(M,a) \<longleftrightarrow> a = succ(1)"
by (simp add: number2_def)

lemma (in M_trivial) number3_abs [simp]:
     "M(a) \<Longrightarrow> number3(M,a) \<longleftrightarrow> a = succ(succ(1))"
by (simp add: number3_def)

text\<open>Kunen continued to 20...\<close>

(*Could not get this to work.  The \<lambda>x\<in>nat is essential because everything
  but the recursion variable must stay unchanged.  But then the recursion
  equations only hold for x\<in>nat (or in some other set) and not for the
  whole of the class M.
  consts
    natnumber_aux :: "[i\<Rightarrow>o,i] \<Rightarrow> i"

  primrec
      "natnumber_aux(M,0) = (\<lambda>x\<in>nat. if empty(M,x) then 1 else 0)"
      "natnumber_aux(M,succ(n)) =
           (\<lambda>x\<in>nat. if (\<exists>y[M]. natnumber_aux(M,n)`y=1 \<and> successor(M,y,x))
                     then 1 else 0)"

  definition
    natnumber :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o"
      "natnumber(M,n,x) \<equiv> natnumber_aux(M,n)`x = 1"

  lemma (in M_trivial) [simp]:
       "natnumber(M,0,x) \<equiv> x=0"
*)

subsection\<open>Some instances of separation and strong replacement\<close>

locale M_basic = M_trivial +
assumes Inter_separation:
     "M(A) \<Longrightarrow> separation(M, \<lambda>x. \<forall>y[M]. y\<in>A \<longrightarrow> x\<in>y)"
  and Diff_separation:
     "M(B) \<Longrightarrow> separation(M, \<lambda>x. x \<notin> B)"
  and cartprod_separation:
     "\<lbrakk>M(A); M(B)\<rbrakk>
      \<Longrightarrow> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A \<and> (\<exists>y[M]. y\<in>B \<and> pair(M,x,y,z)))"
  and image_separation:
     "\<lbrakk>M(A); M(r)\<rbrakk>
      \<Longrightarrow> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r \<and> (\<exists>x[M]. x\<in>A \<and> pair(M,x,y,p)))"
  and converse_separation:
     "M(r) \<Longrightarrow> separation(M,
         \<lambda>z. \<exists>p[M]. p\<in>r \<and> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,p) \<and> pair(M,y,x,z)))"
  and restrict_separation:
     "M(A) \<Longrightarrow> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A \<and> (\<exists>y[M]. pair(M,x,y,z)))"
  and comp_separation:
     "\<lbrakk>M(r); M(s)\<rbrakk>
      \<Longrightarrow> separation(M, \<lambda>xz. \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M].
                  pair(M,x,z,xz) \<and> pair(M,x,y,xy) \<and> pair(M,y,z,yz) \<and>
                  xy\<in>s \<and> yz\<in>r)"
  and pred_separation:
     "\<lbrakk>M(r); M(x)\<rbrakk> \<Longrightarrow> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r \<and> pair(M,y,x,p))"
  and Memrel_separation:
     "separation(M, \<lambda>z. \<exists>x[M]. \<exists>y[M]. pair(M,x,y,z) \<and> x \<in> y)"
  and funspace_succ_replacement:
     "M(n) \<Longrightarrow>
      strong_replacement(M, \<lambda>p z. \<exists>f[M]. \<exists>b[M]. \<exists>nb[M]. \<exists>cnbf[M].
                pair(M,f,b,p) \<and> pair(M,n,b,nb) \<and> is_cons(M,nb,f,cnbf) \<and>
                upair(M,cnbf,cnbf,z))"
  and is_recfun_separation:
     \<comment> \<open>for well-founded recursion: used to prove \<open>is_recfun_equal\<close>\<close>
     "\<lbrakk>M(r); M(f); M(g); M(a); M(b)\<rbrakk>
     \<Longrightarrow> separation(M,
            \<lambda>x. \<exists>xa[M]. \<exists>xb[M].
                pair(M,x,a,xa) \<and> xa \<in> r \<and> pair(M,x,b,xb) \<and> xb \<in> r \<and>
                (\<exists>fx[M]. \<exists>gx[M]. fun_apply(M,f,x,fx) \<and> fun_apply(M,g,x,gx) \<and>
                                   fx \<noteq> gx))"
     and power_ax:         "power_ax(M)"

lemma (in M_trivial) cartprod_iff_lemma:
     "\<lbrakk>M(C);  \<forall>u[M]. u \<in> C \<longleftrightarrow> (\<exists>x\<in>A. \<exists>y\<in>B. u = {{x}, {x,y}});
         powerset(M, A \<union> B, p1); powerset(M, p1, p2);  M(p2)\<rbrakk>
       \<Longrightarrow> C = {u \<in> p2 . \<exists>x\<in>A. \<exists>y\<in>B. u = {{x}, {x,y}}}"
apply (simp add: powerset_def)
apply (rule equalityI, clarify, simp)
 apply (frule transM, assumption)
 apply (frule transM, assumption, simp (no_asm_simp))
 apply blast
apply clarify
apply (frule transM, assumption, force)
done

lemma (in M_basic) cartprod_iff:
     "\<lbrakk>M(A); M(B); M(C)\<rbrakk>
      \<Longrightarrow> cartprod(M,A,B,C) \<longleftrightarrow>
          (\<exists>p1[M]. \<exists>p2[M]. powerset(M,A \<union> B,p1) \<and> powerset(M,p1,p2) \<and>
                   C = {z \<in> p2. \<exists>x\<in>A. \<exists>y\<in>B. z = \<langle>x,y\<rangle>})"
apply (simp add: Pair_def cartprod_def, safe)
defer 1
  apply (simp add: powerset_def)
 apply blast
txt\<open>Final, difficult case: the left-to-right direction of the theorem.\<close>
apply (insert power_ax, simp add: power_ax_def)
apply (frule_tac x="A \<union> B" and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
apply (blast, clarify)
apply (drule_tac x=z and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
apply assumption
apply (blast intro: cartprod_iff_lemma)
done

lemma (in M_basic) cartprod_closed_lemma:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> \<exists>C[M]. cartprod(M,A,B,C)"
apply (simp del: cartprod_abs add: cartprod_iff)
apply (insert power_ax, simp add: power_ax_def)
apply (frule_tac x="A \<union> B" and P="\<lambda>x. rex(M,Q(x))" for Q in rspec)
apply (blast, clarify)
apply (drule_tac x=z and P="\<lambda>x. rex(M,Q(x))" for Q in rspec, auto)
apply (intro rexI conjI, simp+)
apply (insert cartprod_separation [of A B], simp)
done

text\<open>All the lemmas above are necessary because Powerset is not absolute.
      I should have used Replacement instead!\<close>
lemma (in M_basic) cartprod_closed [intro,simp]:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> M(A*B)"
by (frule cartprod_closed_lemma, assumption, force)

lemma (in M_basic) sum_closed [intro,simp]:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> M(A+B)"
by (simp add: sum_def)

lemma (in M_basic) sum_abs [simp]:
     "\<lbrakk>M(A); M(B); M(Z)\<rbrakk> \<Longrightarrow> is_sum(M,A,B,Z) \<longleftrightarrow> (Z = A+B)"
by (simp add: is_sum_def sum_def singleton_0 nat_into_M)

lemma (in M_trivial) Inl_in_M_iff [iff]:
     "M(Inl(a)) \<longleftrightarrow> M(a)"
by (simp add: Inl_def)

lemma (in M_trivial) Inl_abs [simp]:
     "M(Z) \<Longrightarrow> is_Inl(M,a,Z) \<longleftrightarrow> (Z = Inl(a))"
by (simp add: is_Inl_def Inl_def)

lemma (in M_trivial) Inr_in_M_iff [iff]:
     "M(Inr(a)) \<longleftrightarrow> M(a)"
by (simp add: Inr_def)

lemma (in M_trivial) Inr_abs [simp]:
     "M(Z) \<Longrightarrow> is_Inr(M,a,Z) \<longleftrightarrow> (Z = Inr(a))"
by (simp add: is_Inr_def Inr_def)


subsubsection \<open>converse of a relation\<close>

lemma (in M_basic) M_converse_iff:
     "M(r) \<Longrightarrow>
      converse(r) =
      {z \<in> \<Union>(\<Union>(r)) * \<Union>(\<Union>(r)).
       \<exists>p\<in>r. \<exists>x[M]. \<exists>y[M]. p = \<langle>x,y\<rangle> \<and> z = \<langle>y,x\<rangle>}"
apply (rule equalityI)
 prefer 2 apply (blast dest: transM, clarify, simp)
apply (simp add: Pair_def)
apply (blast dest: transM)
done

lemma (in M_basic) converse_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(converse(r))"
apply (simp add: M_converse_iff)
apply (insert converse_separation [of r], simp)
done

lemma (in M_basic) converse_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> is_converse(M,r,z) \<longleftrightarrow> z = converse(r)"
apply (simp add: is_converse_def)
apply (rule iffI)
 prefer 2 apply blast
apply (rule M_equalityI)
  apply simp
  apply (blast dest: transM)+
done


subsubsection \<open>image, preimage, domain, range\<close>

lemma (in M_basic) image_closed [intro,simp]:
     "\<lbrakk>M(A); M(r)\<rbrakk> \<Longrightarrow> M(r``A)"
apply (simp add: image_iff_Collect)
apply (insert image_separation [of A r], simp)
done

lemma (in M_basic) vimage_abs [simp]:
     "\<lbrakk>M(r); M(A); M(z)\<rbrakk> \<Longrightarrow> pre_image(M,r,A,z) \<longleftrightarrow> z = r-``A"
apply (simp add: pre_image_def)
apply (rule iffI)
 apply (blast intro!: equalityI dest: transM, blast)
done

lemma (in M_basic) vimage_closed [intro,simp]:
     "\<lbrakk>M(A); M(r)\<rbrakk> \<Longrightarrow> M(r-``A)"
by (simp add: vimage_def)


subsubsection\<open>Domain, range and field\<close>

lemma (in M_trans) domain_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> is_domain(M,r,z) \<longleftrightarrow> z = domain(r)"
apply (simp add: is_domain_def)
apply (blast intro!: equalityI dest: transM)
done

lemma (in M_basic) domain_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(domain(r))"
apply (simp add: domain_eq_vimage)
done

lemma (in M_trans) range_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> is_range(M,r,z) \<longleftrightarrow> z = range(r)"
apply (simp add: is_range_def)
apply (blast intro!: equalityI dest: transM)
done

lemma (in M_basic) range_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(range(r))"
apply (simp add: range_eq_image)
done

lemma (in M_basic) field_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> is_field(M,r,z) \<longleftrightarrow> z = field(r)"
by (simp add: is_field_def field_def)

lemma (in M_basic) field_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(field(r))"
by (simp add: field_def)


subsubsection\<open>Relations, functions and application\<close>

lemma (in M_trans) relation_abs [simp]:
     "M(r) \<Longrightarrow> is_relation(M,r) \<longleftrightarrow> relation(r)"
apply (simp add: is_relation_def relation_def)
apply (blast dest!: bspec dest: pair_components_in_M)+
done

lemma (in M_trivial) function_abs [simp]:
     "M(r) \<Longrightarrow> is_function(M,r) \<longleftrightarrow> function(r)"
apply (simp add: is_function_def function_def, safe)
   apply (frule transM, assumption)
  apply (blast dest: pair_components_in_M)+
done

lemma (in M_basic) apply_closed [intro,simp]:
     "\<lbrakk>M(f); M(a)\<rbrakk> \<Longrightarrow> M(f`a)"
by (simp add: apply_def)

lemma (in M_basic) apply_abs [simp]:
     "\<lbrakk>M(f); M(x); M(y)\<rbrakk> \<Longrightarrow> fun_apply(M,f,x,y) \<longleftrightarrow> f`x = y"
apply (simp add: fun_apply_def apply_def, blast)
done

lemma (in M_trivial) typed_function_abs [simp]:
     "\<lbrakk>M(A); M(f)\<rbrakk> \<Longrightarrow> typed_function(M,A,B,f) \<longleftrightarrow> f \<in> A -> B"
apply (auto simp add: typed_function_def relation_def Pi_iff)
apply (blast dest: pair_components_in_M)+
done

lemma (in M_basic) injection_abs [simp]:
     "\<lbrakk>M(A); M(f)\<rbrakk> \<Longrightarrow> injection(M,A,B,f) \<longleftrightarrow> f \<in> inj(A,B)"
apply (simp add: injection_def apply_iff inj_def)
apply (blast dest: transM [of _ A])
done

lemma (in M_basic) surjection_abs [simp]:
     "\<lbrakk>M(A); M(B); M(f)\<rbrakk> \<Longrightarrow> surjection(M,A,B,f) \<longleftrightarrow> f \<in> surj(A,B)"
by (simp add: surjection_def surj_def)

lemma (in M_basic) bijection_abs [simp]:
     "\<lbrakk>M(A); M(B); M(f)\<rbrakk> \<Longrightarrow> bijection(M,A,B,f) \<longleftrightarrow> f \<in> bij(A,B)"
by (simp add: bijection_def bij_def)


subsubsection\<open>Composition of relations\<close>

lemma (in M_basic) M_comp_iff:
     "\<lbrakk>M(r); M(s)\<rbrakk>
      \<Longrightarrow> r O s =
          {xz \<in> domain(s) * range(r).
            \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. xz = \<langle>x,z\<rangle> \<and> \<langle>x,y\<rangle> \<in> s \<and> \<langle>y,z\<rangle> \<in> r}"
apply (simp add: comp_def)
apply (rule equalityI)
 apply clarify
 apply simp
 apply  (blast dest:  transM)+
done

lemma (in M_basic) comp_closed [intro,simp]:
     "\<lbrakk>M(r); M(s)\<rbrakk> \<Longrightarrow> M(r O s)"
apply (simp add: M_comp_iff)
apply (insert comp_separation [of r s], simp)
done

lemma (in M_basic) composition_abs [simp]:
     "\<lbrakk>M(r); M(s); M(t)\<rbrakk> \<Longrightarrow> composition(M,r,s,t) \<longleftrightarrow> t = r O s"
apply safe
 txt\<open>Proving \<^term>\<open>composition(M, r, s, r O s)\<close>\<close>
 prefer 2
 apply (simp add: composition_def comp_def)
 apply (blast dest: transM)
txt\<open>Opposite implication\<close>
apply (rule M_equalityI)
  apply (simp add: composition_def comp_def)
  apply (blast del: allE dest: transM)+
done

text\<open>no longer needed\<close>
lemma (in M_basic) restriction_is_function:
     "\<lbrakk>restriction(M,f,A,z); function(f); M(f); M(A); M(z)\<rbrakk>
      \<Longrightarrow> function(z)"
apply (simp add: restriction_def ball_iff_equiv)
apply (unfold function_def, blast)
done

lemma (in M_trans) restriction_abs [simp]:
     "\<lbrakk>M(f); M(A); M(z)\<rbrakk>
      \<Longrightarrow> restriction(M,f,A,z) \<longleftrightarrow> z = restrict(f,A)"
apply (simp add: ball_iff_equiv restriction_def restrict_def)
apply (blast intro!: equalityI dest: transM)
done


lemma (in M_trans) M_restrict_iff:
     "M(r) \<Longrightarrow> restrict(r,A) = {z \<in> r . \<exists>x\<in>A. \<exists>y[M]. z = \<langle>x, y\<rangle>}"
by (simp add: restrict_def, blast dest: transM)

lemma (in M_basic) restrict_closed [intro,simp]:
     "\<lbrakk>M(A); M(r)\<rbrakk> \<Longrightarrow> M(restrict(r,A))"
apply (simp add: M_restrict_iff)
apply (insert restrict_separation [of A], simp)
done

lemma (in M_trans) Inter_abs [simp]:
     "\<lbrakk>M(A); M(z)\<rbrakk> \<Longrightarrow> big_inter(M,A,z) \<longleftrightarrow> z = \<Inter>(A)"
apply (simp add: big_inter_def Inter_def)
apply (blast intro!: equalityI dest: transM)
done

lemma (in M_basic) Inter_closed [intro,simp]:
     "M(A) \<Longrightarrow> M(\<Inter>(A))"
by (insert Inter_separation, simp add: Inter_def)

lemma (in M_basic) Int_closed [intro,simp]:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> M(A \<inter> B)"
apply (subgoal_tac "M({A,B})")
apply (frule Inter_closed, force+)
done

lemma (in M_basic) Diff_closed [intro,simp]:
     "\<lbrakk>M(A); M(B)\<rbrakk> \<Longrightarrow> M(A-B)"
by (insert Diff_separation, simp add: Diff_def)

subsubsection\<open>Some Facts About Separation Axioms\<close>

lemma (in M_basic) separation_conj:
     "\<lbrakk>separation(M,P); separation(M,Q)\<rbrakk> \<Longrightarrow> separation(M, \<lambda>z. P(z) \<and> Q(z))"
by (simp del: separation_closed
         add: separation_iff Collect_Int_Collect_eq [symmetric])

(*???equalities*)
lemma Collect_Un_Collect_eq:
     "Collect(A,P) \<union> Collect(A,Q) = Collect(A, \<lambda>x. P(x) \<or> Q(x))"
by blast

lemma Diff_Collect_eq:
     "A - Collect(A,P) = Collect(A, \<lambda>x. \<not> P(x))"
by blast

lemma (in M_trans) Collect_rall_eq:
     "M(Y) \<Longrightarrow> Collect(A, \<lambda>x. \<forall>y[M]. y\<in>Y \<longrightarrow> P(x,y)) =
               (if Y=0 then A else (\<Inter>y \<in> Y. {x \<in> A. P(x,y)}))"
  by (simp,blast dest: transM)


lemma (in M_basic) separation_disj:
     "\<lbrakk>separation(M,P); separation(M,Q)\<rbrakk> \<Longrightarrow> separation(M, \<lambda>z. P(z) \<or> Q(z))"
by (simp del: separation_closed
         add: separation_iff Collect_Un_Collect_eq [symmetric])

lemma (in M_basic) separation_neg:
     "separation(M,P) \<Longrightarrow> separation(M, \<lambda>z. \<not>P(z))"
by (simp del: separation_closed
         add: separation_iff Diff_Collect_eq [symmetric])

lemma (in M_basic) separation_imp:
     "\<lbrakk>separation(M,P); separation(M,Q)\<rbrakk>
      \<Longrightarrow> separation(M, \<lambda>z. P(z) \<longrightarrow> Q(z))"
by (simp add: separation_neg separation_disj not_disj_iff_imp [symmetric])

text\<open>This result is a hint of how little can be done without the Reflection
  Theorem.  The quantifier has to be bounded by a set.  We also need another
  instance of Separation!\<close>
lemma (in M_basic) separation_rall:
     "\<lbrakk>M(Y); \<forall>y[M]. separation(M, \<lambda>x. P(x,y));
        \<forall>z[M]. strong_replacement(M, \<lambda>x y. y = {u \<in> z . P(u,x)})\<rbrakk>
      \<Longrightarrow> separation(M, \<lambda>x. \<forall>y[M]. y\<in>Y \<longrightarrow> P(x,y))"
apply (simp del: separation_closed rall_abs
         add: separation_iff Collect_rall_eq)
apply (blast intro!:  RepFun_closed dest: transM)
done


subsubsection\<open>Functions and function space\<close>

text\<open>The assumption \<^term>\<open>M(A->B)\<close> is unusual, but essential: in
all but trivial cases, A->B cannot be expected to belong to \<^term>\<open>M\<close>.\<close>
lemma (in M_trivial) is_funspace_abs [simp]:
     "\<lbrakk>M(A); M(B); M(F); M(A->B)\<rbrakk> \<Longrightarrow> is_funspace(M,A,B,F) \<longleftrightarrow> F = A->B"
apply (simp add: is_funspace_def)
apply (rule iffI)
 prefer 2 apply blast
apply (rule M_equalityI)
  apply simp_all
done

lemma (in M_basic) succ_fun_eq2:
     "\<lbrakk>M(B); M(n->B)\<rbrakk> \<Longrightarrow>
      succ(n) -> B =
      \<Union>{z. p \<in> (n->B)*B, \<exists>f[M]. \<exists>b[M]. p = \<langle>f,b\<rangle> \<and> z = {cons(\<langle>n,b\<rangle>, f)}}"
apply (simp add: succ_fun_eq)
apply (blast dest: transM)
done

lemma (in M_basic) funspace_succ:
     "\<lbrakk>M(n); M(B); M(n->B)\<rbrakk> \<Longrightarrow> M(succ(n) -> B)"
apply (insert funspace_succ_replacement [of n], simp)
apply (force simp add: succ_fun_eq2 univalent_def)
done

text\<open>\<^term>\<open>M\<close> contains all finite function spaces.  Needed to prove the
absoluteness of transitive closure.  See the definition of
\<open>rtrancl_alt\<close> in in \<open>WF_absolute.thy\<close>.\<close>
lemma (in M_basic) finite_funspace_closed [intro,simp]:
     "\<lbrakk>n\<in>nat; M(B)\<rbrakk> \<Longrightarrow> M(n->B)"
apply (induct_tac n, simp)
apply (simp add: funspace_succ nat_into_M)
done


subsection\<open>Relativization and Absoluteness for Boolean Operators\<close>

definition
  is_bool_of_o :: "[i\<Rightarrow>o, o, i] \<Rightarrow> o" where
   "is_bool_of_o(M,P,z) \<equiv> (P \<and> number1(M,z)) \<or> (\<not>P \<and> empty(M,z))"

definition
  is_not :: "[i\<Rightarrow>o, i, i] \<Rightarrow> o" where
   "is_not(M,a,z) \<equiv> (number1(M,a)  \<and> empty(M,z)) |
                     (\<not>number1(M,a) \<and> number1(M,z))"

definition
  is_and :: "[i\<Rightarrow>o, i, i, i] \<Rightarrow> o" where
   "is_and(M,a,b,z) \<equiv> (number1(M,a)  \<and> z=b) |
                       (\<not>number1(M,a) \<and> empty(M,z))"

definition
  is_or :: "[i\<Rightarrow>o, i, i, i] \<Rightarrow> o" where
   "is_or(M,a,b,z) \<equiv> (number1(M,a)  \<and> number1(M,z)) |
                      (\<not>number1(M,a) \<and> z=b)"

lemma (in M_trivial) bool_of_o_abs [simp]:
     "M(z) \<Longrightarrow> is_bool_of_o(M,P,z) \<longleftrightarrow> z = bool_of_o(P)"
by (simp add: is_bool_of_o_def bool_of_o_def)


lemma (in M_trivial) not_abs [simp]:
     "\<lbrakk>M(a); M(z)\<rbrakk> \<Longrightarrow> is_not(M,a,z) \<longleftrightarrow> z = not(a)"
by (simp add: Bool.not_def cond_def is_not_def)

lemma (in M_trivial) and_abs [simp]:
     "\<lbrakk>M(a); M(b); M(z)\<rbrakk> \<Longrightarrow> is_and(M,a,b,z) \<longleftrightarrow> z = a and b"
by (simp add: Bool.and_def cond_def is_and_def)

lemma (in M_trivial) or_abs [simp]:
     "\<lbrakk>M(a); M(b); M(z)\<rbrakk> \<Longrightarrow> is_or(M,a,b,z) \<longleftrightarrow> z = a or b"
by (simp add: Bool.or_def cond_def is_or_def)


lemma (in M_trivial) bool_of_o_closed [intro,simp]:
     "M(bool_of_o(P))"
by (simp add: bool_of_o_def)

lemma (in M_trivial) and_closed [intro,simp]:
     "\<lbrakk>M(p); M(q)\<rbrakk> \<Longrightarrow> M(p and q)"
by (simp add: and_def cond_def)

lemma (in M_trivial) or_closed [intro,simp]:
     "\<lbrakk>M(p); M(q)\<rbrakk> \<Longrightarrow> M(p or q)"
by (simp add: or_def cond_def)

lemma (in M_trivial) not_closed [intro,simp]:
     "M(p) \<Longrightarrow> M(not(p))"
by (simp add: Bool.not_def cond_def)


subsection\<open>Relativization and Absoluteness for List Operators\<close>

definition
  is_Nil :: "[i\<Rightarrow>o, i] \<Rightarrow> o" where
     \<comment> \<open>because \<^prop>\<open>[] \<equiv> Inl(0)\<close>\<close>
    "is_Nil(M,xs) \<equiv> \<exists>zero[M]. empty(M,zero) \<and> is_Inl(M,zero,xs)"

definition
  is_Cons :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
     \<comment> \<open>because \<^prop>\<open>Cons(a, l) \<equiv> Inr(\<langle>a,l\<rangle>)\<close>\<close>
    "is_Cons(M,a,l,Z) \<equiv> \<exists>p[M]. pair(M,a,l,p) \<and> is_Inr(M,p,Z)"


lemma (in M_trivial) Nil_in_M [intro,simp]: "M(Nil)"
by (simp add: Nil_def)

lemma (in M_trivial) Nil_abs [simp]: "M(Z) \<Longrightarrow> is_Nil(M,Z) \<longleftrightarrow> (Z = Nil)"
by (simp add: is_Nil_def Nil_def)

lemma (in M_trivial) Cons_in_M_iff [iff]: "M(Cons(a,l)) \<longleftrightarrow> M(a) \<and> M(l)"
by (simp add: Cons_def)

lemma (in M_trivial) Cons_abs [simp]:
     "\<lbrakk>M(a); M(l); M(Z)\<rbrakk> \<Longrightarrow> is_Cons(M,a,l,Z) \<longleftrightarrow> (Z = Cons(a,l))"
by (simp add: is_Cons_def Cons_def)


definition
  quasilist :: "i \<Rightarrow> o" where
    "quasilist(xs) \<equiv> xs=Nil \<or> (\<exists>x l. xs = Cons(x,l))"

definition
  is_quasilist :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
    "is_quasilist(M,z) \<equiv> is_Nil(M,z) \<or> (\<exists>x[M]. \<exists>l[M]. is_Cons(M,x,l,z))"

definition
  list_case' :: "[i, [i,i]\<Rightarrow>i, i] \<Rightarrow> i" where
    \<comment> \<open>A version of \<^term>\<open>list_case\<close> that's always defined.\<close>
    "list_case'(a,b,xs) \<equiv>
       if quasilist(xs) then list_case(a,b,xs) else 0"

definition
  is_list_case :: "[i\<Rightarrow>o, i, [i,i,i]\<Rightarrow>o, i, i] \<Rightarrow> o" where
    \<comment> \<open>Returns 0 for non-lists\<close>
    "is_list_case(M, a, is_b, xs, z) \<equiv>
       (is_Nil(M,xs) \<longrightarrow> z=a) \<and>
       (\<forall>x[M]. \<forall>l[M]. is_Cons(M,x,l,xs) \<longrightarrow> is_b(x,l,z)) \<and>
       (is_quasilist(M,xs) \<or> empty(M,z))"

definition
  hd' :: "i \<Rightarrow> i" where
    \<comment> \<open>A version of \<^term>\<open>hd\<close> that's always defined.\<close>
    "hd'(xs) \<equiv> if quasilist(xs) then hd(xs) else 0"

definition
  tl' :: "i \<Rightarrow> i" where
    \<comment> \<open>A version of \<^term>\<open>tl\<close> that's always defined.\<close>
    "tl'(xs) \<equiv> if quasilist(xs) then tl(xs) else 0"

definition
  is_hd :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
     \<comment> \<open>\<^term>\<open>hd([]) = 0\<close> no constraints if not a list.
          Avoiding implication prevents the simplifier's looping.\<close>
    "is_hd(M,xs,H) \<equiv>
       (is_Nil(M,xs) \<longrightarrow> empty(M,H)) \<and>
       (\<forall>x[M]. \<forall>l[M]. \<not> is_Cons(M,x,l,xs) \<or> H=x) \<and>
       (is_quasilist(M,xs) \<or> empty(M,H))"

definition
  is_tl :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
     \<comment> \<open>\<^term>\<open>tl([]) = []\<close>; see comments about \<^term>\<open>is_hd\<close>\<close>
    "is_tl(M,xs,T) \<equiv>
       (is_Nil(M,xs) \<longrightarrow> T=xs) \<and>
       (\<forall>x[M]. \<forall>l[M]. \<not> is_Cons(M,x,l,xs) \<or> T=l) \<and>
       (is_quasilist(M,xs) \<or> empty(M,T))"

subsubsection\<open>\<^term>\<open>quasilist\<close>: For Case-Splitting with \<^term>\<open>list_case'\<close>\<close>

lemma [iff]: "quasilist(Nil)"
by (simp add: quasilist_def)

lemma [iff]: "quasilist(Cons(x,l))"
by (simp add: quasilist_def)

lemma list_imp_quasilist: "l \<in> list(A) \<Longrightarrow> quasilist(l)"
by (erule list.cases, simp_all)

subsubsection\<open>\<^term>\<open>list_case'\<close>, the Modified Version of \<^term>\<open>list_case\<close>\<close>

lemma list_case'_Nil [simp]: "list_case'(a,b,Nil) = a"
by (simp add: list_case'_def quasilist_def)

lemma list_case'_Cons [simp]: "list_case'(a,b,Cons(x,l)) = b(x,l)"
by (simp add: list_case'_def quasilist_def)

lemma non_list_case: "\<not> quasilist(x) \<Longrightarrow> list_case'(a,b,x) = 0"
by (simp add: quasilist_def list_case'_def)

lemma list_case'_eq_list_case [simp]:
     "xs \<in> list(A) \<Longrightarrow>list_case'(a,b,xs) = list_case(a,b,xs)"
by (erule list.cases, simp_all)

lemma (in M_basic) list_case'_closed [intro,simp]:
  "\<lbrakk>M(k); M(a); \<forall>x[M]. \<forall>y[M]. M(b(x,y))\<rbrakk> \<Longrightarrow> M(list_case'(a,b,k))"
apply (case_tac "quasilist(k)")
 apply (simp add: quasilist_def, force)
apply (simp add: non_list_case)
done

lemma (in M_trivial) quasilist_abs [simp]:
     "M(z) \<Longrightarrow> is_quasilist(M,z) \<longleftrightarrow> quasilist(z)"
by (auto simp add: is_quasilist_def quasilist_def)

lemma (in M_trivial) list_case_abs [simp]:
     "\<lbrakk>relation2(M,is_b,b); M(k); M(z)\<rbrakk>
      \<Longrightarrow> is_list_case(M,a,is_b,k,z) \<longleftrightarrow> z = list_case'(a,b,k)"
apply (case_tac "quasilist(k)")
 prefer 2
 apply (simp add: is_list_case_def non_list_case)
 apply (force simp add: quasilist_def)
apply (simp add: quasilist_def is_list_case_def)
apply (elim disjE exE)
 apply (simp_all add: relation2_def)
done


subsubsection\<open>The Modified Operators \<^term>\<open>hd'\<close> and \<^term>\<open>tl'\<close>\<close>

lemma (in M_trivial) is_hd_Nil: "is_hd(M,[],Z) \<longleftrightarrow> empty(M,Z)"
by (simp add: is_hd_def)

lemma (in M_trivial) is_hd_Cons:
     "\<lbrakk>M(a); M(l)\<rbrakk> \<Longrightarrow> is_hd(M,Cons(a,l),Z) \<longleftrightarrow> Z = a"
by (force simp add: is_hd_def)

lemma (in M_trivial) hd_abs [simp]:
     "\<lbrakk>M(x); M(y)\<rbrakk> \<Longrightarrow> is_hd(M,x,y) \<longleftrightarrow> y = hd'(x)"
apply (simp add: hd'_def)
apply (intro impI conjI)
 prefer 2 apply (force simp add: is_hd_def)
apply (simp add: quasilist_def is_hd_def)
apply (elim disjE exE, auto)
done

lemma (in M_trivial) is_tl_Nil: "is_tl(M,[],Z) \<longleftrightarrow> Z = []"
by (simp add: is_tl_def)

lemma (in M_trivial) is_tl_Cons:
     "\<lbrakk>M(a); M(l)\<rbrakk> \<Longrightarrow> is_tl(M,Cons(a,l),Z) \<longleftrightarrow> Z = l"
by (force simp add: is_tl_def)

lemma (in M_trivial) tl_abs [simp]:
     "\<lbrakk>M(x); M(y)\<rbrakk> \<Longrightarrow> is_tl(M,x,y) \<longleftrightarrow> y = tl'(x)"
apply (simp add: tl'_def)
apply (intro impI conjI)
 prefer 2 apply (force simp add: is_tl_def)
apply (simp add: quasilist_def is_tl_def)
apply (elim disjE exE, auto)
done

lemma (in M_trivial) relation1_tl: "relation1(M, is_tl(M), tl')"
by (simp add: relation1_def)

lemma hd'_Nil: "hd'([]) = 0"
by (simp add: hd'_def)

lemma hd'_Cons: "hd'(Cons(a,l)) = a"
by (simp add: hd'_def)

lemma tl'_Nil: "tl'([]) = []"
by (simp add: tl'_def)

lemma tl'_Cons: "tl'(Cons(a,l)) = l"
by (simp add: tl'_def)

lemma iterates_tl_Nil: "n \<in> nat \<Longrightarrow> tl'^n ([]) = []"
apply (induct_tac n)
apply (simp_all add: tl'_Nil)
done

lemma (in M_basic) tl'_closed: "M(x) \<Longrightarrow> M(tl'(x))"
apply (simp add: tl'_def)
apply (force simp add: quasilist_def)
done


end
