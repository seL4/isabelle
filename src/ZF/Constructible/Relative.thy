header {*Relativization and Absoluteness*}

theory Relative = Main:

subsection{* Relativized versions of standard set-theoretic concepts *}

constdefs
  empty :: "[i=>o,i] => o"
    "empty(M,z) == \<forall>x[M]. x \<notin> z"

  subset :: "[i=>o,i,i] => o"
    "subset(M,A,B) == \<forall>x[M]. x\<in>A --> x \<in> B"

  upair :: "[i=>o,i,i,i] => o"
    "upair(M,a,b,z) == a \<in> z & b \<in> z & (\<forall>x[M]. x\<in>z --> x = a | x = b)"

  pair :: "[i=>o,i,i,i] => o"
    "pair(M,a,b,z) == \<exists>x[M]. upair(M,a,a,x) & 
                          (\<exists>y[M]. upair(M,a,b,y) & upair(M,x,y,z))"


  union :: "[i=>o,i,i,i] => o"
    "union(M,a,b,z) == \<forall>x[M]. x \<in> z <-> x \<in> a | x \<in> b"

  is_cons :: "[i=>o,i,i,i] => o"
    "is_cons(M,a,b,z) == \<exists>x[M]. upair(M,a,a,x) & union(M,x,b,z)"

  successor :: "[i=>o,i,i] => o"
    "successor(M,a,z) == is_cons(M,a,a,z)"

  powerset :: "[i=>o,i,i] => o"
    "powerset(M,A,z) == \<forall>x[M]. x \<in> z <-> subset(M,x,A)"

  inter :: "[i=>o,i,i,i] => o"
    "inter(M,a,b,z) == \<forall>x[M]. x \<in> z <-> x \<in> a & x \<in> b"

  setdiff :: "[i=>o,i,i,i] => o"
    "setdiff(M,a,b,z) == \<forall>x[M]. x \<in> z <-> x \<in> a & x \<notin> b"

  big_union :: "[i=>o,i,i] => o"
    "big_union(M,A,z) == \<forall>x[M]. x \<in> z <-> (\<exists>y[M]. y\<in>A & x \<in> y)"

  big_inter :: "[i=>o,i,i] => o"
    "big_inter(M,A,z) == 
             (A=0 --> z=0) &
	     (A\<noteq>0 --> (\<forall>x[M]. x \<in> z <-> (\<forall>y[M]. y\<in>A --> x \<in> y)))"

  cartprod :: "[i=>o,i,i,i] => o"
    "cartprod(M,A,B,z) == 
	\<forall>u[M]. u \<in> z <-> (\<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,u)))"

  is_converse :: "[i=>o,i,i] => o"
    "is_converse(M,r,z) == 
	\<forall>x[M]. x \<in> z <-> 
             (\<exists>w[M]. w\<in>r & (\<exists>u[M]. \<exists>v[M]. pair(M,u,v,w) & pair(M,v,u,x)))"

  pre_image :: "[i=>o,i,i,i] => o"
    "pre_image(M,r,A,z) == 
	\<forall>x[M]. x \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. y\<in>A & pair(M,x,y,w)))"

  is_domain :: "[i=>o,i,i] => o"
    "is_domain(M,r,z) == 
	\<forall>x[M]. (x \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>y[M]. pair(M,x,y,w))))"

  image :: "[i=>o,i,i,i] => o"
    "image(M,r,A,z) == 
        \<forall>y[M]. (y \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,w))))"

  is_range :: "[i=>o,i,i] => o"
    --{*the cleaner 
      @{term "\<exists>r'[M]. is_converse(M,r,r') & is_domain(M,r',z)"}
      unfortunately needs an instance of separation in order to prove 
        @{term "M(converse(r))"}.*}
    "is_range(M,r,z) == 
	\<forall>y[M]. (y \<in> z <-> (\<exists>w[M]. w\<in>r & (\<exists>x[M]. pair(M,x,y,w))))"

  is_field :: "[i=>o,i,i] => o"
    "is_field(M,r,z) == 
	\<exists>dr[M]. is_domain(M,r,dr) & 
            (\<exists>rr[M]. is_range(M,r,rr) & union(M,dr,rr,z))"

  is_relation :: "[i=>o,i] => o"
    "is_relation(M,r) == 
        (\<forall>z[M]. z\<in>r --> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,z)))"

  is_function :: "[i=>o,i] => o"
    "is_function(M,r) == 
	\<forall>x[M]. \<forall>y[M]. \<forall>y'[M]. \<forall>p[M]. \<forall>p'[M]. 
           pair(M,x,y,p) --> pair(M,x,y',p') --> p\<in>r --> p'\<in>r --> y=y'"

  fun_apply :: "[i=>o,i,i,i] => o"
    "fun_apply(M,f,x,y) == 
	(\<forall>y'[M]. (\<exists>u[M]. u\<in>f & pair(M,x,y',u)) <-> y=y')"

  typed_function :: "[i=>o,i,i,i] => o"
    "typed_function(M,A,B,r) == 
        is_function(M,r) & is_relation(M,r) & is_domain(M,r,A) &
        (\<forall>u[M]. u\<in>r --> (\<forall>x[M]. \<forall>y[M]. pair(M,x,y,u) --> y\<in>B))"

  is_funspace :: "[i=>o,i,i,i] => o"
    "is_funspace(M,A,B,F) == 
        \<forall>f[M]. f \<in> F <-> typed_function(M,A,B,f)"

  composition :: "[i=>o,i,i,i] => o"
    "composition(M,r,s,t) == 
        \<forall>p[M]. p \<in> t <-> 
               (\<exists>x[M]. \<exists>y[M]. \<exists>z[M]. pair(M,x,z,p) & \<langle>x,y\<rangle> \<in> s & \<langle>y,z\<rangle> \<in> r)"


  injection :: "[i=>o,i,i,i] => o"
    "injection(M,A,B,f) == 
	typed_function(M,A,B,f) &
        (\<forall>x[M]. \<forall>x'[M]. \<forall>y[M]. \<forall>p[M]. \<forall>p'[M]. 
          pair(M,x,y,p) --> pair(M,x',y,p') --> p\<in>f --> p'\<in>f --> x=x')"

  surjection :: "[i=>o,i,i,i] => o"
    "surjection(M,A,B,f) == 
        typed_function(M,A,B,f) &
        (\<forall>y[M]. y\<in>B --> (\<exists>x[M]. x\<in>A & fun_apply(M,f,x,y)))"

  bijection :: "[i=>o,i,i,i] => o"
    "bijection(M,A,B,f) == injection(M,A,B,f) & surjection(M,A,B,f)"

  restriction :: "[i=>o,i,i,i] => o"
    "restriction(M,r,A,z) == 
	\<forall>x[M]. x \<in> z <-> (x \<in> r & (\<exists>u[M]. u\<in>A & (\<exists>v[M]. pair(M,u,v,x))))"

  transitive_set :: "[i=>o,i] => o"
    "transitive_set(M,a) == \<forall>x[M]. x\<in>a --> subset(M,x,a)"

  ordinal :: "[i=>o,i] => o"
     --{*an ordinal is a transitive set of transitive sets*}
    "ordinal(M,a) == transitive_set(M,a) & (\<forall>x[M]. x\<in>a --> transitive_set(M,x))"

  limit_ordinal :: "[i=>o,i] => o"
    --{*a limit ordinal is a non-empty, successor-closed ordinal*}
    "limit_ordinal(M,a) == 
	ordinal(M,a) & ~ empty(M,a) & 
        (\<forall>x[M]. x\<in>a --> (\<exists>y[M]. y\<in>a & successor(M,x,y)))"

  successor_ordinal :: "[i=>o,i] => o"
    --{*a successor ordinal is any ordinal that is neither empty nor limit*}
    "successor_ordinal(M,a) == 
	ordinal(M,a) & ~ empty(M,a) & ~ limit_ordinal(M,a)"

  finite_ordinal :: "[i=>o,i] => o"
    --{*an ordinal is finite if neither it nor any of its elements are limit*}
    "finite_ordinal(M,a) == 
	ordinal(M,a) & ~ limit_ordinal(M,a) & 
        (\<forall>x[M]. x\<in>a --> ~ limit_ordinal(M,x))"

  omega :: "[i=>o,i] => o"
    --{*omega is a limit ordinal none of whose elements are limit*}
    "omega(M,a) == limit_ordinal(M,a) & (\<forall>x[M]. x\<in>a --> ~ limit_ordinal(M,x))"

  number1 :: "[i=>o,i] => o"
    "number1(M,a) == (\<exists>x[M]. empty(M,x) & successor(M,x,a))"

  number2 :: "[i=>o,i] => o"
    "number2(M,a) == (\<exists>x[M]. number1(M,x) & successor(M,x,a))"

  number3 :: "[i=>o,i] => o"
    "number3(M,a) == (\<exists>x[M]. number2(M,x) & successor(M,x,a))"


subsection {*The relativized ZF axioms*}
constdefs

  extensionality :: "(i=>o) => o"
    "extensionality(M) == 
	\<forall>x[M]. \<forall>y[M]. (\<forall>z[M]. z \<in> x <-> z \<in> y) --> x=y"

  separation :: "[i=>o, i=>o] => o"
    --{*Big problem: the formula @{text P} should only involve parameters
        belonging to @{text M}.  Don't see how to enforce that.*}
    "separation(M,P) == 
	\<forall>z[M]. \<exists>y[M]. \<forall>x[M]. x \<in> y <-> x \<in> z & P(x)"

  upair_ax :: "(i=>o) => o"
    "upair_ax(M) == \<forall>x y. M(x) --> M(y) --> (\<exists>z[M]. upair(M,x,y,z))"

  Union_ax :: "(i=>o) => o"
    "Union_ax(M) == \<forall>x[M]. (\<exists>z[M]. big_union(M,x,z))"

  power_ax :: "(i=>o) => o"
    "power_ax(M) == \<forall>x[M]. (\<exists>z[M]. powerset(M,x,z))"

  univalent :: "[i=>o, i, [i,i]=>o] => o"
    "univalent(M,A,P) == 
	(\<forall>x[M]. x\<in>A --> (\<forall>y z. M(y) --> M(z) --> P(x,y) & P(x,z) --> y=z))"

  replacement :: "[i=>o, [i,i]=>o] => o"
    "replacement(M,P) == 
      \<forall>A[M]. univalent(M,A,P) -->
      (\<exists>Y[M]. (\<forall>b[M]. ((\<exists>x[M]. x\<in>A & P(x,b)) --> b \<in> Y)))"

  strong_replacement :: "[i=>o, [i,i]=>o] => o"
    "strong_replacement(M,P) == 
      \<forall>A[M]. univalent(M,A,P) -->
      (\<exists>Y[M]. (\<forall>b[M]. (b \<in> Y <-> (\<exists>x[M]. x\<in>A & P(x,b)))))"

  foundation_ax :: "(i=>o) => o"
    "foundation_ax(M) == 
	\<forall>x[M]. (\<exists>y\<in>x. M(y))
                 --> (\<exists>y[M]. y\<in>x & ~(\<exists>z[M]. z\<in>x & z \<in> y))"


subsection{*A trivial consistency proof for $V_\omega$ *}

text{*We prove that $V_\omega$ 
      (or @{text univ} in Isabelle) satisfies some ZF axioms.
     Kunen, Theorem IV 3.13, page 123.*}

lemma univ0_downwards_mem: "[| y \<in> x; x \<in> univ(0) |] ==> y \<in> univ(0)"
apply (insert Transset_univ [OF Transset_0])  
apply (simp add: Transset_def, blast) 
done

lemma univ0_Ball_abs [simp]: 
     "A \<in> univ(0) ==> (\<forall>x\<in>A. x \<in> univ(0) --> P(x)) <-> (\<forall>x\<in>A. P(x))" 
by (blast intro: univ0_downwards_mem) 

lemma univ0_Bex_abs [simp]: 
     "A \<in> univ(0) ==> (\<exists>x\<in>A. x \<in> univ(0) & P(x)) <-> (\<exists>x\<in>A. P(x))" 
by (blast intro: univ0_downwards_mem) 

text{*Congruence rule for separation: can assume the variable is in @{text M}*}
lemma separation_cong [cong]:
     "(!!x. M(x) ==> P(x) <-> P'(x)) ==> separation(M,P) <-> separation(M,P')"
by (simp add: separation_def) 

text{*Congruence rules for replacement*}
lemma univalent_cong [cong]:
     "[| A=A'; !!x y. [| x\<in>A; M(x); M(y) |] ==> P(x,y) <-> P'(x,y) |] 
      ==> univalent(M,A,P) <-> univalent(M,A',P')"
by (simp add: univalent_def) 

lemma strong_replacement_cong [cong]:
     "[| !!x y. [| M(x); M(y) |] ==> P(x,y) <-> P'(x,y) |] 
      ==> strong_replacement(M,P) <-> strong_replacement(M,P')" 
by (simp add: strong_replacement_def) 

text{*The extensionality axiom*}
lemma "extensionality(\<lambda>x. x \<in> univ(0))"
apply (simp add: extensionality_def)
apply (blast intro: univ0_downwards_mem) 
done

text{*The separation axiom requires some lemmas*}
lemma Collect_in_Vfrom:
     "[| X \<in> Vfrom(A,j);  Transset(A) |] ==> Collect(X,P) \<in> Vfrom(A, succ(j))"
apply (drule Transset_Vfrom)
apply (rule subset_mem_Vfrom)
apply (unfold Transset_def, blast)
done

lemma Collect_in_VLimit:
     "[| X \<in> Vfrom(A,i);  Limit(i);  Transset(A) |] 
      ==> Collect(X,P) \<in> Vfrom(A,i)"
apply (rule Limit_VfromE, assumption+)
apply (blast intro: Limit_has_succ VfromI Collect_in_Vfrom)
done

lemma Collect_in_univ:
     "[| X \<in> univ(A);  Transset(A) |] ==> Collect(X,P) \<in> univ(A)"
by (simp add: univ_def Collect_in_VLimit Limit_nat)

lemma "separation(\<lambda>x. x \<in> univ(0), P)"
apply (simp add: separation_def, clarify) 
apply (rule_tac x = "Collect(x,P)" in bexI) 
apply (blast intro: Collect_in_univ Transset_0)+
done

text{*Unordered pairing axiom*}
lemma "upair_ax(\<lambda>x. x \<in> univ(0))"
apply (simp add: upair_ax_def upair_def)  
apply (blast intro: doubleton_in_univ) 
done

text{*Union axiom*}
lemma "Union_ax(\<lambda>x. x \<in> univ(0))"  
apply (simp add: Union_ax_def big_union_def, clarify) 
apply (rule_tac x="\<Union>x" in bexI)  
 apply (blast intro: univ0_downwards_mem)
apply (blast intro: Union_in_univ Transset_0) 
done

text{*Powerset axiom*}

lemma Pow_in_univ:
     "[| X \<in> univ(A);  Transset(A) |] ==> Pow(X) \<in> univ(A)"
apply (simp add: univ_def Pow_in_VLimit Limit_nat)
done

lemma "power_ax(\<lambda>x. x \<in> univ(0))"  
apply (simp add: power_ax_def powerset_def subset_def, clarify) 
apply (rule_tac x="Pow(x)" in bexI)
 apply (blast intro: univ0_downwards_mem)
apply (blast intro: Pow_in_univ Transset_0) 
done

text{*Foundation axiom*}
lemma "foundation_ax(\<lambda>x. x \<in> univ(0))"  
apply (simp add: foundation_ax_def, clarify)
apply (cut_tac A=x in foundation) 
apply (blast intro: univ0_downwards_mem)
done

lemma "replacement(\<lambda>x. x \<in> univ(0), P)"  
apply (simp add: replacement_def, clarify) 
oops
text{*no idea: maybe prove by induction on the rank of A?*}

text{*Still missing: Replacement, Choice*}

subsection{*lemmas needed to reduce some set constructions to instances
      of Separation*}

lemma image_iff_Collect: "r `` A = {y \<in> Union(Union(r)). \<exists>p\<in>r. \<exists>x\<in>A. p=<x,y>}"
apply (rule equalityI, auto) 
apply (simp add: Pair_def, blast) 
done

lemma vimage_iff_Collect:
     "r -`` A = {x \<in> Union(Union(r)). \<exists>p\<in>r. \<exists>y\<in>A. p=<x,y>}"
apply (rule equalityI, auto) 
apply (simp add: Pair_def, blast) 
done

text{*These two lemmas lets us prove @{text domain_closed} and 
      @{text range_closed} without new instances of separation*}

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
    "[| replacement(M,P); M(A);  univalent(M,A,P) |]
     ==> \<exists>Y[M]. (\<forall>b[M]. ((\<exists>x[M]. x\<in>A & P(x,b)) --> b \<in> Y))"
by (simp add: replacement_def) 

lemma strong_replacementD:
    "[| strong_replacement(M,P); M(A);  univalent(M,A,P) |]
     ==> \<exists>Y[M]. (\<forall>b[M]. (b \<in> Y <-> (\<exists>x[M]. x\<in>A & P(x,b))))"
by (simp add: strong_replacement_def) 

lemma separationD:
    "[| separation(M,P); M(z) |] ==> \<exists>y[M]. \<forall>x[M]. x \<in> y <-> x \<in> z & P(x)"
by (simp add: separation_def) 


text{*More constants, for order types*}
constdefs

  order_isomorphism :: "[i=>o,i,i,i,i,i] => o"
    "order_isomorphism(M,A,r,B,s,f) == 
        bijection(M,A,B,f) & 
        (\<forall>x[M]. x\<in>A --> (\<forall>y[M]. y\<in>A -->
          (\<forall>p[M]. \<forall>fx[M]. \<forall>fy[M]. \<forall>q[M].
            pair(M,x,y,p) --> fun_apply(M,f,x,fx) --> fun_apply(M,f,y,fy) --> 
            pair(M,fx,fy,q) --> (p\<in>r <-> q\<in>s))))"

  pred_set :: "[i=>o,i,i,i,i] => o"
    "pred_set(M,A,x,r,B) == 
	\<forall>y[M]. y \<in> B <-> (\<exists>p[M]. p\<in>r & y \<in> A & pair(M,y,x,p))"

  membership :: "[i=>o,i,i] => o" --{*membership relation*}
    "membership(M,A,r) == 
	\<forall>p[M]. p \<in> r <-> (\<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>A & x\<in>y & pair(M,x,y,p)))"


subsection{*Absoluteness for a transitive class model*}

text{*The class M is assumed to be transitive and to satisfy some
      relativized ZF axioms*}
locale M_triv_axioms =
  fixes M
  assumes transM:           "[| y\<in>x; M(x) |] ==> M(y)"
      and nonempty [simp]:  "M(0)"
      and upair_ax:	    "upair_ax(M)"
      and Union_ax:	    "Union_ax(M)"
      and power_ax:         "power_ax(M)"
      and replacement:      "replacement(M,P)"
      and M_nat [iff]:      "M(nat)"           (*i.e. the axiom of infinity*)

lemma (in M_triv_axioms) ball_abs [simp]: 
     "M(A) ==> (\<forall>x\<in>A. M(x) --> P(x)) <-> (\<forall>x\<in>A. P(x))" 
by (blast intro: transM) 

lemma (in M_triv_axioms) rall_abs [simp]: 
     "M(A) ==> (\<forall>x[M]. x\<in>A --> P(x)) <-> (\<forall>x\<in>A. P(x))" 
by (blast intro: transM) 

lemma (in M_triv_axioms) bex_abs [simp]: 
     "M(A) ==> (\<exists>x\<in>A. M(x) & P(x)) <-> (\<exists>x\<in>A. P(x))" 
by (blast intro: transM) 

lemma (in M_triv_axioms) rex_abs [simp]: 
     "M(A) ==> (\<exists>x[M]. x\<in>A & P(x)) <-> (\<exists>x\<in>A. P(x))" 
by (blast intro: transM) 

lemma (in M_triv_axioms) ball_iff_equiv: 
     "M(A) ==> (\<forall>x[M]. (x\<in>A <-> P(x))) <-> 
               (\<forall>x\<in>A. P(x)) & (\<forall>x. P(x) --> M(x) --> x\<in>A)" 
by (blast intro: transM)

text{*Simplifies proofs of equalities when there's an iff-equality
      available for rewriting, universally quantified over M. *}
lemma (in M_triv_axioms) M_equalityI: 
     "[| !!x. M(x) ==> x\<in>A <-> x\<in>B; M(A); M(B) |] ==> A=B"
by (blast intro!: equalityI dest: transM) 

lemma (in M_triv_axioms) empty_abs [simp]: 
     "M(z) ==> empty(M,z) <-> z=0"
apply (simp add: empty_def)
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) subset_abs [simp]: 
     "M(A) ==> subset(M,A,B) <-> A \<subseteq> B"
apply (simp add: subset_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) upair_abs [simp]: 
     "M(z) ==> upair(M,a,b,z) <-> z={a,b}"
apply (simp add: upair_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) upair_in_M_iff [iff]:
     "M({a,b}) <-> M(a) & M(b)"
apply (insert upair_ax, simp add: upair_ax_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) singleton_in_M_iff [iff]:
     "M({a}) <-> M(a)"
by (insert upair_in_M_iff [of a a], simp) 

lemma (in M_triv_axioms) pair_abs [simp]: 
     "M(z) ==> pair(M,a,b,z) <-> z=<a,b>"
apply (simp add: pair_def ZF.Pair_def)
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) pair_in_M_iff [iff]:
     "M(<a,b>) <-> M(a) & M(b)"
by (simp add: ZF.Pair_def)

lemma (in M_triv_axioms) pair_components_in_M:
     "[| <x,y> \<in> A; M(A) |] ==> M(x) & M(y)"
apply (simp add: Pair_def)
apply (blast dest: transM) 
done

lemma (in M_triv_axioms) cartprod_abs [simp]: 
     "[| M(A); M(B); M(z) |] ==> cartprod(M,A,B,z) <-> z = A*B"
apply (simp add: cartprod_def)
apply (rule iffI) 
 apply (blast intro!: equalityI intro: transM dest!: rspec) 
apply (blast dest: transM) 
done

lemma (in M_triv_axioms) union_abs [simp]: 
     "[| M(a); M(b); M(z) |] ==> union(M,a,b,z) <-> z = a Un b"
apply (simp add: union_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) inter_abs [simp]: 
     "[| M(a); M(b); M(z) |] ==> inter(M,a,b,z) <-> z = a Int b"
apply (simp add: inter_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) setdiff_abs [simp]: 
     "[| M(a); M(b); M(z) |] ==> setdiff(M,a,b,z) <-> z = a-b"
apply (simp add: setdiff_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) Union_abs [simp]: 
     "[| M(A); M(z) |] ==> big_union(M,A,z) <-> z = Union(A)"
apply (simp add: big_union_def) 
apply (blast intro!: equalityI dest: transM) 
done

lemma (in M_triv_axioms) Union_closed [intro,simp]:
     "M(A) ==> M(Union(A))"
by (insert Union_ax, simp add: Union_ax_def) 

lemma (in M_triv_axioms) Un_closed [intro,simp]:
     "[| M(A); M(B) |] ==> M(A Un B)"
by (simp only: Un_eq_Union, blast) 

lemma (in M_triv_axioms) cons_closed [intro,simp]:
     "[| M(a); M(A) |] ==> M(cons(a,A))"
by (subst cons_eq [symmetric], blast) 

lemma (in M_triv_axioms) cons_abs [simp]: 
     "[| M(b); M(z) |] ==> is_cons(M,a,b,z) <-> z = cons(a,b)"
by (simp add: is_cons_def, blast intro: transM)  

lemma (in M_triv_axioms) successor_abs [simp]: 
     "[| M(a); M(z) |] ==> successor(M,a,z) <-> z = succ(a)"
by (simp add: successor_def, blast)  

lemma (in M_triv_axioms) succ_in_M_iff [iff]:
     "M(succ(a)) <-> M(a)"
apply (simp add: succ_def) 
apply (blast intro: transM) 
done

lemma (in M_triv_axioms) separation_closed [intro,simp]:
     "[| separation(M,P); M(A) |] ==> M(Collect(A,P))"
apply (insert separation, simp add: separation_def) 
apply (drule rspec, assumption, clarify) 
apply (subgoal_tac "y = Collect(A,P)", blast)
apply (blast dest: transM) 
done

text{*Probably the premise and conclusion are equivalent*}
lemma (in M_triv_axioms) strong_replacementI [OF rallI]:
    "[| \<forall>A[M]. separation(M, %u. \<exists>x[M]. x\<in>A & P(x,u)) |]
     ==> strong_replacement(M,P)"
apply (simp add: strong_replacement_def, clarify) 
apply (frule replacementD [OF replacement], assumption, clarify) 
apply (drule_tac x=A in rspec, clarify)  
apply (drule_tac z=Y in separationD, assumption, clarify) 
apply (rule_tac x=y in rexI) 
apply (blast dest: transM)+
done


(*The last premise expresses that P takes M to M*)
lemma (in M_triv_axioms) strong_replacement_closed [intro,simp]:
     "[| strong_replacement(M,P); M(A); univalent(M,A,P); 
       !!x y. [| x\<in>A; P(x,y); M(x) |] ==> M(y) |] ==> M(Replace(A,P))"
apply (simp add: strong_replacement_def) 
apply (drule rspec, auto) 
apply (subgoal_tac "Replace(A,P) = Y")
 apply simp 
apply (rule equality_iffI) 
apply (simp add: Replace_iff, safe)
 apply (blast dest: transM) 
apply (frule transM, assumption) 
 apply (simp add: univalent_def)
 apply (drule rspec [THEN iffD1], assumption, assumption)
 apply (blast dest: transM) 
done

(*The first premise can't simply be assumed as a schema.
  It is essential to take care when asserting instances of Replacement.
  Let K be a nonconstructible subset of nat and define
  f(x) = x if x:K and f(x)=0 otherwise.  Then RepFun(nat,f) = cons(0,K), a 
  nonconstructible set.  So we cannot assume that M(X) implies M(RepFun(X,f))
  even for f : M -> M.
*)
lemma (in M_triv_axioms) RepFun_closed [intro,simp]:
     "[| strong_replacement(M, \<lambda>x y. y = f(x)); M(A); \<forall>x\<in>A. M(f(x)) |]
      ==> M(RepFun(A,f))"
apply (simp add: RepFun_def) 
apply (rule strong_replacement_closed) 
apply (auto dest: transM  simp add: univalent_def) 
done

lemma (in M_triv_axioms) lam_closed [intro,simp]:
     "[| strong_replacement(M, \<lambda>x y. y = <x,b(x)>); M(A); \<forall>x\<in>A. M(b(x)) |]
      ==> M(\<lambda>x\<in>A. b(x))"
by (simp add: lam_def, blast dest: transM) 

lemma (in M_triv_axioms) image_abs [simp]: 
     "[| M(r); M(A); M(z) |] ==> image(M,r,A,z) <-> z = r``A"
apply (simp add: image_def)
apply (rule iffI) 
 apply (blast intro!: equalityI dest: transM, blast) 
done

text{*What about @{text Pow_abs}?  Powerset is NOT absolute!
      This result is one direction of absoluteness.*}

lemma (in M_triv_axioms) powerset_Pow: 
     "powerset(M, x, Pow(x))"
by (simp add: powerset_def)

text{*But we can't prove that the powerset in @{text M} includes the
      real powerset.*}
lemma (in M_triv_axioms) powerset_imp_subset_Pow: 
     "[| powerset(M,x,y); M(y) |] ==> y <= Pow(x)"
apply (simp add: powerset_def) 
apply (blast dest: transM) 
done

lemma (in M_triv_axioms) nat_into_M [intro]:
     "n \<in> nat ==> M(n)"
by (induct n rule: nat_induct, simp_all)

lemma (in M_triv_axioms) nat_case_closed:
  "[|M(k); M(a); \<forall>m[M]. M(b(m))|] ==> M(nat_case(a,b,k))"
apply (case_tac "k=0", simp) 
apply (case_tac "\<exists>m. k = succ(m)", force)
apply (simp add: nat_case_def) 
done

lemma (in M_triv_axioms) Inl_in_M_iff [iff]:
     "M(Inl(a)) <-> M(a)"
by (simp add: Inl_def) 

lemma (in M_triv_axioms) Inr_in_M_iff [iff]:
     "M(Inr(a)) <-> M(a)"
by (simp add: Inr_def)


subsection{*Absoluteness for ordinals*}
text{*These results constitute Theorem IV 5.1 of Kunen (page 126).*}

lemma (in M_triv_axioms) lt_closed:
     "[| j<i; M(i) |] ==> M(j)" 
by (blast dest: ltD intro: transM) 

lemma (in M_triv_axioms) transitive_set_abs [simp]: 
     "M(a) ==> transitive_set(M,a) <-> Transset(a)"
by (simp add: transitive_set_def Transset_def)

lemma (in M_triv_axioms) ordinal_abs [simp]: 
     "M(a) ==> ordinal(M,a) <-> Ord(a)"
by (simp add: ordinal_def Ord_def)

lemma (in M_triv_axioms) limit_ordinal_abs [simp]: 
     "M(a) ==> limit_ordinal(M,a) <-> Limit(a)"
apply (simp add: limit_ordinal_def Ord_0_lt_iff Limit_def) 
apply (simp add: lt_def, blast) 
done

lemma (in M_triv_axioms) successor_ordinal_abs [simp]: 
     "M(a) ==> successor_ordinal(M,a) <-> Ord(a) & (\<exists>b[M]. a = succ(b))"
apply (simp add: successor_ordinal_def, safe)
apply (drule Ord_cases_disj, auto) 
done

lemma finite_Ord_is_nat:
      "[| Ord(a); ~ Limit(a); \<forall>x\<in>a. ~ Limit(x) |] ==> a \<in> nat"
by (induct a rule: trans_induct3, simp_all)

lemma naturals_not_limit: "a \<in> nat ==> ~ Limit(a)"
by (induct a rule: nat_induct, auto)

lemma (in M_triv_axioms) finite_ordinal_abs [simp]: 
     "M(a) ==> finite_ordinal(M,a) <-> a \<in> nat"
apply (simp add: finite_ordinal_def)
apply (blast intro: finite_Ord_is_nat intro: nat_into_Ord 
             dest: Ord_trans naturals_not_limit)
done

lemma Limit_non_Limit_implies_nat:
     "[| Limit(a); \<forall>x\<in>a. ~ Limit(x) |] ==> a = nat"
apply (rule le_anti_sym) 
apply (rule all_lt_imp_le, blast, blast intro: Limit_is_Ord)  
 apply (simp add: lt_def)  
 apply (blast intro: Ord_in_Ord Ord_trans finite_Ord_is_nat) 
apply (erule nat_le_Limit)
done

lemma (in M_triv_axioms) omega_abs [simp]: 
     "M(a) ==> omega(M,a) <-> a = nat"
apply (simp add: omega_def) 
apply (blast intro: Limit_non_Limit_implies_nat dest: naturals_not_limit)
done

lemma (in M_triv_axioms) number1_abs [simp]: 
     "M(a) ==> number1(M,a) <-> a = 1"
by (simp add: number1_def) 

lemma (in M_triv_axioms) number1_abs [simp]: 
     "M(a) ==> number2(M,a) <-> a = succ(1)"
by (simp add: number2_def) 

lemma (in M_triv_axioms) number3_abs [simp]: 
     "M(a) ==> number3(M,a) <-> a = succ(succ(1))"
by (simp add: number3_def) 

text{*Kunen continued to 20...*}

(*Could not get this to work.  The \<lambda>x\<in>nat is essential because everything 
  but the recursion variable must stay unchanged.  But then the recursion
  equations only hold for x\<in>nat (or in some other set) and not for the 
  whole of the class M.
  consts
    natnumber_aux :: "[i=>o,i] => i"

  primrec
      "natnumber_aux(M,0) = (\<lambda>x\<in>nat. if empty(M,x) then 1 else 0)"
      "natnumber_aux(M,succ(n)) = 
	   (\<lambda>x\<in>nat. if (\<exists>y[M]. natnumber_aux(M,n)`y=1 & successor(M,y,x)) 
		     then 1 else 0)"

  constdefs
    natnumber :: "[i=>o,i,i] => o"
      "natnumber(M,n,x) == natnumber_aux(M,n)`x = 1"

  lemma (in M_triv_axioms) [simp]: 
       "natnumber(M,0,x) == x=0"
*)

subsection{*Some instances of separation and strong replacement*}

locale M_axioms = M_triv_axioms +
assumes Inter_separation:
     "M(A) ==> separation(M, \<lambda>x. \<forall>y[M]. y\<in>A --> x\<in>y)"
  and cartprod_separation:
     "[| M(A); M(B) |] 
      ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. y\<in>B & pair(M,x,y,z)))"
  and image_separation:
     "[| M(A); M(r) |] 
      ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & (\<exists>x[M]. x\<in>A & pair(M,x,y,p)))"
  and converse_separation:
     "M(r) ==> separation(M, 
         \<lambda>z. \<exists>p[M]. p\<in>r & (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,p) & pair(M,y,x,z)))"
  and restrict_separation:
     "M(A) ==> separation(M, \<lambda>z. \<exists>x[M]. x\<in>A & (\<exists>y[M]. pair(M,x,y,z)))"
  and comp_separation:
     "[| M(r); M(s) |]
      ==> separation(M, \<lambda>xz. \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. \<exists>xy[M]. \<exists>yz[M]. 
		  pair(M,x,z,xz) & pair(M,x,y,xy) & pair(M,y,z,yz) & 
                  xy\<in>s & yz\<in>r)"
  and pred_separation:
     "[| M(r); M(x) |] ==> separation(M, \<lambda>y. \<exists>p[M]. p\<in>r & pair(M,y,x,p))"
  and Memrel_separation:
     "separation(M, \<lambda>z. \<exists>x[M]. \<exists>y[M]. pair(M,x,y,z) & x \<in> y)"
  and funspace_succ_replacement:
     "M(n) ==> 
      strong_replacement(M, \<lambda>p z. \<exists>f[M]. \<exists>b[M]. \<exists>nb[M]. \<exists>cnbf[M]. 
                pair(M,f,b,p) & pair(M,n,b,nb) & is_cons(M,nb,f,cnbf) &
                upair(M,cnbf,cnbf,z))"
  and well_ord_iso_separation:
     "[| M(A); M(f); M(r) |] 
      ==> separation (M, \<lambda>x. x\<in>A --> (\<exists>y[M]. (\<exists>p[M]. 
		     fun_apply(M,f,x,y) & pair(M,y,x,p) & p \<in> r)))"
  and obase_separation:
     --{*part of the order type formalization*}
     "[| M(A); M(r) |] 
      ==> separation(M, \<lambda>a. \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M]. 
	     ordinal(M,x) & membership(M,x,mx) & pred_set(M,A,a,r,par) &
	     order_isomorphism(M,par,r,x,mx,g))"
  and obase_equals_separation:
     "[| M(A); M(r) |] 
      ==> separation
      (M, \<lambda>x. x\<in>A --> ~(\<exists>y[M]. \<exists>g[M]. 
	      ordinal(M,y) & (\<exists>my[M]. \<exists>pxr[M]. 
	      membership(M,y,my) & pred_set(M,A,x,r,pxr) &
	      order_isomorphism(M,pxr,r,y,my,g))))"
  and omap_replacement:
     "[| M(A); M(r) |] 
      ==> strong_replacement(M,
             \<lambda>a z. \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M]. 
	     ordinal(M,x) & pair(M,a,x,z) & membership(M,x,mx) & 
	     pred_set(M,A,a,r,par) & order_isomorphism(M,par,r,x,mx,g))"
  and is_recfun_separation:
     --{*for well-founded recursion.  NEEDS RELATIVIZATION*}
     "[| M(A); M(f); M(g); M(a); M(b) |] 
     ==> separation(M, \<lambda>x. \<langle>x,a\<rangle> \<in> r & \<langle>x,b\<rangle> \<in> r & f`x \<noteq> g`x)"

lemma (in M_axioms) cartprod_iff_lemma:
     "[| M(C);  \<forall>u[M]. u \<in> C <-> (\<exists>x\<in>A. \<exists>y\<in>B. u = {{x}, {x,y}}); 
         powerset(M, A \<union> B, p1); powerset(M, p1, p2);  M(p2) |]
       ==> C = {u \<in> p2 . \<exists>x\<in>A. \<exists>y\<in>B. u = {{x}, {x,y}}}"
apply (simp add: powerset_def) 
apply (rule equalityI, clarify, simp)
 apply (frule transM, assumption) 
 apply (frule transM, assumption, simp) 
 apply blast 
apply clarify
apply (frule transM, assumption, force) 
done

lemma (in M_axioms) cartprod_iff:
     "[| M(A); M(B); M(C) |] 
      ==> cartprod(M,A,B,C) <-> 
          (\<exists>p1 p2. M(p1) & M(p2) & powerset(M,A Un B,p1) & powerset(M,p1,p2) &
                   C = {z \<in> p2. \<exists>x\<in>A. \<exists>y\<in>B. z = <x,y>})"
apply (simp add: Pair_def cartprod_def, safe)
defer 1 
  apply (simp add: powerset_def) 
 apply blast 
txt{*Final, difficult case: the left-to-right direction of the theorem.*}
apply (insert power_ax, simp add: power_ax_def) 
apply (frule_tac x="A Un B" and P="\<lambda>x. rex(M,?Q(x))" in rspec) 
apply (blast, clarify) 
apply (drule_tac x=z and P="\<lambda>x. rex(M,?Q(x))" in rspec)
apply assumption
apply (blast intro: cartprod_iff_lemma) 
done

lemma (in M_axioms) cartprod_closed_lemma:
     "[| M(A); M(B) |] ==> \<exists>C[M]. cartprod(M,A,B,C)"
apply (simp del: cartprod_abs add: cartprod_iff)
apply (insert power_ax, simp add: power_ax_def) 
apply (frule_tac x="A Un B" and P="\<lambda>x. rex(M,?Q(x))" in rspec) 
apply (blast, clarify) 
apply (drule_tac x=z and P="\<lambda>x. rex(M,?Q(x))" in rspec) 
apply (blast, clarify)
apply (intro rexI exI conjI) 
prefer 5 apply (rule refl) 
prefer 3 apply assumption
prefer 3 apply assumption
apply (insert cartprod_separation [of A B], auto)
done

text{*All the lemmas above are necessary because Powerset is not absolute.
      I should have used Replacement instead!*}
lemma (in M_axioms) cartprod_closed [intro,simp]: 
     "[| M(A); M(B) |] ==> M(A*B)"
by (frule cartprod_closed_lemma, assumption, force)

lemma (in M_axioms) sum_closed [intro,simp]: 
     "[| M(A); M(B) |] ==> M(A+B)"
by (simp add: sum_def)


subsubsection {*converse of a relation*}

lemma (in M_axioms) M_converse_iff:
     "M(r) ==> 
      converse(r) = 
      {z \<in> Union(Union(r)) * Union(Union(r)). 
       \<exists>p\<in>r. \<exists>x[M]. \<exists>y[M]. p = \<langle>x,y\<rangle> & z = \<langle>y,x\<rangle>}"
apply (rule equalityI)
 prefer 2 apply (blast dest: transM, clarify, simp) 
apply (simp add: Pair_def) 
apply (blast dest: transM) 
done

lemma (in M_axioms) converse_closed [intro,simp]: 
     "M(r) ==> M(converse(r))"
apply (simp add: M_converse_iff)
apply (insert converse_separation [of r], simp)
done

lemma (in M_axioms) converse_abs [simp]: 
     "[| M(r); M(z) |] ==> is_converse(M,r,z) <-> z = converse(r)"
apply (simp add: is_converse_def)
apply (rule iffI)
 prefer 2 apply blast 
apply (rule M_equalityI)
  apply simp
  apply (blast dest: transM)+
done


subsubsection {*image, preimage, domain, range*}

lemma (in M_axioms) image_closed [intro,simp]: 
     "[| M(A); M(r) |] ==> M(r``A)"
apply (simp add: image_iff_Collect)
apply (insert image_separation [of A r], simp) 
done

lemma (in M_axioms) vimage_abs [simp]: 
     "[| M(r); M(A); M(z) |] ==> pre_image(M,r,A,z) <-> z = r-``A"
apply (simp add: pre_image_def)
apply (rule iffI) 
 apply (blast intro!: equalityI dest: transM, blast) 
done

lemma (in M_axioms) vimage_closed [intro,simp]: 
     "[| M(A); M(r) |] ==> M(r-``A)"
by (simp add: vimage_def)


subsubsection{*Domain, range and field*}

lemma (in M_axioms) domain_abs [simp]: 
     "[| M(r); M(z) |] ==> is_domain(M,r,z) <-> z = domain(r)"
apply (simp add: is_domain_def) 
apply (blast intro!: equalityI dest: transM) 
done

lemma (in M_axioms) domain_closed [intro,simp]: 
     "M(r) ==> M(domain(r))"
apply (simp add: domain_eq_vimage)
done

lemma (in M_axioms) range_abs [simp]: 
     "[| M(r); M(z) |] ==> is_range(M,r,z) <-> z = range(r)"
apply (simp add: is_range_def)
apply (blast intro!: equalityI dest: transM)
done

lemma (in M_axioms) range_closed [intro,simp]: 
     "M(r) ==> M(range(r))"
apply (simp add: range_eq_image)
done

lemma (in M_axioms) field_abs [simp]: 
     "[| M(r); M(z) |] ==> is_field(M,r,z) <-> z = field(r)"
by (simp add: domain_closed range_closed is_field_def field_def)

lemma (in M_axioms) field_closed [intro,simp]: 
     "M(r) ==> M(field(r))"
by (simp add: domain_closed range_closed Un_closed field_def) 


subsubsection{*Relations, functions and application*}

lemma (in M_axioms) relation_abs [simp]: 
     "M(r) ==> is_relation(M,r) <-> relation(r)"
apply (simp add: is_relation_def relation_def) 
apply (blast dest!: bspec dest: pair_components_in_M)+
done

lemma (in M_axioms) function_abs [simp]: 
     "M(r) ==> is_function(M,r) <-> function(r)"
apply (simp add: is_function_def function_def, safe) 
   apply (frule transM, assumption) 
  apply (blast dest: pair_components_in_M)+
done

lemma (in M_axioms) apply_closed [intro,simp]: 
     "[|M(f); M(a)|] ==> M(f`a)"
by (simp add: apply_def)

lemma (in M_axioms) apply_abs: 
     "[| function(f); M(f); M(y) |] 
      ==> fun_apply(M,f,x,y) <-> x \<in> domain(f) & f`x = y"
apply (simp add: fun_apply_def)
apply (blast intro: function_apply_equality function_apply_Pair) 
done

lemma (in M_axioms) typed_apply_abs: 
     "[| f \<in> A -> B; M(f); M(y) |] 
      ==> fun_apply(M,f,x,y) <-> x \<in> A & f`x = y"
by (simp add: apply_abs fun_is_function domain_of_fun) 

lemma (in M_axioms) typed_function_abs [simp]: 
     "[| M(A); M(f) |] ==> typed_function(M,A,B,f) <-> f \<in> A -> B"
apply (auto simp add: typed_function_def relation_def Pi_iff) 
apply (blast dest: pair_components_in_M)+
done

lemma (in M_axioms) injection_abs [simp]: 
     "[| M(A); M(f) |] ==> injection(M,A,B,f) <-> f \<in> inj(A,B)"
apply (simp add: injection_def apply_iff inj_def apply_closed)
apply (blast dest: transM [of _ A]) 
done

lemma (in M_axioms) surjection_abs [simp]: 
     "[| M(A); M(B); M(f) |] ==> surjection(M,A,B,f) <-> f \<in> surj(A,B)"
by (simp add: typed_apply_abs surjection_def surj_def)

lemma (in M_axioms) bijection_abs [simp]: 
     "[| M(A); M(B); M(f) |] ==> bijection(M,A,B,f) <-> f \<in> bij(A,B)"
by (simp add: bijection_def bij_def)


subsubsection{*Composition of relations*}

lemma (in M_axioms) M_comp_iff:
     "[| M(r); M(s) |] 
      ==> r O s = 
          {xz \<in> domain(s) * range(r).  
            \<exists>x[M]. \<exists>y[M]. \<exists>z[M]. xz = \<langle>x,z\<rangle> & \<langle>x,y\<rangle> \<in> s & \<langle>y,z\<rangle> \<in> r}"
apply (simp add: comp_def)
apply (rule equalityI) 
 apply clarify 
 apply simp 
 apply  (blast dest:  transM)+
done

lemma (in M_axioms) comp_closed [intro,simp]: 
     "[| M(r); M(s) |] ==> M(r O s)"
apply (simp add: M_comp_iff)
apply (insert comp_separation [of r s], simp) 
done

lemma (in M_axioms) composition_abs [simp]: 
     "[| M(r); M(s); M(t) |] 
      ==> composition(M,r,s,t) <-> t = r O s"
apply safe
 txt{*Proving @{term "composition(M, r, s, r O s)"}*}
 prefer 2 
 apply (simp add: composition_def comp_def)
 apply (blast dest: transM) 
txt{*Opposite implication*}
apply (rule M_equalityI)
  apply (simp add: composition_def comp_def)
  apply (blast del: allE dest: transM)+
done

text{*no longer needed*}
lemma (in M_axioms) restriction_is_function: 
     "[| restriction(M,f,A,z); function(f); M(f); M(A); M(z) |] 
      ==> function(z)"
apply (rotate_tac 1)
apply (simp add: restriction_def ball_iff_equiv) 
apply (unfold function_def, blast) 
done

lemma (in M_axioms) restriction_abs [simp]: 
     "[| M(f); M(A); M(z) |] 
      ==> restriction(M,f,A,z) <-> z = restrict(f,A)"
apply (simp add: ball_iff_equiv restriction_def restrict_def)
apply (blast intro!: equalityI dest: transM) 
done


lemma (in M_axioms) M_restrict_iff:
     "M(r) ==> restrict(r,A) = {z \<in> r . \<exists>x\<in>A. \<exists>y[M]. z = \<langle>x, y\<rangle>}"
by (simp add: restrict_def, blast dest: transM)

lemma (in M_axioms) restrict_closed [intro,simp]: 
     "[| M(A); M(r) |] ==> M(restrict(r,A))"
apply (simp add: M_restrict_iff)
apply (insert restrict_separation [of A], simp) 
done

lemma (in M_axioms) Inter_abs [simp]: 
     "[| M(A); M(z) |] ==> big_inter(M,A,z) <-> z = Inter(A)"
apply (simp add: big_inter_def Inter_def) 
apply (blast intro!: equalityI dest: transM) 
done

lemma (in M_axioms) Inter_closed [intro,simp]:
     "M(A) ==> M(Inter(A))"
by (insert Inter_separation, simp add: Inter_def)

lemma (in M_axioms) Int_closed [intro,simp]:
     "[| M(A); M(B) |] ==> M(A Int B)"
apply (subgoal_tac "M({A,B})")
apply (frule Inter_closed, force+) 
done

subsubsection{*Functions and function space*}

text{*M contains all finite functions*}
lemma (in M_axioms) finite_fun_closed_lemma [rule_format]: 
     "[| n \<in> nat; M(A) |] ==> \<forall>f \<in> n -> A. M(f)"
apply (induct_tac n, simp)
apply (rule ballI)  
apply (simp add: succ_def) 
apply (frule fun_cons_restrict_eq)
apply (erule ssubst) 
apply (subgoal_tac "M(f`x) & restrict(f,x) \<in> x -> A") 
 apply (simp add: cons_closed nat_into_M apply_closed) 
apply (blast intro: apply_funtype transM restrict_type2) 
done

lemma (in M_axioms) finite_fun_closed [rule_format]: 
     "[| f \<in> n -> A; n \<in> nat; M(A) |] ==> M(f)"
by (blast intro: finite_fun_closed_lemma) 

text{*The assumption @{term "M(A->B)"} is unusual, but essential: in 
all but trivial cases, A->B cannot be expected to belong to @{term M}.*}
lemma (in M_axioms) is_funspace_abs [simp]:
     "[|M(A); M(B); M(F); M(A->B)|] ==> is_funspace(M,A,B,F) <-> F = A->B";
apply (simp add: is_funspace_def)
apply (rule iffI)
 prefer 2 apply blast 
apply (rule M_equalityI)
  apply simp_all
done

lemma (in M_axioms) succ_fun_eq2:
     "[|M(B); M(n->B)|] ==>
      succ(n) -> B = 
      \<Union>{z. p \<in> (n->B)*B, \<exists>f[M]. \<exists>b[M]. p = <f,b> & z = {cons(<n,b>, f)}}"
apply (simp add: succ_fun_eq)
apply (blast dest: transM)  
done

lemma (in M_axioms) funspace_succ:
     "[|M(n); M(B); M(n->B) |] ==> M(succ(n) -> B)"
apply (insert funspace_succ_replacement [of n], simp) 
apply (force simp add: succ_fun_eq2 univalent_def) 
done

text{*@{term M} contains all finite function spaces.  Needed to prove the
absoluteness of transitive closure.*}
lemma (in M_axioms) finite_funspace_closed [intro,simp]:
     "[|n\<in>nat; M(B)|] ==> M(n->B)"
apply (induct_tac n, simp)
apply (simp add: funspace_succ nat_into_M) 
done

end
