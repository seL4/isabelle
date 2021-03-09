theory Confluent_Quotient imports
  Confluence
begin

text \<open>Functors with finite setters preserve wide intersection for any equivalence relation that respects the mapper.\<close>

lemma Inter_finite_subset:
  assumes "\<forall>A \<in> \<A>. finite A"
  shows "\<exists>\<B>\<subseteq>\<A>. finite \<B> \<and> (\<Inter>\<B>) = (\<Inter>\<A>)"
proof(cases "\<A> = {}")
  case False
  then obtain A where A: "A \<in> \<A>" by auto
  then have finA: "finite A" using assms by auto
  hence fin: "finite (A - \<Inter>\<A>)" by(rule finite_subset[rotated]) auto
  let ?P = "\<lambda>x A. A \<in> \<A> \<and> x \<notin> A"
  define f where "f x = Eps (?P x)" for x
  let ?\<B> = "insert A (f ` (A - \<Inter>\<A>))"
  have "?P x (f x)" if "x \<in> A - \<Inter>\<A>" for x unfolding f_def by(rule someI_ex)(use that A in auto)
  hence "(\<Inter>?\<B>) = (\<Inter>\<A>)" "?\<B> \<subseteq> \<A>" using A by auto
  moreover have "finite ?\<B>" using fin by simp
  ultimately show ?thesis by blast
qed simp

locale wide_intersection_finite =
  fixes E :: "'Fa \<Rightarrow> 'Fa \<Rightarrow> bool"
    and mapFa :: "('a \<Rightarrow> 'a) \<Rightarrow> 'Fa \<Rightarrow> 'Fa"
    and setFa :: "'Fa \<Rightarrow> 'a set"
  assumes equiv: "equivp E"
    and map_E: "E x y \<Longrightarrow> E (mapFa f x) (mapFa f y)"
    and map_id: "mapFa id x = x"
    and map_cong: "\<forall>a\<in>setFa x. f a = g a \<Longrightarrow> mapFa f x = mapFa g x"
    and set_map: "setFa (mapFa f x) = f ` setFa x"
    and finite: "finite (setFa x)"
begin

lemma binary_intersection:
  assumes "E y z" and y: "setFa y \<subseteq> Y" and z: "setFa z \<subseteq> Z" and a: "a \<in> Y" "a \<in> Z"
  shows "\<exists>x. E x y \<and> setFa x \<subseteq> Y \<and> setFa x \<subseteq> Z"
proof -
  let ?f = "\<lambda>b. if b \<in> Z then b else a"
  let ?u = "mapFa ?f y"
  from \<open>E y z\<close> have "E ?u (mapFa ?f z)" by(rule map_E)
  also have "mapFa ?f z = mapFa id z" by(rule map_cong)(use z in auto)
  also have "\<dots> = z" by(rule map_id)
  finally have "E ?u y" using \<open>E y z\<close> equivp_symp[OF equiv] equivp_transp[OF equiv] by blast
  moreover have "setFa ?u \<subseteq> Y" using a y by(subst set_map) auto
  moreover have "setFa ?u \<subseteq> Z" using a by(subst set_map) auto
  ultimately show ?thesis by blast
qed

lemma finite_intersection:
  assumes E: "\<forall>y\<in>A. E y z"
    and fin: "finite A"
    and sub: "\<forall>y\<in>A. setFa y \<subseteq> Y y \<and> a \<in> Y y"
  shows "\<exists>x. E x z \<and> (\<forall>y\<in>A. setFa x \<subseteq> Y y)"
  using fin E sub
proof(induction)
  case empty
  then show ?case using equivp_reflp[OF equiv, of z] by(auto)
next
  case (insert y A)
  then obtain x where x: "E x z" "\<forall>y\<in>A. setFa x \<subseteq> Y y \<and> a \<in> Y y" by auto
  hence set_x: "setFa x \<subseteq> (\<Inter>y\<in>A. Y y)" "a \<in> (\<Inter>y\<in>A. Y y)" by auto
  from insert.prems have "E y z" and set_y: "setFa y \<subseteq> Y y" "a \<in> Y y" by auto
  from \<open>E y z\<close> \<open>E x z\<close> have "E x y" using equivp_symp[OF equiv] equivp_transp[OF equiv] by blast
  from binary_intersection[OF this set_x(1) set_y(1) set_x(2) set_y(2)]
  obtain x' where "E x' x" "setFa x' \<subseteq> \<Inter> (Y ` A)" "setFa x' \<subseteq> Y y" by blast
  then show ?case using \<open>E x z\<close> equivp_transp[OF equiv] by blast
qed

lemma wide_intersection:
  assumes inter_nonempty: "\<Inter> Ss \<noteq> {}"
  shows "(\<Inter>As \<in> Ss. {(x, x'). E x x'} `` {x. setFa x \<subseteq> As}) \<subseteq> {(x, x'). E x x'} `` {x. setFa x \<subseteq> \<Inter> Ss}" (is "?lhs \<subseteq> ?rhs")
proof
  fix x
  assume lhs: "x \<in> ?lhs"
  from inter_nonempty obtain a where a: "\<forall>As \<in> Ss. a \<in> As" by auto
  from lhs obtain y where y: "\<And>As. As \<in> Ss \<Longrightarrow> E (y As) x \<and> setFa (y As) \<subseteq> As"
    by atomize_elim(rule choice, auto)
  define Ts where "Ts = (\<lambda>As. insert a (setFa (y As))) ` Ss"
  have Ts_subset: "(\<Inter>Ts) \<subseteq> (\<Inter>Ss)" using a unfolding Ts_def by(auto dest: y)
  have Ts_finite: "\<forall>Bs \<in> Ts. finite Bs" unfolding Ts_def by(auto dest: y intro: finite)
  from Inter_finite_subset[OF this] obtain Us
    where Us: "Us \<subseteq> Ts" and finite_Us: "finite Us" and Int_Us: "(\<Inter>Us) \<subseteq> (\<Inter>Ts)" by force
  let ?P = "\<lambda>U As. As \<in> Ss \<and> U = insert a (setFa (y As))"
  define Y where "Y U = Eps (?P U)" for U
  have Y: "?P U (Y U)" if "U \<in> Us" for U unfolding Y_def
    by(rule someI_ex)(use that Us in \<open>auto simp add: Ts_def\<close>)
  let ?f = "\<lambda>U. y (Y U)"
  have *: "\<forall>z\<in>(?f ` Us). E z x" by(auto dest!: Y y)
  have **: "\<forall>z\<in>(?f ` Us). setFa z \<subseteq> insert a (setFa z) \<and> a \<in> insert a (setFa z)" by auto
  from finite_intersection[OF * _ **] finite_Us obtain u
    where u: "E u x" and set_u: "\<forall>z\<in>(?f ` Us). setFa u \<subseteq> insert a (setFa z)" by auto
  from set_u have "setFa u \<subseteq> (\<Inter> Us)" by(auto dest: Y)
  with Int_Us Ts_subset have "setFa u \<subseteq> (\<Inter> Ss)" by auto
  with u show "x \<in> ?rhs" by auto
qed

end

text \<open>Subdistributivity for quotients via confluence\<close>

lemma rtranclp_transp_reflp: "R\<^sup>*\<^sup>* = R" if "transp R" "reflp R"
  apply(rule ext iffI)+
  subgoal premises prems for x y using prems by(induction)(use that in \<open>auto intro: reflpD transpD\<close>)
  subgoal by(rule r_into_rtranclp)
  done

lemma rtranclp_equivp: "R\<^sup>*\<^sup>* = R" if "equivp R"
  using that by(simp add: rtranclp_transp_reflp equivp_reflp_symp_transp)

locale confluent_quotient =
  fixes Rb :: "'Fb \<Rightarrow> 'Fb \<Rightarrow> bool"
    and Ea :: "'Fa \<Rightarrow> 'Fa \<Rightarrow> bool"
    and Eb :: "'Fb \<Rightarrow> 'Fb \<Rightarrow> bool"
    and Ec :: "'Fc \<Rightarrow> 'Fc \<Rightarrow> bool"
    and Eab :: "'Fab \<Rightarrow> 'Fab \<Rightarrow> bool"
    and Ebc :: "'Fbc \<Rightarrow> 'Fbc \<Rightarrow> bool"
    and \<pi>_Faba :: "'Fab \<Rightarrow> 'Fa"
    and \<pi>_Fabb :: "'Fab \<Rightarrow> 'Fb"
    and \<pi>_Fbcb :: "'Fbc \<Rightarrow> 'Fb"
    and \<pi>_Fbcc :: "'Fbc \<Rightarrow> 'Fc"
    and rel_Fab :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'Fa \<Rightarrow> 'Fb \<Rightarrow> bool"
    and rel_Fbc :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'Fb \<Rightarrow> 'Fc \<Rightarrow> bool"
    and rel_Fac :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'Fa \<Rightarrow> 'Fc \<Rightarrow> bool"
    and set_Fab :: "'Fab \<Rightarrow> ('a \<times> 'b) set"
    and set_Fbc :: "'Fbc \<Rightarrow> ('b \<times> 'c) set"
  assumes confluent: "confluentp Rb"
    and retract1_ab: "\<And>x y. Rb (\<pi>_Fabb x) y \<Longrightarrow> \<exists>z. Eab x z \<and> y = \<pi>_Fabb z \<and> set_Fab z \<subseteq> set_Fab x"
    and retract1_bc: "\<And>x y. Rb (\<pi>_Fbcb x) y \<Longrightarrow> \<exists>z. Ebc x z \<and> y = \<pi>_Fbcb z \<and> set_Fbc z \<subseteq> set_Fbc x"
    and generated_b: "Eb \<le> equivclp Rb"
    and transp_a: "transp Ea"
    and transp_c: "transp Ec"
    and equivp_ab: "equivp Eab"
    and equivp_bc: "equivp Ebc"
    and in_rel_Fab: "\<And>A x y. rel_Fab A x y \<longleftrightarrow> (\<exists>z. z \<in> {x. set_Fab x \<subseteq> {(x, y). A x y}} \<and> \<pi>_Faba z = x \<and> \<pi>_Fabb z = y)"
    and in_rel_Fbc: "\<And>B x y. rel_Fbc B x y \<longleftrightarrow> (\<exists>z. z \<in> {x. set_Fbc x \<subseteq> {(x, y). B x y}} \<and> \<pi>_Fbcb z = x \<and> \<pi>_Fbcc z = y)"
    and rel_compp: "\<And>A B. rel_Fac (A OO B) = rel_Fab A OO rel_Fbc B"
    and \<pi>_Faba_respect: "rel_fun Eab Ea \<pi>_Faba \<pi>_Faba"
    and \<pi>_Fbcc_respect: "rel_fun Ebc Ec \<pi>_Fbcc \<pi>_Fbcc"
begin

lemma retract_ab: "Rb\<^sup>*\<^sup>* (\<pi>_Fabb x) y \<Longrightarrow> \<exists>z. Eab x z \<and> y = \<pi>_Fabb z \<and> set_Fab z \<subseteq> set_Fab x"
  by(induction rule: rtranclp_induct)(blast dest: retract1_ab intro: equivp_transp[OF equivp_ab] equivp_reflp[OF equivp_ab])+

lemma retract_bc: "Rb\<^sup>*\<^sup>* (\<pi>_Fbcb x) y \<Longrightarrow> \<exists>z. Ebc x z \<and> y = \<pi>_Fbcb z \<and> set_Fbc z \<subseteq> set_Fbc x"
  by(induction rule: rtranclp_induct)(blast dest: retract1_bc intro: equivp_transp[OF equivp_bc] equivp_reflp[OF equivp_bc])+

lemma subdistributivity: "rel_Fab A OO Eb OO rel_Fbc B \<le> Ea OO rel_Fac (A OO B) OO Ec"
proof(rule predicate2I; elim relcomppE)
  fix x y y' z
  assume "rel_Fab A x y" and "Eb y y'" and "rel_Fbc B y' z"
  then obtain xy y'z
    where xy: "set_Fab xy \<subseteq> {(a, b). A a b}" "x = \<pi>_Faba xy" "y = \<pi>_Fabb xy"
      and y'z: "set_Fbc y'z \<subseteq> {(a, b). B a b}" "y' = \<pi>_Fbcb y'z" "z = \<pi>_Fbcc y'z"
    by(auto simp add: in_rel_Fab in_rel_Fbc)
  from \<open>Eb y y'\<close> have "equivclp Rb y y'" using generated_b by blast
  then obtain u where u: "Rb\<^sup>*\<^sup>* y u" "Rb\<^sup>*\<^sup>* y' u"
    unfolding semiconfluentp_equivclp[OF confluent[THEN confluentp_imp_semiconfluentp]]
    by(auto simp add: rtranclp_conversep)
  with xy y'z obtain xy' y'z'
    where retract1: "Eab xy xy'" "\<pi>_Fabb xy' = u" "set_Fab xy' \<subseteq> set_Fab xy"
      and retract2: "Ebc y'z y'z'" "\<pi>_Fbcb y'z' = u" "set_Fbc y'z' \<subseteq> set_Fbc y'z"
    by(auto dest!: retract_ab retract_bc)
  from retract1(1) xy have "Ea x (\<pi>_Faba xy')" by(auto dest: \<pi>_Faba_respect[THEN rel_funD])
  moreover have "rel_Fab A (\<pi>_Faba xy') u" using xy retract1 by(auto simp add: in_rel_Fab)
  moreover have "rel_Fbc B u (\<pi>_Fbcc y'z')" using y'z retract2 by(auto simp add: in_rel_Fbc)
  moreover have "Ec (\<pi>_Fbcc y'z') z" using retract2 y'z equivp_symp[OF equivp_bc]
    by(auto intro: \<pi>_Fbcc_respect[THEN rel_funD])
  ultimately show "(Ea OO rel_Fac (A OO B) OO Ec) x z" unfolding rel_compp by blast
qed

end

end