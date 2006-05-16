(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Ferrante and Rackoff Algorithm: LCF-proof-synthesis version.
*)

theory Ferrante_Rackoff
imports RealPow
uses ("ferrante_rackoff_proof.ML") ("ferrante_rackoff.ML")
begin

  (* Synthesis of \<exists>z. \<forall>x<z. P x = P1 *)
lemma minf: 
  "\<exists>(z::real) . \<forall>x<z. x < t = True "  "\<exists>(z::real) . \<forall>x<z. x > t = False "
  "\<exists>(z::real) . \<forall>x<z. x \<le> t = True "  "\<exists>(z::real) . \<forall>x<z. x \<ge> t = False "
  "\<exists>(z::real) . \<forall>x<z. (x = t) = False "  "\<exists>(z::real) . \<forall>x<z. (x \<noteq> t) = True "
  "\<exists>z. \<forall>(x::real)<z. (P::bool) = P"
  "\<lbrakk>\<exists>(z1::real). \<forall>x<z1. P1 x = P1'; \<exists>z2. \<forall>x<z2. P2 x = P2'\<rbrakk> \<Longrightarrow>
  \<exists>z. \<forall>x<z. (P1 x \<and> P2 x) = (P1' \<and> P2')"
  "\<lbrakk>\<exists>(z1::real). \<forall>x<z1. P1 x = P1'; \<exists>z2. \<forall>x<z2. P2 x = P2'\<rbrakk> \<Longrightarrow>
  \<exists>z. \<forall>x<z. (P1 x \<or> P2 x) = (P1' \<or> P2')"
  by (rule_tac x="t" in exI,simp)+
(clarsimp,rule_tac x="min z1 z2" in exI,simp)+

lemma minf_ex: "\<lbrakk>\<exists>z. \<forall>x<z. P (x::real) = P1 ; P1\<rbrakk> \<Longrightarrow> \<exists> x. P x"
  by clarsimp (rule_tac x="z - 1" in exI, auto)

  (* Synthesis of \<exists>z. \<forall>x>z. P x = P1 *)
lemma pinf: 
  "\<exists>(z::real) . \<forall>x>z. x < t = False "  "\<exists>(z::real) . \<forall>x>z. x > t = True "
  "\<exists>(z::real) . \<forall>x>z. x \<le> t = False "  "\<exists>(z::real) . \<forall>x>z. x \<ge> t = True "
  "\<exists>(z::real) . \<forall>x>z. (x = t) = False "  "\<exists>(z::real) . \<forall>x>z. (x \<noteq> t) = True "
  "\<exists>z. \<forall>(x::real)>z. (P::bool) = P"
  "\<lbrakk>\<exists>(z1::real). \<forall>x>z1. P1 x = P1'; \<exists>z2. \<forall>x>z2. P2 x = P2'\<rbrakk> \<Longrightarrow>
  \<exists>z. \<forall>x>z. (P1 x \<and> P2 x) = (P1' \<and> P2')"
  "\<lbrakk>\<exists>(z1::real). \<forall>x>z1. P1 x = P1'; \<exists>z2. \<forall>x>z2. P2 x = P2'\<rbrakk> \<Longrightarrow>
  \<exists>z. \<forall>x>z. (P1 x \<or> P2 x) = (P1' \<or> P2')"
  by (rule_tac x="t" in exI,simp)+
(clarsimp,rule_tac x="max z1 z2" in exI,simp)+

lemma pinf_ex: "\<lbrakk>\<exists>z. \<forall>x>z. P (x::real) = P1 ; P1\<rbrakk> \<Longrightarrow> \<exists> x. P x"
  by clarsimp (rule_tac x="z+1" in exI, auto)

    (* The ~P1 \<and> ~P2 \<and> P x \<longrightarrow> \<exists> u,u' \<in> U. u \<le> x \<le> u'*)
lemma nmilbnd: 
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> (x::real) < t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> (x::real) > t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> (x::real) \<le> t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> (x::real) \<ge> t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  (x::real) = t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "t \<in> U \<Longrightarrow>\<forall>x. \<not>True \<and> (x::real) \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. u \<le> x )"
  "\<forall> (x::real). ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. u \<le> x )"
  "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 (x::real) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x) ; 
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x )\<rbrakk> \<Longrightarrow> 
  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 (x::real) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x) ; 
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<le> x )\<rbrakk> \<Longrightarrow> 
  \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<le> x)"
  by auto (rule_tac x="t" in bexI,simp,simp)

lemma npiubnd: 
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  (x::real) < t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> (x::real) > t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  (x::real) \<le> t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> (x::real) \<ge> t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  (x::real) = t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> (x::real) \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x )"
  "\<forall> (x::real). ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x )"
  "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 (x::real) \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x) ;  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x )\<rbrakk> 
  \<Longrightarrow>  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 (x::real) \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x) ; \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x )\<rbrakk> 
  \<Longrightarrow> \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<ge> x)"
  by auto (rule_tac x="t" in bexI,simp,simp)
lemma npmibnd: "\<lbrakk>\<forall>x. \<not> MP \<and> P (x::real) \<longrightarrow> (\<exists> u\<in> U. u \<le> x); \<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<ge> x)\<rbrakk> 
  \<Longrightarrow> \<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<le> x \<and> x \<le> u')"
by auto

  (* Synthesis of  (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x<u \<and> P x \<and> l < y < u \<longrightarrow> P y*)
lemma lin_dense_lt: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) < t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y< t)"
proof(clarsimp)
  fix x l u y  assume tU: "t \<in> U" and noU: "\<forall>t\<Colon>real. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" 
    and xu: "x<u"  and px: "x < t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y> t" hence "l < t \<and> t < u" using px lx yu by simp 
    with tU noU have "False" by auto} hence "\<not> y>t"  by auto hence "y \<le> t" by auto
  thus "y < t" using tny by simp 
qed
    
lemma lin_dense_gt: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) > t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y> t)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t\<Colon>real. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "x > t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y< t" hence "l < t \<and> t < u" using px xu ly by simp 
    with tU noU have "False" by auto}
  hence	"\<not> y<t"  by auto hence "y \<ge> t" by auto
  thus "y > t" using tny by simp 
qed
lemma lin_dense_le: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) \<le> t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y\<le> t)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t\<Colon>real. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "x \<le> t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y> t" hence "l < t \<and> t < u" using px lx yu by simp 
    with tU noU have "False" by auto}
  hence	"\<not> y>t"  by auto thus "y \<le> t" by auto
qed
    
lemma lin_dense_ge: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) \<ge> t \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y\<ge> t)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t\<Colon>real. l < t \<and> t < u \<longrightarrow> t \<notin> U" and lx: "l < x" and xu: "x<u"
  and px: "x \<ge> t" and ly: "l<y" and yu:"y < u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y< t" hence "l < t \<and> t < u" using px xu ly by simp 
    with tU noU have "False" by auto}
  hence	"\<not> y<t"  by auto thus "y \<ge> t" by auto
qed
lemma lin_dense_eq: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) = t   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y= t)"  by auto
lemma lin_dense_neq: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (x::real) \<noteq> t   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> y\<noteq> t)"  by auto
lemma lin_dense_fm: "\<forall>(x::real) l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P)"  by auto

lemma lin_dense_conj: 
  "\<lbrakk>\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P1 (x::real) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P1 y) ;  
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P2 (x::real) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow> 
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (P1 x \<and> P2 x) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> (P1 y \<and> P2 y))"
  by blast
lemma lin_dense_disj: 
  "\<lbrakk>\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P1 (x::real) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P1 y) ;  
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P2 (x::real) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow> 
  \<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> (P1 x \<or> P2 x) 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> (P1 y \<or> P2 y))"
  by blast

lemma finite_set_intervals:
  assumes px: "P (x::real)" and lx: "l \<le> x" and xu: "x \<le> u" and linS: "l\<in> S" 
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<le> x" and Su: "\<forall> x\<in> S. x \<le> u"
  shows "\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a \<le> x \<and> x \<le> b \<and> P x"
proof-
  let ?Mx = "{y. y\<in> S \<and> y \<le> x}"
  let ?xM = "{y. y\<in> S \<and> x \<le> y}"
  let ?a = "Max ?Mx"
  let ?b = "Min ?xM"
  have MxS: "?Mx \<subseteq> S" by blast
  hence fMx: "finite ?Mx" using fS finite_subset by auto
  from lx linS have linMx: "l \<in> ?Mx" by blast
  hence Mxne: "?Mx \<noteq> {}" by blast
  have xMS: "?xM \<subseteq> S" by blast
  hence fxM: "finite ?xM" using fS finite_subset by auto
  from xu uinS have linxM: "u \<in> ?xM" by blast
  hence xMne: "?xM \<noteq> {}" by blast
  have ax:"?a \<le> x" using Mxne fMx by auto
  have xb:"x \<le> ?b" using xMne fxM by auto
  have "?a \<in> ?Mx" using Max_in[OF fMx Mxne] by simp hence ainS: "?a \<in> S" using MxS by blast
  have "?b \<in> ?xM" using Min_in[OF fxM xMne] by simp hence binS: "?b \<in> S" using xMS by blast
  have noy:"\<forall> y. ?a < y \<and> y < ?b \<longrightarrow> y \<notin> S"
  proof(clarsimp)
    fix y   assume ay: "?a < y" and yb: "y < ?b" and yS: "y \<in> S"
    from yS have "y\<in> ?Mx \<or> y\<in> ?xM" by auto
    moreover {assume "y \<in> ?Mx" hence "y \<le> ?a" using Mxne fMx by auto with ay have "False" by simp}
    moreover {assume "y \<in> ?xM" hence "y \<ge> ?b" using xMne fxM by auto with yb have "False" by simp}
    ultimately show "False" by blast
  qed
  from ainS binS noy ax xb px show ?thesis by blast
qed

lemma finite_set_intervals2:
  assumes px: "P (x::real)" and lx: "l \<le> x" and xu: "x \<le> u" and linS: "l\<in> S" 
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<le> x" and Su: "\<forall> x\<in> S. x \<le> u"
  shows "(\<exists> s\<in> S. P s) \<or> (\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a < x \<and> x < b \<and> P x)"
proof-
  from finite_set_intervals[where P="P", OF px lx xu linS uinS fS lS Su]
  obtain a and b where 
    as: "a\<in> S" and bs: "b\<in> S" and noS:"\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S" 
    and axb: "a \<le> x \<and> x \<le> b \<and> P x"  by auto
  from axb have "x= a \<or> x= b \<or> (a < x \<and> x < b)" by auto
  thus ?thesis using px as bs noS by blast 
qed

lemma rinf_U:
  assumes fU: "finite U" 
  and lin_dense: "\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P x 
  \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P y )"
  and nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<le> x \<and> x \<le> u')"
  and nmi: "\<not> MP"  and npi: "\<not> PP"  and ex: "\<exists> x.  P (x::real)"
  shows "\<exists> u\<in> U. \<exists> u' \<in> U. P ((u + u') / 2)" 
proof-
  from ex obtain x where px: "P x" by blast
  from px nmi npi nmpiU have "\<exists> u\<in> U. \<exists> u' \<in> U. u \<le> x \<and> x \<le> u'" by auto
  then obtain u and u' where uU:"u\<in> U" and uU': "u' \<in> U" and ux:"u \<le> x" and xu':"x \<le> u'" by auto 
  from uU have Une: "U \<noteq> {}" by auto
  let ?l = "Min U"
  let ?u = "Max U"
  have linM: "?l \<in> U" using fU Une by simp
  have uinM: "?u \<in> U" using fU Une by simp
  have lM: "\<forall> t\<in> U. ?l \<le> t" using Une fU by auto
  have Mu: "\<forall> t\<in> U. t \<le> ?u" using Une fU by auto
  have "?l \<le> u" using uU Une lM by auto hence lx: "?l \<le> x" using ux by simp
  have "u' \<le> ?u" using uU' Une Mu by simp hence xu: "x \<le> ?u" using xu' by simp
  from finite_set_intervals2[where P="P",OF px lx xu linM uinM fU lM Mu]
  have "(\<exists> s\<in> U. P s) \<or> 
      (\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> U) \<and> t1 < x \<and> x < t2 \<and> P x)" .
  moreover { fix u assume um: "u\<in>U" and pu: "P u"
    have "(u + u) / 2 = u" by auto 
    with um pu have "P ((u + u) / 2)" by simp
    with um have ?thesis by blast}
  moreover{
    assume "\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> U) \<and> t1 < x \<and> x < t2 \<and> P x"
      then obtain t1 and t2 where t1M: "t1 \<in> U" and t2M: "t2\<in> U" 
	and noM: "\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> U" and t1x: "t1 < x" and xt2: "x < t2" and px: "P x"
	by blast
      from t1x xt2 have t1t2: "t1 < t2" by simp
      let ?u = "(t1 + t2) / 2"
      from less_half_sum[OF t1t2] gt_half_sum[OF t1t2] have t1lu: "t1 < ?u" and ut2: "?u < t2" by auto
      from lin_dense[rule_format, OF] noM t1x xt2 px t1lu ut2 have "P ?u" by blast
      with t1M t2M have ?thesis by blast}
    ultimately show ?thesis by blast
  qed

theorem fr_eq: 
  assumes fU: "finite U"
  and lin_dense: "\<forall>x l u. (\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> U) \<and> l< x \<and> x < u \<and> P x 
   \<longrightarrow> (\<forall> y. l < y \<and> y < u \<longrightarrow> P y )"
  and nmibnd: "\<forall>x. \<not> MP \<and> P (x::real) \<longrightarrow> (\<exists> u\<in> U. u \<le> x)"
  and npibnd: "\<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<ge> x)"
  and mi: "\<exists>z. \<forall>x<z. P x = MP"  and pi: "\<exists>z. \<forall>x>z. P x = PP"
  shows "(\<exists> x. P (x::real)) = (MP \<or> PP \<or> (\<exists> u \<in> U. \<exists> u'\<in> U. P ((u + u') / 2)))" 
  (is "_ = (_ \<or> _ \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists> x. P x"
  have "MP \<or> PP \<or> (\<not> MP \<and> \<not> PP)" by blast
  moreover {assume "MP \<or> PP" hence "?D" by blast}
  moreover {assume nmi: "\<not> MP" and npi: "\<not> PP"
    from npmibnd[OF nmibnd npibnd] 
    have nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<le> x \<and> x \<le> u')" .
    from rinf_U[OF fU lin_dense nmpiU nmi npi px] have "?D" by blast}   
  ultimately show "?D" by blast
next
  assume "?D" 
  moreover {assume m:"MP" from minf_ex[OF mi m] have "?E" .}
  moreover {assume p: "PP" from pinf_ex[OF pi p] have "?E" . }
  moreover {assume f:"?F" hence "?E" by blast}
  ultimately show "?E" by blast
qed

lemma fr_simps: 
  "(True | P) = True"  "(P | True) = True"  "(True & P) = P"  "(P & True) = P"
  "(P & P) = P"  "(P & (P & P')) = (P & P')"  "(P & (P | P')) = P"  "(False | P) = P"
  "(P | False) = P"  "(False & P) = False"  "(P & False) = False"  "(P | P) = P"
  "(P | (P | P')) = (P | P')"  "(P | (P & P')) = P"  "(~ True) = False"  "(~ False) = True"
  "(x::real) \<le> x"  "(\<exists> u\<in> {}. Q u) = False"
  "(\<exists> u\<in> (insert (x::real) U). \<exists>u'\<in> (insert x U). R ((u+u') / 2)) = 
  ((R x) \<or> (\<exists>u\<in>U. R((x+u) / 2))\<or> (\<exists> u\<in> U. \<exists> u'\<in> U. R ((u + u') /2)))"
  "(\<exists> u\<in> (insert (x::real) U). R u) = (R x \<or> (\<exists> u\<in> U. R u))"
  "Q' (((t::real) + t)/2) = Q' t"
by (auto simp add: add_ac)
  
lemma fr_prepqelim:
  "(\<exists> x. True) = True" "(\<exists> x. False) = False" "(ALL x. A x) = (~ (EX x. ~ (A x)))"
  "(P \<longrightarrow> Q) = ((\<not> P) \<or> Q)" "(\<not> (P \<longrightarrow> Q)) = (P \<and> (\<not> Q))" "(\<not> (P = Q)) = ((\<not> P) = Q)" 
  "(\<not> (P \<and> Q)) = ((\<not> P) \<or> (\<not> Q))" "(\<not> (P \<or> Q)) = ((\<not> P) \<and> (\<not> Q))"
by auto
  (* Lemmas for the normalization of Expressions *)
lemma nadd_cong:  
  assumes m: "m'*m = l" and n: "n'*n = (l::real)"
  and mz: "m \<noteq> 0" and nz: "n \<noteq> 0" and lz: "l \<noteq> 0"
  and ad: "(m'*t + n'*s) = t'"
  shows "t/m + s/n = (t' / l)"
proof-
  from lz m n have mz': "m'\<noteq>0" and nz':"n' \<noteq> 0" by auto
  have "t' / l = (m'*t + n'*s) / l" using ad by simp
  also have "\<dots> = (m'*t) / l + (n'*s) / l" by (simp add: add_divide_distrib)
  also have "\<dots> = (m'*t) /(m'*m) + (n'*s) /(n'*n)" using m n by simp
  also have "\<dots> = t/m + s/n" using mz nz mz' nz' by simp
  finally show ?thesis  by simp
qed

lemma nadd_cong_same: "\<lbrakk> (n::real) = m ; t+s = t'\<rbrakk> \<Longrightarrow> t/n + s/m = t'/n"  
  by (simp add: add_divide_distrib[symmetric])
lemma plus_cong: "\<lbrakk>t = t'; s = s'; t' + s' = r\<rbrakk> \<Longrightarrow> t+s = r"
  by simp
lemma diff_cong: "\<lbrakk>t = t'; s = s'; t' - s' = r\<rbrakk> \<Longrightarrow> t-s = r"
  by simp
lemma mult_cong2: "\<lbrakk>(t ::real) = t'; c*t' = r\<rbrakk> \<Longrightarrow> t*c = r"
  by (simp add: mult_ac)
lemma mult_cong: "\<lbrakk>(t ::real) = t'; c*t' = r\<rbrakk> \<Longrightarrow> c*t = r"
  by simp
lemma divide_cong: "\<lbrakk> (t::real) = t' ; t'/n = r\<rbrakk> \<Longrightarrow> t/n = r"
  by simp
lemma naddh_cong_ts: "\<lbrakk>t1 + (s::real) = t'\<rbrakk> \<Longrightarrow> (x + t1) + s = x + t'" by simp
lemma naddh_cong_st: "\<lbrakk>(t::real) + s = t'\<rbrakk> \<Longrightarrow> t+ (x + s) = x + t'" by simp
lemma naddh_cong_same: "\<lbrakk>(c1::real) + c2 = c ; t1 + t2 = t\<rbrakk> \<Longrightarrow> (c1*x + t1) + (c2*x+t2) = c*x + t"
  by (simp add: ring_eq_simps,simp only: ring_distrib(2)[symmetric])
lemma naddh_cong_same0: "\<lbrakk>(c1::real) + c2 = 0 ; t1 + t2 = t\<rbrakk> \<Longrightarrow> (c1*x + t1) + (c2*x+t2) = t"
  by (simp add: ring_eq_simps,simp only: ring_distrib(2)[symmetric]) simp
lemma ncmul_congh: "\<lbrakk> c*c' = (k::real) ; c*t = t'\<rbrakk>  \<Longrightarrow> c*(c'*x + t) = k*x + t'"
  by (simp add: ring_eq_simps)
lemma ncmul_cong: "\<lbrakk> c / n = c'/n' ; c'*t = (t'::real)\<rbrakk> \<Longrightarrow> c* (t/n) = t'/n'"
proof-
  assume "c / n = c'/n'" and "c'*t = (t'::real)"
  have "\<lbrakk> c' / n' = c/n ; (t'::real) = c'*t\<rbrakk> \<Longrightarrow> c* (t/n) = t'/n'"
    by (simp add: divide_inverse ring_eq_simps)  thus ?thesis using prems by simp
qed

lemma nneg_cong: "(-1 ::real)*t = t' \<Longrightarrow> - t = t'"  by simp
lemma uminus_cong: "\<lbrakk> t = t' ; - t' = r\<rbrakk> \<Longrightarrow>  - t = r"  by simp
lemma nsub_cong: "\<lbrakk>- (s::real) = s'; t + s' = t'\<rbrakk> \<Longrightarrow> t - s = t'"  by simp
lemma ndivide_cong: "m*n = (m'::real) \<Longrightarrow> (t/m) / n = t / m'"  by simp
lemma normalizeh_var: "(x::real) = (1*x + 0) / 1"  by simp
lemma nrefl: "(x::real) = x/1"  by simp

    (* cong rules for atoms normalization *)
  (* the < -case *)
lemma normalize_ltxpos_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cnp: "n/c > 0" and rr': "r/c + r'/c' = 0"
  shows "(s < t) = (x < r'/c')"
proof-
  from cnp have cnz: "c \<noteq> 0" by auto
  from cnp have nnz: "n\<noteq>0" by auto
  from rr' have rr'': "-(r/c) = r'/c'" by simp
  have "s < t = (s - t < 0)" by simp
  also have "\<dots> = ((c*x+r) / n < 0)" using smt by simp
  also have "\<dots> = ((c/n)*x + r/n < 0)" by (simp add: add_divide_distrib)
  also have "\<dots> = ( (n/c)*((c/n)*x + r/n) < (n/c)*0)" 
    using cnp mult_less_cancel_left[where c="(n/c)" and b="0"] by simp 
  also have "\<dots> = (x + r/c < 0)" 
    using cnz nnz by (simp add: add_divide_distrib ring_eq_simps)
  also have "\<dots> = (x < - (r/c))" by auto
  finally show ?thesis using rr'' by simp
qed

lemma normalize_ltxneg_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cnp: "n/c < 0" and rr': "r/c + r'/c' = 0"
  shows "(s < t) = (x > r'/c')"
proof-
  from cnp have cnz: "c \<noteq> 0" by auto
  from cnp have nnz: "n\<noteq>0" by auto
  from cnp have cnp': "\<not> (n/c > 0)" by simp
  from rr' have rr'': "-(r/c) = r'/c'" by simp
  have "s < t = (s - t < 0)" by simp
  also have "\<dots> = ((c*x+r) / n < 0)" using smt by simp
  also have "\<dots> = ((c/n)*x + r/n < 0)" by (simp add: add_divide_distrib)
  also have "\<dots> = ( (n/c)*((c/n)*x + r/n) > 0)"
    using zero_less_mult_iff[where a="n/c" and b="(c/n)*x + r/n", simplified cnp cnp' simp_thms]
    by simp 
  also have "\<dots> = (x + r/c > 0)" 
    using cnz nnz by (simp add: add_divide_distrib ring_eq_simps)
  also have "\<dots> = (x > - (r/c))" by auto
  finally show ?thesis using rr'' by simp
qed
lemma normalize_ltground_cong: "\<lbrakk> s -t = (r::real) ; r < 0 = P\<rbrakk> \<Longrightarrow> s < t = P"  by auto
lemma normalize_ltnoxpos_cong: 
  assumes st: "s - t = (r::real) / n" and mp: "n > 0"
  shows "s < t = (r <0)"
proof-  
  have "s < t = (s - t < 0)" by simp
  also have "\<dots> = (r / n < 0)" using st by simp
  also have "\<dots> = (n* (r/n) < 0)" using mult_less_0_iff[where a="n" and b="r/n"] mp by simp
  finally show ?thesis using mp by auto
qed

lemma normalize_ltnoxneg_cong: 
  assumes st: "s - t = (r::real) / n" and mp: "n < 0"
  shows "s < t = (r > 0)"
proof-  
  have "s < t = (s - t < 0)" by simp
  also have "\<dots> = (r / n < 0)" using st by simp
  also have "\<dots> = (n* (r/n) > 0)" using zero_less_mult_iff[where a="n" and b="r/n"] mp by simp
  finally show ?thesis using mp by auto
qed

  (* the <= -case *)
lemma normalize_lexpos_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cnp: "n/c > 0" and rr': "r/c + r'/c' = 0"
  shows "(s \<le> t) = (x \<le> r'/c')"
proof-
  from cnp have cnz: "c \<noteq> 0" by auto
  from cnp have nnz: "n\<noteq>0" by auto
  from rr' have rr'': "-(r/c) = r'/c'" by simp
  have "s \<le> t = (s - t \<le> 0)" by simp
  also have "\<dots> = ((c*x+r) / n \<le> 0)" using smt by simp
  also have "\<dots> = ((c/n)*x + r/n \<le> 0)" by (simp add: add_divide_distrib)
  also have "\<dots> = ( (n/c)*((c/n)*x + r/n) \<le> (n/c)*0)" 
    using cnp mult_le_cancel_left[where c="(n/c)" and b="0"] by simp 
  also have "\<dots> = (x + r/c \<le> 0)" 
    using cnz nnz by (simp add: add_divide_distrib ring_eq_simps)
  also have "\<dots> = (x \<le> - (r/c))" by auto
  finally show ?thesis using rr'' by simp
qed

lemma normalize_lexneg_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cnp: "n/c < 0" and rr': "r/c + r'/c' = 0"
  shows "(s \<le> t) = (x \<ge> r'/c')"
proof-
  from cnp have cnz: "c \<noteq> 0" by auto
  from cnp have nnz: "n\<noteq>0" by auto
  from cnp have cnp': "\<not> (n/c \<ge> 0) \<and> n/c \<le> 0" by simp
  from rr' have rr'': "-(r/c) = r'/c'" by simp
  have "s \<le> t = (s - t \<le> 0)" by simp
  also have "\<dots> = ((c*x+r) / n \<le> 0)" using smt by simp
  also have "\<dots> = ((c/n)*x + r/n \<le> 0)" by (simp add: add_divide_distrib)
  also have "\<dots> = ( (n/c)*((c/n)*x + r/n) \<ge> 0)"
    using zero_le_mult_iff[where a="n/c" and b="(c/n)*x + r/n", simplified cnp' simp_thms]
    by simp 
  also have "\<dots> = (x + r/c \<ge> 0)" 
    using cnz nnz by (simp add: add_divide_distrib ring_eq_simps)
  also have "\<dots> = (x \<ge> - (r/c))" by auto
  finally show ?thesis using rr'' by simp
qed
lemma normalize_leground_cong: "\<lbrakk> s -t = (r::real) ; r \<le> 0 = P\<rbrakk> \<Longrightarrow> s \<le> t = P"  by auto
lemma normalize_lenoxpos_cong: 
  assumes st: "s - t = (r::real) / n" and mp: "n > 0"
  shows "s \<le> t = (r \<le>0)"
proof-  
  have "s \<le> t = (s - t \<le> 0)" by simp
  also have "\<dots> = (r / n \<le> 0)" using st by simp
  also have "\<dots> = (n* (r/n) \<le> 0)" using mult_le_0_iff[where a="n" and b="r/n"] mp by simp
  finally show ?thesis using mp by auto
qed

lemma normalize_lenoxneg_cong: 
  assumes st: "s - t = (r::real) / n" and mp: "n < 0"
  shows "s \<le> t = (r \<ge> 0)"
proof-  
  have "s \<le> t = (s - t \<le> 0)" by simp
  also have "\<dots> = (r / n \<le> 0)" using st by simp
  also have "\<dots> = (n* (r/n) \<ge> 0)" using zero_le_mult_iff[where a="n" and b="r/n"] mp by simp
  finally show ?thesis using mp by auto
qed
    (* The = -case *)

lemma normalize_eqxpos_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cp: "c > 0" and nnz: "n \<noteq> 0" and rr': "r+ r' = 0"
  shows "(s = t) = (x = r'/c)"
proof-
  from rr' have rr'': "-r = r'" by simp
  have "(s = t) = (s - t = 0)" by simp
  also have "\<dots> = ((c*x + r) /n = 0)" using smt by simp
  also have "\<dots> = (c*x = -r)" using nnz by auto
  also have "\<dots> = (x = (-r) / c)" using cp eq_divide_eq[where c="c" and a="x" and b="-r"]
    by (simp add: mult_ac)
  finally show ?thesis using rr'' by simp
qed

lemma normalize_eqxneg_cong: assumes smt: "s - t = (c*x+r) / (n::real)"
  and cp: "c < 0" and nnz: "n \<noteq> 0" and cc': "c+ c' = 0"
  shows "(s = t) = (x = r/c')"
proof-
  from cc' have cc'': "-c = c'" by simp
  have "(s = t) = (s - t = 0)" by simp
  also have "\<dots> = ((c*x + r) /n = 0)" using smt by simp
  also have "\<dots> = ((-c)*x = r)" using nnz by auto
  also have "\<dots> = (x = r / (-c))" using cp eq_divide_eq[where c="-c" and a="x" and b="r"]
    by (simp add: mult_ac)
  finally show ?thesis using cc'' by simp
qed

lemma normalize_eqnox_cong: "\<lbrakk>s - t = (r::real) / n;n \<noteq> 0\<rbrakk> \<Longrightarrow> s = t = (r = 0)" by auto

lemma normalize_eqground_cong: "\<lbrakk>s - t =(r::real)/n;n \<noteq> 0;(r = 0) = P \<rbrakk> \<Longrightarrow> s=t = P" by auto

lemma trivial_sum_of_opposites: "-t = t' \<Longrightarrow> t + t' = (0::real)" by simp
lemma sum_of_opposite_denoms: 
  assumes cc': "(c::real) + c' = 0" shows "r/c + r/c' = 0"
proof-
  from cc' have "c' = -c" by simp
  thus ?thesis by simp
qed
lemma sum_of_same_denoms: " -r = (r'::real) \<Longrightarrow> r/c + r'/c = 0"  by auto
lemma normalize_not_lt: "t \<le> (s::real) = P \<Longrightarrow> (\<not> s<t) = P"  by auto
lemma normalize_not_le: "t < (s::real) = P \<Longrightarrow> (\<not> s\<le>t) = P"  by auto
lemma normalize_not_eq: "\<lbrakk> t = (s::real) = P ; (~P) = P' \<rbrakk> \<Longrightarrow> (s\<noteq>t) = P'"  by auto
lemma ex_eq_cong: "(!! x. A x = B x) \<Longrightarrow> ((\<exists>x. A x) = (\<exists> x. B x))"  by blast

use "ferrante_rackoff_proof.ML"
use "ferrante_rackoff.ML"
setup "Ferrante_Rackoff.setup"

end
