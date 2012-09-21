theory DP_Library
imports Main
begin

primrec alluopairs:: "'a list \<Rightarrow> ('a \<times> 'a) list"
where
  "alluopairs [] = []"
| "alluopairs (x#xs) = (map (Pair x) (x#xs))@(alluopairs xs)"

lemma alluopairs_set1: "set (alluopairs xs) \<le> {(x,y). x\<in> set xs \<and> y\<in> set xs}"
  by (induct xs) auto

lemma alluopairs_set:
  "\<lbrakk>x\<in> set xs ; y \<in> set xs\<rbrakk> \<Longrightarrow> (x,y) \<in> set (alluopairs xs) \<or> (y,x) \<in> set (alluopairs xs) "
  by (induct xs) auto

lemma alluopairs_bex:
  assumes Pc: "\<forall> x \<in> set xs. \<forall>y\<in> set xs. P x y = P y x"
  shows "(\<exists> x \<in> set xs. \<exists> y \<in> set xs. P x y) = (\<exists> (x,y) \<in> set (alluopairs xs). P x y)"
proof
  assume "\<exists>x\<in>set xs. \<exists>y\<in>set xs. P x y"
  then obtain x y where x: "x \<in> set xs" and y:"y \<in> set xs" and P: "P x y"
    by blast
  from alluopairs_set[OF x y] P Pc x y show"\<exists>(x, y)\<in>set (alluopairs xs). P x y" 
    by auto
next
  assume "\<exists>(x, y)\<in>set (alluopairs xs). P x y"
  then obtain "x" and "y" where xy: "(x,y) \<in> set (alluopairs xs)" and P: "P x y"
    by blast+
  from xy have "x \<in> set xs \<and> y\<in> set xs" using alluopairs_set1 by blast
  with P show "\<exists>x\<in>set xs. \<exists>y\<in>set xs. P x y" by blast
qed

lemma alluopairs_ex:
  "\<forall>x y. P x y = P y x \<Longrightarrow>
    (\<exists>x \<in> set xs. \<exists> y \<in> set xs. P x y) = (\<exists>(x,y) \<in> set (alluopairs xs). P x y)"
  by (blast intro!: alluopairs_bex)

end
