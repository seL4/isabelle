theory SeriesPlus
  imports Complex_Main Nat_Int_Bij 

begin

text{*From the Hurd/Coble measure theory development, translated by Lawrence Paulson.*}

lemma choice2: "(!!x. \<exists>y z. Q x y z) ==> \<exists>f g. \<forall>x. Q x (f x) (g x)"
  by metis

lemma range_subsetD: "range f \<subseteq> B \<Longrightarrow> f i \<in> B"
  by blast


lemma suminf_2dimen:
  fixes f:: "nat * nat \<Rightarrow> real"
  assumes f_nneg: "!!m n. 0 \<le> f(m,n)"
      and fsums: "!!m. (\<lambda>n. f (m,n)) sums (g m)"
      and sumg: "summable g"
  shows "(f o nat_to_nat2) sums suminf g"
proof (simp add: sums_def)
  {
    fix x
    have "0 \<le> f x"
      by (cases x) (simp add: f_nneg) 
  } note [iff]  = this
  have g_nneg: "!!m. 0 \<le> g m"
    proof -
      fix m
      have "0 \<le> suminf (\<lambda>n. f (m,n))"
	by (rule suminf_0_le, simp add: f_nneg, metis fsums sums_iff)
      thus "0 \<le> g m" using fsums [of m] 
	by (auto simp add: sums_iff) 
    qed
  show "(\<lambda>n. \<Sum>x = 0..<n. f (nat_to_nat2 x)) ----> suminf g"
  proof (rule increasing_LIMSEQ, simp add: f_nneg)
    fix n
    def i \<equiv> "Max (Domain (nat_to_nat2 ` {0..<n}))"
    def j \<equiv> "Max (Range (nat_to_nat2 ` {0..<n}))"
    have ij: "nat_to_nat2 ` {0..<n} \<subseteq> ({0..i} \<times> {0..j})" 
      by (force simp add: i_def j_def 
                intro: finite_imageI Max_ge finite_Domain finite_Range)  
    have "(\<Sum>x = 0..<n. f (nat_to_nat2 x)) = setsum f (nat_to_nat2 ` {0..<n})" 
      using setsum_reindex [of nat_to_nat2 "{0..<n}" f] 
      by (simp add: o_def)
         (metis nat_to_nat2_inj subset_inj_on subset_UNIV nat_to_nat2_inj) 
    also have "... \<le> setsum f ({0..i} \<times> {0..j})"
      by (rule setsum_mono2) (auto simp add: ij) 
    also have "... = setsum (\<lambda>m. setsum (\<lambda>n. f (m,n)) {0..j}) {0..<Suc i}"
      by (metis atLeast0AtMost atLeast0LessThan lessThan_Suc_atMost
	        setsum_cartesian_product split_eta) 
    also have "... \<le> setsum g {0..<Suc i}" 
      proof (rule setsum_mono, simp add: less_Suc_eq_le) 
	fix m
	assume m: "m \<le> i"
	thus " (\<Sum>n = 0..j. f (m, n)) \<le> g m" using fsums [of m]
	  by (auto simp add: sums_iff) 
	   (metis atLeastLessThanSuc_atLeastAtMost f_nneg series_pos_le f_nneg) 
      qed
    finally have  "(\<Sum>x = 0..<n. f (nat_to_nat2 x)) \<le> setsum g {0..<Suc i}" .
    also have "... \<le> suminf g" 
      by (rule series_pos_le [OF sumg]) (simp add: g_nneg) 
    finally show "(\<Sum>x = 0..<n. f (nat_to_nat2 x)) \<le> suminf g" .
  next
    fix e :: real
    assume e: "0 < e"
    with summable_sums [OF sumg]
    obtain N where "\<bar>setsum g {0..<N} - suminf g\<bar> < e/2" and nz: "N>0"
      by (simp add: sums_def LIMSEQ_iff_nz dist_real_def)
         (metis e half_gt_zero le_refl that)
    hence gless: "suminf g < setsum g {0..<N} + e/2" using series_pos_le [OF sumg]
      by (simp add: g_nneg)
    { fix m
      assume m: "m<N"
      hence enneg: "0 < e / (2 * real N)" using e
	by (simp add: zero_less_divide_iff) 
      hence  "\<exists>j. \<bar>(\<Sum>n = 0..<j. f (m, n)) - g m\<bar> < e/(2 * real N)"
	using fsums [of m] m
        by (force simp add: sums_def LIMSEQ_def dist_real_def)
      hence "\<exists>j. g m < setsum (\<lambda>n. f (m,n)) {0..<j} + e/(2 * real N)" 
	using fsums [of m]
	by (auto simp add: sums_iff) 
           (metis abs_diff_less_iff add_less_cancel_right eq_diff_eq') 
    }
    hence "\<exists>jj. \<forall>m. m<N \<longrightarrow> g m < (\<Sum>n = 0..<jj m. f (m, n)) + e/(2 * real N)"
      by (force intro: choice) 
    then obtain jj where jj:
          "!!m. m<N \<Longrightarrow> g m < (\<Sum>n = 0..<jj m. f (m, n)) + e/(2 * real N)"
      by auto
    def IJ \<equiv> "SIGMA i : {0..<N}. {0..<jj i}"
    have "setsum g {0..<N} <
             (\<Sum>m = 0..<N. (\<Sum>n = 0..<jj m. f (m, n)) + e/(2 * real N))"
      by (auto simp add: nz jj intro: setsum_strict_mono) 
    also have "... = (\<Sum>m = 0..<N. \<Sum>n = 0..<jj m. f (m, n)) + e/2" using nz
      by (auto simp add: setsum_addf real_of_nat_def) 
    also have "... = setsum f IJ + e/2" 
      by (simp add: IJ_def setsum_Sigma) 
    finally have "setsum g {0..<N} < setsum f IJ + e/2" .
    hence glessf: "suminf g < setsum f IJ + e" using gless 
      by auto
    have finite_IJ: "finite IJ"
      by (simp add: IJ_def) 
    def NIJ \<equiv> "Max (nat_to_nat2 -` IJ)"
    have IJsb: "IJ \<subseteq> nat_to_nat2 ` {0..NIJ}"
      proof (auto simp add: NIJ_def)
	fix i j
	assume ij:"(i,j) \<in> IJ"
	hence "(i,j) = nat_to_nat2 (inv nat_to_nat2 (i,j))"
	  by (metis nat_to_nat2_surj surj_f_inv_f) 
	thus "(i,j) \<in> nat_to_nat2 ` {0..Max (nat_to_nat2 -` IJ)}"
	  by (rule image_eqI) 
	     (simp add: ij finite_vimageI [OF finite_IJ nat_to_nat2_inj]
                    nat_to_nat2_surj surj_f_inv_f) 
      qed
    have "setsum f IJ \<le> setsum f (nat_to_nat2 `{0..NIJ})"
      by (rule setsum_mono2) (auto simp add: IJsb) 
    also have "... = (\<Sum>k = 0..NIJ. f (nat_to_nat2 k))"
      by (simp add: setsum_reindex subset_inj_on [OF nat_to_nat2_inj subset_UNIV]) 
    also have "... = (\<Sum>k = 0..<Suc NIJ. f (nat_to_nat2 k))"
      by (metis atLeast0AtMost atLeast0LessThan lessThan_Suc_atMost)
    finally have "setsum f IJ \<le> (\<Sum>k = 0..<Suc NIJ. f (nat_to_nat2 k))" .
    thus "\<exists>n. suminf g \<le> (\<Sum>x = 0..<n. f (nat_to_nat2 x)) + e" using glessf
      by (metis add_right_mono local.glessf not_leE order_le_less_trans less_asym)
  qed
qed

end
