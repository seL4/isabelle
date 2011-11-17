(*  Title:      HOL/SPARK/Examples/RIPEMD-160/Round.thy
    Author:     Fabian Immler, TU Muenchen

Verification of the RIPEMD-160 hash function
*)

theory Round
imports RMD_Specification
begin

spark_open "rmd/round.siv"

abbreviation from_chain :: "chain \<Rightarrow> RMD.chain" where
  "from_chain c \<equiv> (
    word_of_int (h0 c),
    word_of_int (h1 c),
    word_of_int (h2 c),
    word_of_int (h3 c),
    word_of_int (h4 c))"

abbreviation from_chain_pair :: "chain_pair \<Rightarrow> RMD.chain \<times> RMD.chain" where
  "from_chain_pair cc \<equiv> (
    from_chain (left cc),
    from_chain (right cc))"

abbreviation to_chain :: "RMD.chain \<Rightarrow> chain" where
  "to_chain c \<equiv>
    (let (h0, h1, h2, h3, h4) = c in
      (|h0 = uint h0,
        h1 = uint h1,
        h2 = uint h2,
        h3 = uint h3,
        h4 = uint h4|))"

abbreviation to_chain_pair :: "RMD.chain \<times> RMD.chain \<Rightarrow> chain_pair" where
  "to_chain_pair c == (let (c1, c2) = c in
    (| left = to_chain c1,
      right = to_chain c2 |))"

abbreviation steps' :: "chain_pair \<Rightarrow> int \<Rightarrow> block \<Rightarrow> chain_pair" where
  "steps' cc i b == to_chain_pair (steps
    (\<lambda>n. word_of_int (b (int n)))
    (from_chain_pair cc)
    (nat i))"

abbreviation round_spec :: "chain \<Rightarrow> block \<Rightarrow> chain" where
  "round_spec c b == to_chain (round (\<lambda>n. word_of_int (b (int n))) (from_chain c))"

spark_proof_functions
  steps = steps'
  round_spec = round_spec

lemma uint_word_of_int_id:
  assumes "0 <= (x::int)"
  assumes "x <= 4294967295"
  shows"uint(word_of_int x::word32) = x"
  unfolding int_word_uint
  using assms
  by (simp add:int_mod_eq')

lemma steps_step: "steps X cc (Suc i) = step_both X (steps X cc i) i"
  unfolding steps_def
  by (induct i) simp_all

lemma from_to_id: "from_chain_pair (to_chain_pair CC) = CC"
proof (cases CC)
  fix a::RMD.chain
  fix b c d e f::word32
  assume "CC = (a, b, c, d, e, f)"
  thus ?thesis by (cases a) simp
qed

lemma steps_to_steps':
  "F A (steps X cc i) B =
   F A (from_chain_pair (to_chain_pair (steps X cc i))) B"
  unfolding from_to_id ..

lemma steps'_step:
  assumes "0 <= i"
  shows
  "steps' cc (i + 1) X = to_chain_pair (
     step_both
       (\<lambda>n. word_of_int (X (int n)))
       (from_chain_pair (steps' cc i X))
       (nat i))"
proof -
  have "nat (i + 1) = Suc (nat i)" using assms by simp
  show ?thesis
    unfolding `nat (i + 1) = Suc (nat i)` steps_step steps_to_steps'
    ..
qed 

lemma step_from_hyp:
  assumes
  step_hyp:
  "\<lparr>left =
      \<lparr>h0 = a, h1 = b, h2 = c, h3 = d, h4 = e\<rparr>,
    right =
      \<lparr>h0 = a', h1 = b', h2 = c', h3 = d', h4 = e'\<rparr>\<rparr> =
   steps'
     (\<lparr>left =
         \<lparr>h0 = a_0, h1 = b_0, h2 = c_0,
          h3 = d_0, h4 = e_0\<rparr>,
       right =
         \<lparr>h0 = a_0, h1 = b_0, h2 = c_0,
          h3 = d_0, h4 = e_0\<rparr>\<rparr>)
     j x"
  assumes "a <= 4294967295" (is "_ <= ?M")
  assumes                "b  <= ?M" and "c  <= ?M" and "d  <= ?M" and "e  <= ?M"
  assumes "a' <= ?M" and "b' <= ?M" and "c' <= ?M" and "d' <= ?M" and "e' <= ?M"
  assumes "0 <= a " and "0 <= b " and "0 <= c " and "0 <= d " and "0 <= e "
  assumes "0 <= a'" and "0 <= b'" and "0 <= c'" and "0 <= d'" and "0 <= e'"
  assumes "0 <= x (r_l_spec j)" and "x (r_l_spec j) <= ?M"
  assumes "0 <= x (r_r_spec j)" and "x (r_r_spec j) <= ?M"
  assumes "0 <= j" and "j <= 79"
  shows
  "\<lparr>left =
      \<lparr>h0 = e,
         h1 =
           (rotate_left (s_l_spec j)
             ((((a + f_spec j b c d) mod 4294967296 +
                x (r_l_spec j)) mod
               4294967296 +
               k_l_spec j) mod
              4294967296) +
            e) mod
           4294967296,
         h2 = b, h3 = rotate_left 10 c,
         h4 = d\<rparr>,
      right =
        \<lparr>h0 = e',
           h1 =
             (rotate_left (s_r_spec j)
               ((((a' + f_spec (79 - j) b' c' d') mod
                  4294967296 +
                  x (r_r_spec j)) mod
                 4294967296 +
                 k_r_spec j) mod
                4294967296) +
              e') mod
             4294967296,
           h2 = b', h3 = rotate_left 10 c',
           h4 = d'\<rparr>\<rparr> =
   steps'
    (\<lparr>left =
        \<lparr>h0 = a_0, h1 = b_0, h2 = c_0,
           h3 = d_0, h4 = e_0\<rparr>,
        right =
          \<lparr>h0 = a_0, h1 = b_0, h2 = c_0,
             h3 = d_0, h4 = e_0\<rparr>\<rparr>)
    (j + 1) x"
  using step_hyp
proof -
  let ?MM = 4294967296
  have AL: "uint(word_of_int e::word32) = e"
    by (rule uint_word_of_int_id[OF `0 <= e` `e <= ?M`])
  have CL: "uint(word_of_int b::word32) = b"
    by (rule uint_word_of_int_id[OF `0 <= b` `b <= ?M`])
  have DL: "True" ..
  have EL: "uint(word_of_int d::word32) = d"
    by (rule uint_word_of_int_id[OF `0 <= d` `d <= ?M`])
  have AR: "uint(word_of_int e'::word32) = e'"
    by (rule uint_word_of_int_id[OF `0 <= e'` `e' <= ?M`])
  have CR: "uint(word_of_int b'::word32) = b'"
    by (rule uint_word_of_int_id[OF `0 <= b'` `b' <= ?M`])
  have DR: "True" ..
  have ER: "uint(word_of_int d'::word32) = d'"
    by (rule uint_word_of_int_id[OF `0 <= d'` `d' <= ?M`])
  have BL:
    "(uint
      (word_rotl (s (nat j))
        ((word_of_int::int\<Rightarrow>word32)
          ((((a + f_spec j b c d) mod ?MM +
             x (r_l_spec j)) mod ?MM +
            k_l_spec j) mod ?MM))) +
        e) mod ?MM
    =
    uint
              (word_rotl (s (nat j))
                (word_of_int a +
                 f (nat j) (word_of_int b)
                  (word_of_int c) (word_of_int d) +
                 word_of_int (x (r_l_spec j)) +
                 K (nat j)) +
               word_of_int e)"
    (is "(uint (word_rotl _ (_ ((((_ + ?F) mod _ + ?X) mod _ + _) mod _))) + _) mod _ = _")
  proof -
    have "a mod ?MM = a" using `0 <= a` `a <= ?M`
      by (simp add: int_mod_eq')
    have "?X mod ?MM = ?X" using `0 <= ?X` `?X <= ?M`
      by (simp add: int_mod_eq')
    have "e mod ?MM = e" using `0 <= e` `e <= ?M`
      by (simp add: int_mod_eq')
    have "(?MM::int) = 2 ^ len_of TYPE(32)" by simp
    show ?thesis
      unfolding
        word_add_def
        uint_word_of_int_id[OF `0 <= a` `a <= ?M`]
        uint_word_of_int_id[OF `0 <= ?X` `?X <= ?M`]
        int_word_uint
      unfolding `?MM = 2 ^ len_of TYPE(32)`
      unfolding word_uint.Abs_norm
      by (simp add:
        `a mod ?MM = a`
        `e mod ?MM = e`
        `?X mod ?MM = ?X`)
  qed

  have BR:
    "(uint
      (word_rotl (s' (nat j))
        ((word_of_int::int\<Rightarrow>word32)
          ((((a' + f_spec (79 - j) b' c' d') mod ?MM +
             x (r_r_spec j)) mod ?MM +
            k_r_spec j) mod ?MM))) +
        e') mod ?MM
    =
    uint
              (word_rotl (s' (nat j))
                (word_of_int a' +
                 f (79 - nat j) (word_of_int b')
                  (word_of_int c') (word_of_int d') +
                 word_of_int (x (r_r_spec j)) +
                 K' (nat j)) +
               word_of_int e')"
    (is "(uint (word_rotl _ (_ ((((_ + ?F) mod _ + ?X) mod _ + _) mod _))) + _) mod _ = _")
  proof -
    have "a' mod ?MM = a'" using `0 <= a'` `a' <= ?M`
      by (simp add: int_mod_eq')
    have "?X mod ?MM = ?X" using `0 <= ?X` `?X <= ?M`
      by (simp add: int_mod_eq')
    have "e' mod ?MM = e'" using `0 <= e'` `e' <= ?M`
      by (simp add: int_mod_eq')
    have "(?MM::int) = 2 ^ len_of TYPE(32)" by simp
    have nat_transfer: "79 - nat j = nat (79 - j)"
      using nat_diff_distrib `0 <= j`  `j <= 79`
      by simp
    show ?thesis
      unfolding
        word_add_def
        uint_word_of_int_id[OF `0 <= a'` `a' <= ?M`]
        uint_word_of_int_id[OF `0 <= ?X` `?X <= ?M`]
        int_word_uint
        nat_transfer
      unfolding `?MM = 2 ^ len_of TYPE(32)`
      unfolding word_uint.Abs_norm
      by (simp add: 
        `a' mod ?MM = a'`
        `e' mod ?MM = e'`
        `?X mod ?MM = ?X`)
  qed

  show ?thesis
    unfolding steps'_step[OF `0 <= j`] step_hyp[symmetric]
      step_both_def step_r_def step_l_def
    by (simp add: AL BL CL DL EL AR BR CR DR ER)
qed

spark_vc procedure_round_61
proof -
  let ?M = "4294967295::int"
  have step_hyp:
  "\<lparr>left =
      \<lparr>h0 = ca, h1 = cb, h2 = cc,
         h3 = cd, h4 = ce\<rparr>,
      right =
        \<lparr>h0 = ca, h1 = cb, h2 = cc,
           h3 = cd, h4 = ce\<rparr>\<rparr> =
   steps'
    (\<lparr>left =
        \<lparr>h0 = ca, h1 = cb, h2 = cc,
           h3 = cd, h4 = ce\<rparr>,
        right =
          \<lparr>h0 = ca, h1 = cb, h2 = cc,
             h3 = cd, h4 = ce\<rparr>\<rparr>)
    0 x"
    unfolding steps_def 
    by (simp add:
      uint_word_of_int_id[OF `0 <= ca` `ca <= ?M`]
      uint_word_of_int_id[OF `0 <= cb` `cb <= ?M`]
      uint_word_of_int_id[OF `0 <= cc` `cc <= ?M`]
      uint_word_of_int_id[OF `0 <= cd` `cd <= ?M`]
      uint_word_of_int_id[OF `0 <= ce` `ce <= ?M`])
  let ?rotate_arg_l =
    "((((ca + f 0 cb cc cd) mod 4294967296 +
        x (r_l 0)) mod 4294967296 + k_l 0) mod 4294967296)"
  let ?rotate_arg_r =
    "((((ca + f 79 cb cc cd) mod 4294967296 +
        x (r_r 0)) mod 4294967296 + k_r 0) mod 4294967296)"
  note returns =
    `wordops__rotate (s_l 0) ?rotate_arg_l =
     rotate_left (s_l 0) ?rotate_arg_l`
    `wordops__rotate (s_r 0) ?rotate_arg_r =
     rotate_left (s_r 0) ?rotate_arg_r`
    `wordops__rotate 10 cc = rotate_left 10 cc`
    `f 0 cb cc cd = f_spec 0 cb cc cd`
    `f 79 cb cc cd = f_spec 79 cb cc cd`
    `k_l 0 = k_l_spec 0`
    `k_r 0 = k_r_spec 0`
    `r_l 0 = r_l_spec 0`
    `r_r 0 = r_r_spec 0`
    `s_l 0 = s_l_spec 0`
    `s_r 0 = s_r_spec 0`

  note x_borders = `\<forall>i. 0 \<le> i \<and> i \<le> 15 \<longrightarrow> 0 \<le> x i \<and> x i \<le> ?M`

  from `0 <= r_l 0` `r_l 0 <= 15` x_borders
  have "0 \<le> x (r_l 0)" by blast
  hence x_lower: "0 <= x (r_l_spec 0)" unfolding returns .

  from `0 <= r_l 0` `r_l 0 <= 15` x_borders
  have "x (r_l 0) <= ?M" by blast
  hence x_upper: "x (r_l_spec 0) <= ?M" unfolding returns .

  from `0 <= r_r 0` `r_r 0 <= 15` x_borders
  have "0 \<le> x (r_r 0)" by blast
  hence x_lower': "0 <= x (r_r_spec 0)" unfolding returns .

  from `0 <= r_r 0` `r_r 0 <= 15` x_borders
  have "x (r_r 0) <= ?M" by blast
  hence x_upper': "x (r_r_spec 0) <= ?M" unfolding returns .

  have "0 <= (0::int)" by simp
  have "0 <= (79::int)" by simp
  note step_from_hyp [OF
    step_hyp
    H2 H4 H6 H8 H10 H2 H4 H6 H8 H10 (* upper bounds *)
    H1 H3 H5 H7 H9  H1 H3 H5 H7 H9  (* lower bounds *)
  ]
  from this[OF x_lower x_upper x_lower' x_upper' `0 <= 0` `0 <= 79`]
    `0 \<le> ca` `0 \<le> ce` x_lower x_lower'
  show ?thesis unfolding returns(1) returns(2) unfolding returns
    by simp
qed

spark_vc procedure_round_62
proof -
  let ?M = "4294967295::int"
  let ?rotate_arg_l =
    "((((cla + f (loop__1__j + 1) clb clc cld) mod 4294967296 +
         x (r_l (loop__1__j + 1))) mod 4294967296 +
         k_l (loop__1__j + 1)) mod 4294967296)"
  let ?rotate_arg_r =
    "((((cra + f (79 - (loop__1__j + 1)) crb crc crd) mod
         4294967296 + x (r_r (loop__1__j + 1))) mod 4294967296 +
         k_r (loop__1__j + 1)) mod 4294967296)"

  have s: "78 - loop__1__j = (79 - (loop__1__j + 1))" by simp
  note returns =
    `wordops__rotate (s_l (loop__1__j + 1)) ?rotate_arg_l =
     rotate_left (s_l (loop__1__j + 1)) ?rotate_arg_l`
    `wordops__rotate (s_r (loop__1__j + 1)) ?rotate_arg_r =
     rotate_left (s_r (loop__1__j + 1)) ?rotate_arg_r`
    `f (loop__1__j + 1) clb clc cld =
     f_spec (loop__1__j + 1) clb clc cld`
    `f (78 - loop__1__j) crb crc crd =
     f_spec (78 - loop__1__j) crb crc crd`[simplified s]
    `wordops__rotate 10 clc = rotate_left 10 clc`
    `wordops__rotate 10 crc = rotate_left 10 crc`
    `k_l (loop__1__j + 1) = k_l_spec (loop__1__j + 1)`
    `k_r (loop__1__j + 1) = k_r_spec (loop__1__j + 1)`
    `r_l (loop__1__j + 1) = r_l_spec (loop__1__j + 1)`
    `r_r (loop__1__j + 1) = r_r_spec (loop__1__j + 1)`
    `s_l (loop__1__j + 1) = s_l_spec (loop__1__j + 1)`
    `s_r (loop__1__j + 1) = s_r_spec (loop__1__j + 1)`

  note x_borders = `\<forall>i. 0 \<le> i \<and> i \<le> 15 \<longrightarrow> 0 \<le> x i \<and> x i \<le> ?M`

  from `0 <= r_l (loop__1__j + 1)` `r_l (loop__1__j + 1) <= 15` x_borders
  have "0 \<le> x (r_l (loop__1__j + 1))" by blast
  hence x_lower: "0 <= x (r_l_spec (loop__1__j + 1))" unfolding returns .

  from `0 <= r_l (loop__1__j + 1)` `r_l (loop__1__j + 1) <= 15` x_borders
  have "x (r_l (loop__1__j + 1)) <= ?M" by blast
  hence x_upper: "x (r_l_spec (loop__1__j + 1)) <= ?M" unfolding returns .

  from `0 <= r_r (loop__1__j + 1)` `r_r (loop__1__j + 1) <= 15` x_borders
  have "0 \<le> x (r_r (loop__1__j + 1))" by blast
  hence x_lower': "0 <= x (r_r_spec (loop__1__j + 1))" unfolding returns .

  from `0 <= r_r (loop__1__j + 1)` `r_r (loop__1__j + 1) <= 15` x_borders
  have "x (r_r (loop__1__j + 1)) <= ?M" by blast
  hence x_upper': "x (r_r_spec (loop__1__j + 1)) <= ?M" unfolding returns .

  from `0 <= loop__1__j` have "0 <= loop__1__j + 1" by simp
  from `loop__1__j <= 78` have "loop__1__j + 1 <= 79" by simp

  have "loop__1__j + 1 + 1 = loop__1__j + 2" by simp

  note step_from_hyp[OF H1
    `cla <= ?M`
    `clb <= ?M`
    `clc <= ?M`
    `cld <= ?M`
    `cle <= ?M`
    `cra <= ?M`
    `crb <= ?M`
    `crc <= ?M`
    `crd <= ?M`
    `cre <= ?M`
    
    `0 <= cla`
    `0 <= clb`
    `0 <= clc`
    `0 <= cld`
    `0 <= cle`
    `0 <= cra`
    `0 <= crb`
    `0 <= crc`
    `0 <= crd`
    `0 <= cre`]
  from this[OF
    x_lower x_upper x_lower' x_upper'
    `0 <= loop__1__j + 1` `loop__1__j + 1 <= 79`]
    `0 \<le> cla` `0 \<le> cle` `0 \<le> cra` `0 \<le> cre` x_lower x_lower'
  show ?thesis unfolding `loop__1__j + 1 + 1 = loop__1__j + 2`
    unfolding returns(1) returns(2) unfolding returns
    by simp
qed

spark_vc procedure_round_76
proof -
  let ?M = "4294967295 :: int"
  let ?INIT_CHAIN =
     "\<lparr>h0 = ca_init, h1 = cb_init,
         h2 = cc_init, h3 = cd_init,
         h4 = ce_init\<rparr>"
  have steps_to_steps':
    "steps
       (\<lambda>n\<Colon>nat. word_of_int (x (int n)))
       (from_chain ?INIT_CHAIN, from_chain ?INIT_CHAIN)
       80 =
    from_chain_pair (
      steps'
      (\<lparr>left = ?INIT_CHAIN, right = ?INIT_CHAIN\<rparr>)
      80
      x)"
    unfolding from_to_id by simp
  from
    `0 \<le> ca_init` `ca_init \<le> ?M`
    `0 \<le> cb_init` `cb_init \<le> ?M`
    `0 \<le> cc_init` `cc_init \<le> ?M`
    `0 \<le> cd_init` `cd_init \<le> ?M`
    `0 \<le> ce_init` `ce_init \<le> ?M`
    `0 \<le> cla` `cla \<le> ?M`
    `0 \<le> clb` `clb \<le> ?M`
    `0 \<le> clc` `clc \<le> ?M`
    `0 \<le> cld` `cld \<le> ?M`
    `0 \<le> cle` `cle \<le> ?M`
    `0 \<le> cra` `cra \<le> ?M`
    `0 \<le> crb` `crb \<le> ?M`
    `0 \<le> crc` `crc \<le> ?M`
    `0 \<le> crd` `crd \<le> ?M`
    `0 \<le> cre` `cre \<le> ?M`
  show ?thesis
    unfolding round_def
    unfolding steps_to_steps'
    unfolding H1[symmetric]
    by (simp add: uint_word_ariths(2) rdmods
      uint_word_of_int_id)
qed

spark_end

end
