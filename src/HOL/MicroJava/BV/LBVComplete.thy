(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Completeness of the LBV *}

theory LBVComplete = LBVSpec:;

ML_setup {* bind_thm ("widen_RefT", widen_RefT) *};
ML_setup {* bind_thm ("widen_RefT2", widen_RefT2) *};

constdefs
  is_approx :: "['a option list, 'a list] \\<Rightarrow> bool"
  "is_approx a b \\<equiv> length a = length b \\<and> (\\<forall> n. n < length a \\<longrightarrow>
                   (a!n = None \\<or> a!n = Some (b!n)))"
  
  contains_dead :: "[instr list, certificate, method_type, p_count] \\<Rightarrow> bool"
  "contains_dead ins cert phi pc \\<equiv>
    (((\\<exists> branch. ins!pc = BR (Goto branch)) \\<or> ins!pc = MR Return) \\<or>
     (\\<exists>mi. ins!pc = MI mi)) \\<longrightarrow> Suc pc < length phi \\<longrightarrow>
      cert ! (Suc pc) = Some (phi ! Suc pc)"

  contains_targets :: "[instr list, certificate, method_type, p_count] \\<Rightarrow> bool"
  "contains_targets ins cert phi pc \\<equiv> 
    \\<forall> branch. (ins!pc = BR (Goto branch) \\<or> ins!pc = BR (Ifcmpeq branch)) \\<longrightarrow>
        (let pc' = nat (int pc+branch) in pc' < length phi \\<longrightarrow> cert!pc' = Some (phi!pc'))" 

  fits :: "[instr list, certificate, method_type] \\<Rightarrow> bool"
  "fits ins cert phi \\<equiv> is_approx cert phi \\<and> length ins < length phi \\<and>
                            (\\<forall> pc. pc < length ins \\<longrightarrow>
                                   contains_dead ins cert phi pc \\<and> 
                                   contains_targets ins cert phi pc)"

  is_target :: "[instr list, p_count] \\<Rightarrow> bool" 
  "is_target ins pc \\<equiv> 
     \\<exists> pc' branch. pc' < length ins \\<and> 
                   (ins ! pc' = (BR (Ifcmpeq branch)) \\<or> ins ! pc' = (BR (Goto branch))) \\<and> 
                   pc = (nat(int pc'+branch))"
  
  maybe_dead :: "[instr list, p_count] \\<Rightarrow> bool"
  "maybe_dead ins pc \\<equiv>
     \\<exists> pc'. pc = pc'+1 \\<and> ((\\<exists> branch. ins!pc' = BR (Goto branch)) \\<or>
                          ins!pc' = MR Return \\<or>
                          (\\<exists>mi. ins!pc' = MI mi))"


  mdot :: "[instr list, p_count] \\<Rightarrow> bool"
  "mdot ins pc \\<equiv> maybe_dead ins pc \\<or> is_target ins pc";


consts
  option_filter_n :: "['a list, nat \\<Rightarrow> bool, nat] \\<Rightarrow> 'a option list";
primrec 
  "option_filter_n []    P n = []"  
  "option_filter_n (h#t) P n = (if (P n) then Some h # option_filter_n t P (n+1) 
                                         else None   # option_filter_n t P (n+1))";  
  
constdefs 
  option_filter :: "['a list, nat \\<Rightarrow> bool] \\<Rightarrow> 'a option list" 
  "option_filter l P \\<equiv> option_filter_n l P 0" 
  
  make_cert :: "[instr list, method_type] \\<Rightarrow> certificate"
  "make_cert ins phi \\<equiv> option_filter phi (mdot ins)"
  
  make_Cert :: "[jvm_prog, prog_type] \\<Rightarrow> prog_certificate"
  "make_Cert G Phi \\<equiv>  \\<lambda> C sig.
    let (C,x,y,mdecls) = \\<epsilon> (Cl,x,y,mdecls). (Cl,x,y,mdecls) \\<in> set G \\<and> Cl = C in
      let (sig,rT,maxl,b) = \\<epsilon> (sg,rT,maxl,b). (sg,rT,maxl,b) \\<in> set mdecls \\<and> sg = sig in
        make_cert b (Phi C sig)";
  
constdefs
  wfprg :: "jvm_prog \\<Rightarrow> bool"
  "wfprg G \\<equiv> \\<exists>wf_mb. wf_prog wf_mb G";


lemma length_ofn: "\\<forall>n. length (option_filter_n l P n) = length l";
  by (induct l) auto;

lemma is_approx_option_filter_n:
"\\<forall>n. is_approx (option_filter_n a P n) a" (is "?P a");
proof (induct a);
  show "?P []"; by (auto simp add: is_approx_def);

  fix l ls;
  assume Cons: "?P ls";

  show "?P (l#ls)";
  proof (unfold is_approx_def, intro allI conjI impI);
    fix n;
    show "length (option_filter_n (l # ls) P n) = length (l # ls)"; 
      by (simp only: length_ofn);
    
    fix m;
    assume "m < length (option_filter_n (l # ls) P n)";
    hence m: "m < Suc (length ls)"; by (simp only: length_ofn) simp;
 
    show "option_filter_n (l # ls) P n ! m = None \\<or>
          option_filter_n (l # ls) P n ! m = Some ((l # ls) ! m)"; 
    proof (cases "m");
      assume "m = 0";
      with m; show ?thesis; by simp;
    next;
      fix m'; assume Suc: "m = Suc m'";
      from Cons;
      show ?thesis;
      proof (unfold is_approx_def, elim allE impE conjE);
        from m Suc;
        show "m' < length (option_filter_n ls P (Suc n))"; by (simp add: length_ofn);

        assume "option_filter_n ls P (Suc n) ! m' = None \\<or> 
                option_filter_n ls P (Suc n) ! m' = Some (ls ! m')";
        with m Suc;
        show ?thesis; by auto;
      qed;
    qed;
  qed;
qed;

lemma is_approx_option_filter: "is_approx (option_filter l P) l"; 
  by (simp add: option_filter_def is_approx_option_filter_n);

lemma option_filter_Some:
"\\<lbrakk>n < length l; P n\\<rbrakk> \\<Longrightarrow> option_filter l P ! n = Some (l!n)";
proof -;
  
  assume 1: "n < length l" "P n";

  have "\\<forall>n n'. n < length l \\<longrightarrow> P (n+n') \\<longrightarrow>  option_filter_n l P n' ! n = Some (l!n)"
    (is "?P l");
  proof (induct l);
    show "?P []"; by simp;

    fix l ls; assume Cons: "?P ls";
    show "?P (l#ls)";
    proof (intro);
      fix n n';
      assume l: "n < length (l # ls)";
      assume P: "P (n + n')";
      show "option_filter_n (l # ls) P n' ! n = Some ((l # ls) ! n)";
      proof (cases "n");
        assume "n=0";
        with P; show ?thesis; by simp;
      next;
        fix m; assume "n = Suc m";
        with l P Cons;
        show ?thesis; by simp;
      qed;
    qed;
  qed;

  with 1;
  show ?thesis; by (auto simp add: option_filter_def);
qed;

lemma option_filter_contains_dead:
"contains_dead ins (option_filter phi (mdot ins)) phi pc"; 
  by (auto intro: option_filter_Some simp add: contains_dead_def mdot_def maybe_dead_def);

lemma option_filter_contains_targets:
"pc < length ins \\<Longrightarrow> contains_targets ins (option_filter phi (mdot ins)) phi pc";
proof (simp add: contains_targets_def, intro allI impI conjI); 

  fix branch;
  assume 1: "ins ! pc = BR (Goto branch)" 
            "nat (int pc + branch) < length phi"
            "pc < length ins";

  show "option_filter phi (mdot ins) ! nat (int pc + branch) = Some (phi ! nat (int pc + branch))";
  proof (rule option_filter_Some);
    from 1; show "nat (int pc + branch) < length phi"; by simp;
    from 1;
    have "is_target ins (nat (int pc + branch))"; by (auto simp add: is_target_def);
    thus "mdot ins (nat (int pc + branch))"; by (simp add: mdot_def);
  qed;

next;
  fix branch;
  assume 2: "ins ! pc = BR (Ifcmpeq branch)" 
            "nat (int pc + branch) < length phi"
            "pc < length ins";

  show "option_filter phi (mdot ins) ! nat (int pc + branch) = Some (phi ! nat (int pc + branch))";
  proof (rule option_filter_Some);
    from 2; show "nat (int pc + branch) < length phi"; by simp;
    from 2;
    have "is_target ins (nat (int pc + branch))"; by (auto simp add: is_target_def);
    thus "mdot ins (nat (int pc + branch))"; by (simp add: mdot_def);
  qed;

qed;


lemma fits_make_cert:
  "length ins < length phi \\<Longrightarrow> fits ins (make_cert ins phi) phi";
proof -;
  assume l: "length ins < length phi";

  thus "fits ins (make_cert ins phi) phi";
  proof (unfold fits_def make_cert_def, intro conjI allI impI);
    show "is_approx (option_filter phi (mdot ins)) phi"; by (rule is_approx_option_filter);
    show "length ins < length phi"; .;

    fix pc;
    show "contains_dead ins (option_filter phi (mdot ins)) phi pc"; by (rule option_filter_contains_dead);
    
    assume "pc < length ins"; 
    thus "contains_targets ins (option_filter phi (mdot ins)) phi pc"; by (rule option_filter_contains_targets);
  qed;
qed;

lemma rev_surj: "\\<exists>a'. a = rev a'";
proof (induct "a"); 
  show "\\<exists>a'. [] = rev a'"; by simp;

  fix l ls; assume "\\<exists>a''. ls = rev a''";  
  thus "\\<exists>a'. l # ls = rev a'"; 
  proof (elim exE);
    fix a''; assume "ls = rev a''";
    hence "l#ls = rev (a''@[l])"; by simp;
    thus ?thesis; by blast;
  qed;
qed;

lemma append_length_n: "\\<forall>n. n \\<le> length x \\<longrightarrow> (\\<exists>a b. x = a@b \\<and> length a = n)" (is "?P x");
proof (induct "?P" "x");
  show "?P []"; by simp;

  fix l ls; assume Cons: "?P ls";

  show "?P (l#ls)";
  proof (intro allI impI);
    fix n;
    assume l: "n \\<le> length (l # ls)";

    show "\\<exists>a b. l # ls = a @ b \\<and> length a = n"; 
    proof (cases n);
      assume "n=0"; thus ?thesis; by simp;
    next;
      fix "n'"; assume s: "n = Suc n'";
      with l; 
      have  "n' \\<le> length ls"; by simp; 
      hence "\\<exists>a b. ls = a @ b \\<and> length a = n'"; by (rule Cons [rulify]);
      thus ?thesis;
      proof elim;
        fix a b; 
        assume "ls = a @ b" "length a = n'";
        with s;
        have "l # ls = (l#a) @ b \\<and> length (l#a) = n"; by simp;
        thus ?thesis; by blast;
      qed;
    qed;
  qed;
qed;



lemma rev_append_cons:
"\\<lbrakk>n < length x\\<rbrakk> \\<Longrightarrow> \\<exists>a b c. x = (rev a) @ b # c \\<and> length a = n";
proof -;
  assume n: "n < length x";
  hence "n \\<le> length x"; by simp;
  hence "\\<exists>a b. x = a @ b \\<and> length a = n"; by (rule append_length_n [rulify]);
  thus ?thesis;
  proof elim;
    fix r d; assume x: "x = r@d" "length r = n";
    with n;
    have bc: "\\<exists>b c. d = b#c"; by (simp add: neq_Nil_conv);
    
    have "\\<exists>a. r = rev a"; by (rule rev_surj);    
    with bc;
    show ?thesis;
    proof elim;
      fix a b c; 
      assume "r = rev a" "d = b#c";
      with x;
      have "x = (rev a) @ b # c \\<and> length a = n"; by simp;
      thus ?thesis; by blast;
    qed;
  qed;
qed;

lemma widen_NT: "G \\<turnstile> b \\<preceq> NT \\<Longrightarrow> b = NT";
proof (cases b); 
  case RefT;
  thus "G\\<turnstile>b\\<preceq>NT \\<Longrightarrow> b = NT"; by - (cases ref_ty, auto);
qed auto;

lemma widen_Class: "G \\<turnstile> b \\<preceq> Class C \\<Longrightarrow> \\<exists>r. b = RefT r";
by (cases b) auto;

lemma all_widen_is_sup_loc:
"\\<forall>b. length a = length b \\<longrightarrow> (\\<forall>x\\<in>set (zip a b). x \\<in> widen G) = (G \\<turnstile> (map Some a) <=l (map Some b))" 
 (is "\\<forall>b. length a = length b \\<longrightarrow> ?Q a b" is "?P a");
proof (induct "a");
  show "?P []"; by simp;

  fix l ls; assume Cons: "?P ls";

  show "?P (l#ls)"; 
  proof (intro allI impI);
    fix b; 
    assume "length (l # ls) = length (b::ty list)"; 
    with Cons;
    show "?Q (l # ls) b"; by - (cases b, auto);
  qed;
qed;

lemma method_inv_pseudo_mono:
"\\<lbrakk>fits ins cert phi; i = ins!pc; i = MI meth_inv; pc < length ins; 
  wf_prog wf_mb G;   G \\<turnstile> (x, y) <=s s1; wtl_inst (ins!pc) G rT s1 s1' cert mpc pc\\<rbrakk> 
 \\<Longrightarrow> \\<exists>s2'. wtl_inst i G rT (x, y) s2' cert mpc pc \\<and> \
          ((G \\<turnstile> s2' <=s s1') \\<or> (\\<exists> s. cert ! (Suc pc) = Some s \\<and> (G \\<turnstile> s2' <=s s)))";
proof (cases meth_inv); 
  case Invoke; 
  assume fits: "fits ins cert phi" and
         i: "i = ins ! pc" "i = MI meth_inv" and
         pc: "pc < length ins" and
         wfp: "wf_prog wf_mb G" and
         "wtl_inst (ins!pc) G rT s1 s1' cert mpc pc" and
         lt: "G \\<turnstile> (x, y) <=s s1";
 
  with Invoke; 
  show ?thesis; (* (is "\\<exists>s2'. ?wtl s2' \\<and> (?lt s2' s1' \\<or> ?cert s2')" is "\\<exists>s2'. ?P s2'"); *)
  proof (clarsimp_tac simp del: split_paired_Ex);
    fix apTs X  ST' y' s;

    assume G: "G \\<turnstile> (x, y) <=s (rev apTs @ X # ST', y')";
    assume lapTs: "length apTs = length list";
    assume "cert ! Suc pc = Some s"; 
    assume wtl: "s = s1' \\<and> X = NT \\<or>
            G \\<turnstile> s1' <=s s \\<and>
            (\\<exists>C. X = Class C \\<and>
                 (\\<forall>x\\<in>set (zip apTs list). x \\<in> widen G) \\<and>
                 (\\<exists>D rT. (\\<exists>b. method (G, C) (mname, list) = Some (D, rT, b)) \\<and>
                         (rT # ST', y') = s1'))" (is "?NT \\<or> ?ClassC");
    
    from G;
    have "\\<exists>a b c. x = rev a @ b # c \\<and> length a = length apTs";
      by - (rule rev_append_cons, simp add: sup_state_length_fst);

    thus "\\<exists>s2'. (\\<exists>apTs X ST'.
                   x = rev apTs @ X # ST' \\<and>
                   length apTs = length list \\<and>
                   (s = s2' \\<and> X = NT \\<or>
                    G \\<turnstile> s2' <=s s \\<and>
                    (\\<exists>C. X = Class C \\<and>
                         (\\<forall>x\\<in>set (zip apTs list). x \\<in> widen G) \\<and>
                         (\\<exists>D rT. (\\<exists>b. method (G, C) (mname, list) = Some (D, rT, b)) \\<and>
                                 (rT # ST', y) = s2')))) \\<and>
               (G \\<turnstile> s2' <=s s1' \\<or> G \\<turnstile> s2' <=s s)" (is "\\<exists>s2'. ?P s2'"); 
    proof elim;
      fix a b c;
      assume rac: "x = rev a @ b # c"; 
      with G;
      have x: "G \\<turnstile> (rev a @ b # c, y) <=s (rev apTs @ X # ST', y')"; by simp;

      assume l: "length a = length apTs";
      hence "length (rev a) = length (rev apTs)"; by simp;

      with x;
      have "G \\<turnstile> (rev a, y) <=s (rev apTs, y') \\<and> G \\<turnstile> (b # c, y) <=s (X # ST', y')";
        by - (rule sup_state_append_fst [elimify], blast+);

      hence x2: "G \\<turnstile> (a, y) <=s (apTs, y') \\<and> G \\<turnstile> b\\<preceq>X \\<and> G \\<turnstile> (c, y) <=s (ST', y')";
        by (simp add: sup_state_rev_fst sup_state_Cons1);

      show ?thesis;
      proof (cases "X = NT");
        case True;
        with x2;
        have "b = NT"; by (clarsimp_tac simp add: widen_NT);

        with rac l lapTs;
        have "?P s"; by auto;
        thus ?thesis; by blast;

      next;
        case False;

        with wtl; 
        have "\\<exists>C. X = Class C"; by clarsimp_tac;
        with x2;
        have "\\<exists>r. b = RefT r"; by (auto simp add: widen_Class);
        
        thus ?thesis;
        proof elim;
          fix r;
          assume b: "b = RefT r"; 
          show ?thesis;
          proof (cases r);
            case NullT;
            with b rac x2 l lapTs wtl False;
            have "?P s"; by auto;
            thus ?thesis; by blast;
          next;
            case ClassT;

            from False wtl;
            have wtlC: "?ClassC"; by simp;

            with b ClassT;
            show ?thesis;
            proof (elim exE conjE);
              fix C D rT body;
              assume ClassC: "X = Class C";
              assume zip: "\\<forall>x\\<in>set (zip apTs list). x \\<in> widen G";
              assume s1': "(rT # ST', y') = s1'";
              assume s: "G \\<turnstile> s1' <=s s";
              assume method: "method (G, C) (mname, list) = Some (D, rT, body)";  

              from ClassC b ClassT x2;
              have "G \\<turnstile> cname \\<preceq>C C"; by simp;
              with method wfp;
              have "\\<exists>D' rT' b'. method (G, cname) (mname, list) = Some (D', rT', b') \\<and> G \\<turnstile> rT'\\<preceq>rT";
                by - (rule subcls_widen_methd, blast);
              
              thus ?thesis;
              proof elim;
                fix D' rT' body';
                assume method': "method (G, cname) (mname, list) = Some (D', rT', body')" "G\\<turnstile>rT'\\<preceq>rT";

                have "?P (rT'#c,y)" (is "(\\<exists> apTs X ST'. ?A apTs X ST') \\<and> ?B"); 
                proof (intro conjI);
                  from s1' method' x2;
                  show "?B"; by (auto simp add: sup_state_Cons1);

                  from b ClassT rac l lapTs method'; 
                  have "?A a (Class cname) c"; 
                  proof (simp, intro conjI);

                    from method' x2;
                    have s': "G \\<turnstile> (rT' # c, y) <=s (rT # ST', y')"; 
                      by (auto simp add: sup_state_Cons1);
                    from s s1';
                    have "G \\<turnstile> (rT # ST', y') <=s s"; by simp;
                    with s'; 
                    show "G \\<turnstile> (rT' # c, y) <=s s"; by (rule sup_state_trans);

                    from x2;
                    have 1: "G \\<turnstile> map Some a <=l map Some apTs"; by (simp add: sup_state_def); 
                    from lapTs zip;
                    have "G \\<turnstile> map Some apTs <=l map Some list"; by (simp add: all_widen_is_sup_loc);
                    with 1;
                    have "G \\<turnstile> map Some a <=l map Some list"; by (rule sup_loc_trans);
                    with l lapTs;
                    show "\\<forall>x\\<in>set (zip a list). x \\<in> widen G"; by (simp add: all_widen_is_sup_loc);

                  qed;
                  thus "\\<exists> apTs X ST'. ?A apTs X ST'"; by blast;
                qed;
                thus ?thesis; by blast;
              qed;
            qed;  
          qed;
        qed;
      qed;
    qed;
  qed;
qed;

lemma sup_loc_some:
"\\<forall> y n. (G \\<turnstile> b <=l y) \\<longrightarrow> n < length y \\<longrightarrow> y!n = Some t \\<longrightarrow> (\\<exists>t. b!n = Some t \\<and> (G \\<turnstile> (b!n) <=o (y!n)))" (is "?P b");
proof (induct "?P" b);
  show "?P []"; by simp;

  case Cons;
  show "?P (a#list)";
  proof (clarsimp_tac simp add: list_all2_Cons1 sup_loc_def);
    fix z zs n;
    assume * : 
      "G \\<turnstile> a <=o z" "list_all2 (sup_ty_opt G) list zs" 
      "n < Suc (length zs)" "(z # zs) ! n = Some t";

    show "(\\<exists>t. (a # list) ! n = Some t) \\<and> G \\<turnstile>(a # list) ! n <=o Some t"; 
    proof (cases n); 
      case 0;
      with *; show ?thesis; by (simp add: sup_ty_opt_some);
    next;
      case Suc;
      with Cons *;
      show ?thesis; by (simp add: sup_loc_def);
    qed;
  qed;
qed;

lemma mono_load: 
"\\<lbrakk>G \\<turnstile> (a, b) <=s (x, y); n < length y; y!n = Some t\\<rbrakk> \\<Longrightarrow> \\<exists>ts. b!n = Some ts \\<and> G \\<turnstile> (ts#a, b) <=s (t#x, y)";
proof (clarsimp_tac simp add: sup_state_def);
  assume "G  \\<turnstile> b <=l y" "n < length y" "y!n = Some t";
  thus "\\<exists>ts. b ! n = Some ts \\<and> G\\<turnstile>ts\\<preceq>t";
   by (rule sup_loc_some [rulify, elimify], clarsimp_tac);
qed;
  
lemma mono_store:
"\\<lbrakk>G \\<turnstile> (a, b) <=s (ts # ST', y); n < length y\\<rbrakk> \\<Longrightarrow> 
  \\<exists> t a'. a = t#a' \\<and> G \\<turnstile> (a', b[n := Some t]) <=s (ST', y[n := Some ts])";
proof (clarsimp_tac simp add: sup_state_def sup_loc_Cons2);
  fix Y YT';
  assume * : "n < length y" "G \\<turnstile> b <=l y" "G \\<turnstile>Y <=o Some ts" "G \\<turnstile> YT' <=l map Some ST'";
  assume "map Some a = Y # YT'";
  hence "map Some (tl a) = YT' \\<and> Some (hd a) = Y \\<and> (\\<exists>y yt. a = y # yt)";
    by (rule map_hd_tl);
  with *; 
  show "\\<exists>t a'. a = t # a' \\<and> G \\<turnstile> map Some a' <=l map Some ST' \\<and> G \\<turnstile> b[n := Some t] <=l y[n := Some ts]";
    by (clarsimp_tac simp add: sup_loc_update);
qed;


lemma PrimT_PrimT: "(G \\<turnstile> xb \\<preceq> PrimT p) = (xb = PrimT p)";
proof;
  show "xb = PrimT p \\<Longrightarrow> G \\<turnstile> xb \\<preceq> PrimT p"; by blast;

  show "G\\<turnstile> xb \\<preceq> PrimT p \\<Longrightarrow> xb = PrimT p";
  proof (cases xb); print_cases;
    fix prim;
    assume "xb = PrimT prim" "G\\<turnstile>xb\\<preceq>PrimT p";
    thus ?thesis; by simp;
  next;
    fix ref;
    assume "G\\<turnstile>xb\\<preceq>PrimT p" "xb = RefT ref";
    thus ?thesis; by simp (rule widen_RefT [elimify], auto);
  qed;
qed;


lemma wtl_inst_pseudo_mono:
"\\<lbrakk>wtl_inst i G rT s1 s1' cert mpc pc; fits ins cert phi; pc < length ins; wf_prog wf_mb G; 
  G \\<turnstile> s2 <=s s1; i = ins!pc\\<rbrakk> \\<Longrightarrow> 
 \\<exists> s2'. wtl_inst (ins!pc) G rT s2 s2' cert mpc pc \\<and> (G \\<turnstile> s2' <=s s1' \\<or> (\\<exists>s. cert!(Suc pc) = Some s \\<and> G \\<turnstile> s2' <=s s))";
proof (simp only:);
  assume 1 : "wtl_inst (ins ! pc) G rT s1 s1' cert mpc pc" "G \\<turnstile> s2 <=s s1" "pc < length ins";
  assume 2 : "fits ins cert phi" "wf_prog wf_mb G" "i = ins!pc";

  have 3: "\\<exists> a b. s2 = (a,b)"; by simp;

  show ?thesis; 
  proof (cases "ins ! pc");

    case LS;
    show ?thesis;
    proof (cases "load_and_store");
      case Load;
      with LS 1 3;
      show ?thesis; by (elim, clarsimp_tac) (rule mono_load [elimify], auto simp add: sup_state_length_snd);
    next;
      case Store;
      with LS 1 3; 
      show ?thesis; by (elim, clarsimp_tac) (rule mono_store [elimify], auto simp add: sup_state_length_snd);
    next;
      case Bipush;
      with LS 1 3;
      show ?thesis; by (elim, clarsimp_tac simp add: sup_state_Cons1);
    next;
      case Aconst_null;
      with LS 1 3;
      show ?thesis; by (elim, clarsimp_tac simp add: sup_state_Cons1);
    qed;

  next;
    case CO;
    show ?thesis;
    proof (cases create_object);
      case New;
      with CO 1 3;
      show ?thesis; by (elim, clarsimp_tac simp add: sup_state_Cons1);
    qed;

  next;
    case MO;
    show ?thesis;
    proof (cases manipulate_object);
      case Getfield;
      with MO 1 3;
      show ?thesis;
      proof (elim, clarsimp_tac simp add: sup_state_Cons2);       
        fix oT x;
        assume "G \\<turnstile> x \\<preceq> oT" "G \\<turnstile> oT \\<preceq> Class cname"; 
        show "G \\<turnstile> x \\<preceq> Class cname"; by (rule widen_trans);
      qed;
    next;
      case Putfield;
      with MO 1 3;
      show ?thesis;
      proof (elim, clarsimp_tac simp add: sup_state_Cons2);       
        fix x xa vT oT T;
        assume "G \\<turnstile> x \\<preceq> vT" "G \\<turnstile> vT \\<preceq> T";
        hence * : "G \\<turnstile> x \\<preceq> T"; by (rule widen_trans);
        
        assume "G \\<turnstile> xa \\<preceq> oT" "G \\<turnstile> oT \\<preceq> Class cname"; 
        hence "G \\<turnstile> xa \\<preceq> Class cname"; by (rule widen_trans);
        
        with *;
        show "(G \\<turnstile> xa \\<preceq> Class cname) \\<and> (G \\<turnstile> x \\<preceq> T)"; by blast;
      qed;
    qed;

  next;
    case CH;
    show ?thesis;
    proof (cases check_object);
      case Checkcast;
      with CH 1 3;
      show ?thesis; by (elim, clarsimp_tac simp add: sup_state_Cons2) (rule widen_RefT2);
    qed;

  next;
    case MI;
    with 1 2 3;
    show ?thesis; by elim (rule method_inv_pseudo_mono [elimify], simp+); 

  next;
    case MR;
    show ?thesis;
    proof (cases meth_ret);
      case Return;
      with MR 1 3;
      show ?thesis; 
      proof (elim, clarsimp_tac simp add: sup_state_Cons2 simp del: split_paired_Ex);
        fix x T;
        assume "G\\<turnstile>x\\<preceq>T" "G\\<turnstile>T\\<preceq>rT";
        thus "G\\<turnstile>x\\<preceq>rT"; by (rule widen_trans);
      qed;
    qed;

  next;
    case OS;
    with 1 3;
    show ?thesis; 
      by - (cases op_stack, (elim, clarsimp_tac simp add: sup_state_Cons2)+);

  next;
    case BR;
    show ?thesis;
    proof (cases branch);
      case Goto;
      with BR 1 3;
      show ?thesis;
      proof (elim, clarsimp_tac simp del: split_paired_Ex);
        fix a b x y;
        assume "G \\<turnstile> (a, b) <=s s1" "G \\<turnstile> s1 <=s (x, y)";
        thus "G \\<turnstile> (a, b) <=s (x, y)"; by (rule sup_state_trans);
      qed;
    next;
      case Ifcmpeq;
      with BR 1 3;
      show ?thesis;
      proof (elim, clarsimp_tac simp add: sup_state_Cons2, intro conjI);
        fix xt' b ST' y c d;
        assume "G \\<turnstile> (xt', b) <=s (ST', y)" "G \\<turnstile> (ST', y) <=s (c, d)";
        thus "G \\<turnstile> (xt', b) <=s (c, d)"; by (rule sup_state_trans);
      next;
        fix ts ts' x xa;
        assume * :
        "(\\<exists>p. ts = PrimT p \\<and> ts' = PrimT p) \\<or> (\\<exists>r. ts = RefT r) \\<and> (\\<exists>r'. ts' = RefT r')";

        assume x: "G\\<turnstile>x\\<preceq>ts" "G\\<turnstile>xa\\<preceq>ts'";

        show "(\\<exists>p. x = PrimT p \\<and> xa = PrimT p) \\<or> (\\<exists>r. x = RefT r) \\<and> (\\<exists>r'. xa = RefT r')"; 
        proof (cases x);
          case PrimT;
          with * x;
          show ?thesis; by (auto simp add: PrimT_PrimT);
        next;
          case RefT;
          hence 1: "\\<exists>r. x = RefT r"; by blast;
          
          have "\\<exists>r'. xa = RefT r'";
          proof (cases xa); 
            case PrimT;
            with RefT * x;
            have "False"; by auto (rule widen_RefT [elimify], auto); 
            thus ?thesis; by blast;
          qed blast;

          with 1;
          show ?thesis; by blast;
        qed;
      qed;
    qed;
  qed;
qed;
 
lemma wtl_inst_last_mono:
"\\<lbrakk>wtl_inst i G rT s1 s1' cert (Suc pc) pc; G \\<turnstile> s2 <=s s1\\<rbrakk> \\<Longrightarrow> 
 \\<exists>s2'. wtl_inst i G rT s2 s2' cert (Suc pc) pc \\<and> (G \\<turnstile> s2' <=s s1')";
proof -;
  assume * : "wtl_inst i G rT s1 s1' cert (Suc pc) pc" "G \\<turnstile> s2 <=s s1";
  
  show ?thesis;
  proof (cases i);
    case LS; with *;
    show ?thesis; by - (cases load_and_store, simp+);
  next;
    case CO; with *;
    show ?thesis; by - (cases create_object, simp);
  next;
    case MO; with *;
    show ?thesis; by - (cases manipulate_object, simp+);
  next;
    case CH; with *;
    show ?thesis; by - (cases check_object, simp);
  next;
    case MI; with *;
    show ?thesis; by - (cases meth_inv, simp);
  next;
    case OS; with *;
    show ?thesis; by - (cases op_stack, simp+); 
  next;
    case MR; 
    show ?thesis;
    proof (cases meth_ret);
      case Return; with MR *;
      show ?thesis; 
        by (clarsimp_tac simp del: split_paired_Ex simp add: sup_state_Cons2)
           (rule widen_trans, blast+);
    qed;
  next;
    case BR;
    show ?thesis;
    proof (cases branch);
      case Ifcmpeq; with BR *;
      show ?thesis; by simp;
    next;
      case Goto; with BR *;
      show ?thesis;  
      by (clarsimp_tac simp del: split_paired_Ex simp add: sup_state_Cons2)
         (rule sup_state_trans, blast+);
    qed;
  qed;
qed;

lemma wtl_option_last_mono:
"\\<lbrakk>wtl_inst_option i G rT s1 s1' cert mpc pc; mpc = Suc pc; G \\<turnstile> s2 <=s s1\\<rbrakk> \\<Longrightarrow> 
 \\<exists>s2'. wtl_inst_option i G rT s2 s2' cert mpc pc \\<and> (G \\<turnstile> s2' <=s s1')";
proof (simp only: ); 
  assume G: "G \\<turnstile> s2 <=s s1";
  assume w: "wtl_inst_option i G rT s1 s1' cert (Suc pc) pc"; 
  
  show "\\<exists>s2'. wtl_inst_option i G rT s2 s2' cert (Suc pc) pc \\<and> (G \\<turnstile> s2' <=s s1')";
  proof (cases "cert!pc");
    case None;
    with G w;
    show ?thesis; by (simp add: wtl_inst_option_def wtl_inst_last_mono del: split_paired_Ex); 
  next;
    case Some;
    with G w;
    have o: "G \\<turnstile> s1 <=s a \\<and> wtl_inst i G rT a s1' cert (Suc pc) pc"; 
      by (simp add: wtl_inst_option_def);
    hence w' : "wtl_inst i G rT a s1' cert (Suc pc) pc"; ..;

    from o G;
    have G' : "G \\<turnstile> s2 <=s a"; by - (rule sup_state_trans, blast+); 

    from o;
    have "\\<exists>s2'. wtl_inst i G rT a s2' cert (Suc pc) pc \\<and> G \\<turnstile> s2' <=s s1'";
      by elim (rule wtl_inst_last_mono, auto);

    with Some w G';
    show ?thesis; by (auto simp add: wtl_inst_option_def);  
  qed;
qed;

lemma wt_instr_imp_wtl_inst:
"\\<lbrakk>wt_instr (ins!pc) G rT phi max_pc pc; fits ins cert phi;
  pc < length ins; length ins = max_pc\\<rbrakk> \\<Longrightarrow> 
  \\<exists> s. wtl_inst (ins!pc) G rT (phi!pc) s cert max_pc pc \\<and> G \\<turnstile> s <=s phi ! Suc pc";
proof -;
  assume * : "wt_instr (ins!pc) G rT phi max_pc pc" "fits ins cert phi"
             "pc < length ins" "length ins = max_pc";

  have xy: "\\<exists> x y. phi!pc = (x,y)"; by simp;

  show ?thesis;
  proof (cases "ins!pc");
    case LS; with * xy;
    show ?thesis; 
      by - (cases load_and_store, (elim, force simp add: wt_instr_def)+); 
  next;
    case CO; with * xy;
    show ?thesis;
      by - (cases create_object, (elim, force simp add: wt_instr_def)+); 
  next;
    case MO; with * xy;
    show ?thesis;
      by - (cases manipulate_object, (elim, force simp add: wt_instr_def)+);
  next; 
    case CH; with * xy;
    show ?thesis;
      by - (cases check_object, (elim, force simp add: wt_instr_def)+);
  next;
    case OS; with * xy;
    show ?thesis;
      by - (cases op_stack, (elim, force simp add: wt_instr_def)+);
  next;
    case MR; with * xy;
    show ?thesis;
    by - (cases meth_ret, elim, 
      clarsimp_tac simp add: wt_instr_def fits_def contains_dead_def simp del: split_paired_Ex);
  next;
    case BR; with * xy;
    show ?thesis; 
      by - (cases branch,
           (clarsimp_tac simp add: wt_instr_def fits_def contains_dead_def contains_targets_def 
                         simp del: split_paired_Ex)+);
  next;
    case MI;
    show ?thesis;
    proof (cases meth_inv);
      case Invoke;
      with MI * xy;
      show ?thesis; 
      proof (elim, clarsimp_tac simp add: wt_instr_def simp del: split_paired_Ex);
        fix y apTs X ST'; 
        assume pc : "Suc pc < length ins"; 
        assume phi : "phi ! pc = (rev apTs @ X # ST', y)" "length apTs = length list";
        assume ** :
               "X = NT \\<or> (\\<exists>C. X = Class C \\<and>
               (\\<forall>x\\<in>set (zip apTs list). x \\<in> widen G) \\<and>
               (\\<exists>D rT. (\\<exists>b. method (G, C) (mname, list) = Some (D, rT, b)) \\<and> G \\<turnstile> (rT # ST', y) <=s phi ! Suc pc))"
               (is "?NT \\<or> ?CL"); 

        
        from MI Invoke pc *;
        have cert: "cert ! Suc pc = Some (phi ! Suc pc)"; by (clarsimp_tac simp add: fits_def contains_dead_def); 


        show "\\<exists>s. (\\<exists>apTsa Xa ST'a.
                 rev apTs @ X # ST' = rev apTsa @ Xa # ST'a \\<and>
                 length apTsa = length list \\<and>
                 (\\<exists>s''. cert ! Suc pc = Some s'' \\<and>
                        (s'' = s \\<and> Xa = NT \\<or>
                         G \\<turnstile> s <=s s'' \\<and>
                         (\\<exists>C. Xa = Class C \\<and>
                              (\\<forall>x\\<in>set (zip apTsa list). x \\<in> widen G) \\<and>
                              (\\<exists>D rT. (\\<exists>b. method (G, C) (mname, list) = Some (D, rT, b)) \\<and> (rT # ST'a, y) = s))))) \\<and>
               G \\<turnstile> s <=s phi ! Suc pc" (is "\\<exists>s. ?P s");  
        proof (cases "X=NT"); 
          case True;
          with cert phi **;
          have "?P (phi ! Suc pc)"; by (force simp del: split_paired_Ex);
          thus ?thesis; by blast;
        next;
          case False;
          with **;

          have "?CL"; by simp;

          thus ?thesis; 
          proof (elim exE conjE);
            fix C D rT b;
            assume "X = Class C" "\\<forall>x\\<in>set (zip apTs list). x \\<in> widen G" 
                   "G \\<turnstile> (rT # ST', y) <=s phi ! Suc pc"
                   "method (G, C) (mname, list) = Some (D, rT, b)";
            with cert phi;
            have "?P (rT #ST', y)"; by (force simp del: split_paired_Ex); 
            thus ?thesis; by blast;
          qed;
        qed;
      qed;
    qed;
  qed;
qed;

  
lemma wt_instr_imp_wtl_option:
"\\<lbrakk>fits ins cert phi; pc < length ins; wt_instr (ins!pc) G rT phi max_pc pc;  max_pc = length ins\\<rbrakk> \\<Longrightarrow> 
 \\<exists> s. wtl_inst_option (ins!pc) G rT (phi!pc) s cert max_pc pc \\<and> G \\<turnstile> s <=s phi ! Suc pc";
proof -;
  assume fits : "fits ins cert phi" "pc < length ins" 
         and "wt_instr (ins!pc) G rT phi max_pc pc" 
             "max_pc = length ins";

  hence * : "\\<exists> s. wtl_inst (ins!pc) G rT (phi!pc) s cert max_pc pc \\<and> G \\<turnstile> s <=s phi ! Suc pc";
    by - (rule wt_instr_imp_wtl_inst, simp+);
  
  show ?thesis;
  proof (cases "cert ! pc");
    case None;
    with *;
    show ?thesis; by (simp add: wtl_inst_option_def);

  next;
    case Some;

    from fits; 
    have "pc < length phi"; by (clarsimp_tac simp add: fits_def);
    with fits Some;
    have "cert ! pc = Some (phi!pc)"; by (auto simp add: fits_def is_approx_def);
     
    with *; 
    show ?thesis; by (simp add: wtl_inst_option_def);
  qed;
qed;

(* not needed 
lemma wtl_inst_list_s:
"\\<lbrakk>wtl_inst_list ins G rT s0 s' cert max_pc pc; ins \\<noteq> []; G \\<turnstile> s <=s s0; s \\<noteq> s0 \\<longrightarrow> cert ! pc = Some s0\\<rbrakk> \\<Longrightarrow> 
  wtl_inst_list ins G rT s s' cert max_pc pc";  
proof -;
  assume * : "wtl_inst_list ins G rT s0 s' cert max_pc pc" 
             "ins \\<noteq> []" "G \\<turnstile> s <=s s0" 
             "s \\<noteq> s0 \\<longrightarrow> cert ! pc = Some s0";

  show ?thesis;
  proof (cases ins);
    case Nil;
    with *;
    show ?thesis; by simp;
  next;
    case Cons;

    show ?thesis; 
    proof (cases "list = []");
      case True;
      with Cons *;
      show ?thesis; by - (cases "s = s0", (simp add: wtl_inst_option_def)+);
    next;
      case False;
      with Cons *;
      show ?thesis; by (force simp add: wtl_inst_option_def);
    qed; 
  qed;
qed;


lemma wtl_inst_list_cert:
"\\<lbrakk>wtl_inst_list ins G rT s0 s' cert max_pc pc; ins \\<noteq> []; G \\<turnstile> s <=s s0; cert ! pc = Some s0\\<rbrakk> \\<Longrightarrow> 
  wtl_inst_list ins G rT s s' cert max_pc pc";
by (cases ins) (force simp add: wtl_inst_option_def)+;
*)

lemma wtl_option_pseudo_mono:
"\\<lbrakk>wtl_inst_option i G rT s1 s1' cert mpc pc;  fits ins cert phi; pc < length ins; 
  wf_prog wf_mb G; G \\<turnstile> s2 <=s s1; i = ins!pc\\<rbrakk> \\<Longrightarrow> 
 \\<exists> s2'. wtl_inst_option (ins!pc) G rT s2 s2' cert mpc pc \\<and> 
        (G \\<turnstile> s2' <=s s1' \\<or> (\\<exists>s. cert!(Suc pc) = Some s \\<and> G \\<turnstile> s2' <=s s))";
proof -;
  assume wtl:  "wtl_inst_option i G rT s1 s1' cert mpc pc" and
         fits: "fits ins cert phi" "pc < length ins"
               "wf_prog wf_mb G" "G \\<turnstile> s2 <=s s1" "i = ins!pc";

  show ?thesis;
  proof (cases "cert!pc");
    case None;
    with wtl fits;
    show ?thesis; 
      by - (rule wtl_inst_pseudo_mono [elimify], (simp add: wtl_inst_option_def)+);
  next;
    case Some;
    with wtl fits;

    have G: "G \\<turnstile> s2 <=s a";
     by - (rule sup_state_trans, (simp add: wtl_inst_option_def)+);

    from Some wtl;
    have "wtl_inst i G rT a s1' cert mpc pc"; by (simp add: wtl_inst_option_def);

    with G fits;
    have "\\<exists> s2'. wtl_inst (ins!pc) G rT a s2' cert mpc pc \\<and> 
                 (G \\<turnstile> s2' <=s s1' \\<or> (\\<exists>s. cert!(Suc pc) = Some s \\<and> G \\<turnstile> s2' <=s s))";
      by - (rule wtl_inst_pseudo_mono, (simp add: wtl_inst_option_def)+);
    
    with Some G;
    show ?thesis; by (simp add: wtl_inst_option_def);
  qed;
qed;

lemma append_cons_length_nth: "((l @ a # list) ! length l) = a"; 
  by (induct l, auto);


(* main induction over instruction list *)
theorem wt_imp_wtl_inst_list:
"\\<forall> pc. (\\<forall>pc'. pc' < length ins \\<longrightarrow> wt_instr (ins ! pc') G rT phi (pc+length ins) (pc+pc')) \\<longrightarrow>   
       wf_prog wf_mb G \\<longrightarrow> 
       fits all_ins cert phi \\<longrightarrow> (\\<exists> l. pc = length l \\<and> all_ins=l@ins) \\<longrightarrow> pc < length all_ins \\<longrightarrow>
       (\\<forall> s. (G \\<turnstile> s <=s (phi!pc)) \\<longrightarrow> 
       (\\<exists>s'. wtl_inst_list ins G rT s s' cert (pc+length ins) pc))" 
(is "\\<forall>pc. ?C pc ins" is "?P ins");
proof (induct "?P" "ins");
  case Nil;
  show "?P []"; by simp;
next;
  case Cons;

  show "?P (a#list)";
  proof (intro allI impI, elim exE conjE);
    fix pc s l;
    assume 1: "wf_prog wf_mb G" "fits all_ins cert phi";
    assume 2: "pc < length all_ins" "G \\<turnstile> s <=s phi ! pc"
              "all_ins = l @ a # list" "pc = length l";

    from Cons;
    have IH: "?C (Suc pc) list"; by blast;

    assume 3: "\\<forall>pc'. pc' < length (a # list) \\<longrightarrow>
               wt_instr ((a # list) ! pc') G rT phi (pc + length (a # list)) (pc + pc')";
    hence 4: "\\<forall>pc'. pc' < length list \\<longrightarrow>
              wt_instr (list ! pc') G rT phi (Suc pc + length list) (Suc pc + pc')"; by auto;    

    from 2; 
    have 5: "a = all_ins ! pc"; by (simp add: append_cons_length_nth);


    show "\\<exists>s'. wtl_inst_list (a # list) G rT s s' cert (pc + length (a # list)) pc"; 
    proof (cases list);
      case Nil;

      with 1 2 3 5; 
      have "\\<exists>s'. wtl_inst_option a G rT (phi ! pc) s' cert (Suc (length l)) pc";
        by - (rule wt_instr_imp_wtl_option [elimify], force+);

      with Nil 1 2 5;
      have "\\<exists>s'. wtl_inst_option a G rT s s' cert (Suc (length l)) pc";
        by elim (rule wtl_option_pseudo_mono [elimify], force+); 

      with Nil 2;
      show ?thesis; by auto;
    next;
      fix i' ins'; 
      assume Cons2: "list = i' # ins'";

      with IH 1 2 3;
      have * : "\\<forall> s. (G \\<turnstile> s <=s (phi!(Suc pc))) \\<longrightarrow> 
                     (\\<exists>s'. wtl_inst_list list G rT s s' cert ((Suc pc)+length list) (Suc pc))";
        by (elim impE) force+;

      from 3;
      have "wt_instr a G rT phi (pc + length (a # list)) pc"; by auto;
      
      with 1 2 5;
      have "\\<exists>s1'. wtl_inst_option a G rT (phi!pc) s1' cert (Suc (pc + length list)) pc \\<and> G \\<turnstile> s1' <=s phi ! Suc pc";
        by - (rule wt_instr_imp_wtl_option [elimify], assumption+, simp+);

      hence "\\<exists>s1. wtl_inst_option a G rT s s1 cert (Suc (pc + length list)) pc \\<and>
                  (G \\<turnstile> s1 <=s (phi ! (Suc pc)) \\<or> (\\<exists>s. cert ! Suc pc = Some s \\<and> G \\<turnstile> s1 <=s s))";
      proof elim; 
        fix s1';
        assume "wtl_inst_option a G rT (phi!pc) s1' cert (Suc (pc + length list)) pc" and
            a :"G \\<turnstile> s1' <=s phi ! Suc pc";
        with 1 2 5;
        have "\\<exists>s1. wtl_inst_option a G rT s s1 cert (Suc (pc + length list)) pc \\<and>
                   ((G \\<turnstile> s1 <=s s1') \\<or> (\\<exists>s. cert ! Suc pc = Some s \\<and> G \\<turnstile> s1 <=s s))";
          by - (rule wtl_option_pseudo_mono [elimify], simp+);

        with a;
        show ?thesis;
        proof (elim, intro);
          fix s1;
          assume "G \\<turnstile> s1 <=s s1'" "G \\<turnstile> s1' <=s phi ! Suc pc";
          show "G \\<turnstile> s1 <=s phi ! Suc pc"; by (rule sup_state_trans);
        qed auto;
      qed;

      thus ?thesis;
      proof (elim exE conjE); 
        fix s1;
        assume wto: "wtl_inst_option a G rT s s1 cert (Suc (pc + length list)) pc"; 
        assume Gs1: "G \\<turnstile> s1 <=s phi ! Suc pc \\<or> (\\<exists>s. cert ! Suc pc = Some s \\<and> G \\<turnstile> s1 <=s s)";
        
        have "\\<exists>s'. wtl_inst_list list G rT s1 s' cert ((Suc pc)+length list) (Suc pc)"; 
        proof (cases "G \\<turnstile> s1 <=s phi ! Suc pc");
          case True;
          with Gs1;
          have "G \\<turnstile> s1 <=s phi ! Suc pc"; by simp;
          with *;
          show ?thesis; by blast;
        next;
          case False;
          with Gs1;
          have "\\<exists>c. cert ! Suc pc = Some c \\<and> G \\<turnstile> s1 <=s c"; by simp;
          thus ?thesis;
          proof elim;
            from 1 2 Cons Cons2;
            have "Suc pc < length phi";  by (clarsimp_tac simp add: fits_def is_approx_def); 

            with 1;
            have cert: "cert ! (Suc pc) = None \\<or> cert ! (Suc pc) = Some (phi ! Suc pc)"; 
              by (clarsimp_tac simp add: fits_def is_approx_def); 

            fix c;
            assume "cert ! Suc pc = Some c"; 
            with cert;
            have c: "c = phi ! Suc pc"; by simp;
            assume "G \\<turnstile> s1 <=s c";
            with c;
            have "G \\<turnstile> s1 <=s phi ! Suc pc"; by simp;
            with *;
            show ?thesis; by blast;
          qed;
        qed;
        with wto;
        show ?thesis; by (auto simp del: split_paired_Ex);
      qed;
    qed; 
  qed;
qed;


lemma fits_imp_wtl_method_complete:
"\\<lbrakk>wt_method G C pTs rT mxl ins phi; fits ins cert phi; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> wtl_method G C pTs rT mxl ins cert";
by (simp add: wt_method_def wtl_method_def del: split_paired_Ex)
   (rule wt_imp_wtl_inst_list [rulify, elimify], auto simp add: wt_start_def simp del: split_paired_Ex); 


lemma wtl_method_complete:
"\\<lbrakk>wt_method G C pTs rT mxl ins phi; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> wtl_method G C pTs rT mxl ins (make_cert ins phi)";
proof -;
  assume * : "wt_method G C pTs rT mxl ins phi" "wf_prog wf_mb G";
  
  hence "fits ins (make_cert ins phi) phi";
    by - (rule fits_make_cert, simp add: wt_method_def);

  with *;
  show ?thesis; by - (rule fits_imp_wtl_method_complete);
qed;

(*
Goalw[wt_jvm_prog_def, wfprg_def] "\\<lbrakk>wt_jvm_prog G Phi\\<rbrakk> \\<Longrightarrow> wfprg G";
by Auto_tac;
qed "wt_imp_wfprg";
*)

lemma unique_set:
"(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (a',b',c',d') \\<in> set l \\<longrightarrow> a = a' \\<longrightarrow> b=b' \\<and> c=c' \\<and> d=d'";
  by (induct "l") auto;

lemma unique_epsilon:
"(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (\\<epsilon> (a',b',c',d'). (a',b',c',d') \\<in> set l \\<and> a'=a) = (a,b,c,d)";
  by (auto simp add: unique_set);


theorem wtl_complete: "\\<lbrakk>wt_jvm_prog G Phi\\<rbrakk> \\<Longrightarrow> wtl_jvm_prog G (make_Cert G Phi)";
proof (simp only: wt_jvm_prog_def);

  assume wfprog: "wf_prog (\\<lambda>G C (sig,rT,maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) G";

  thus ?thesis; 
  proof (simp add: wtl_jvm_prog_def wf_prog_def wf_cdecl_def wf_mdecl_def, auto);
    fix a aa ab b ac ba ad ae bb; 
    assume 1 : "\\<forall>(C,sc,fs,ms)\\<in>set G.
             Ball (set fs) (wf_fdecl G) \\<and>
             unique fs \\<and>
             (\\<forall>(sig,rT,mb)\\<in>set ms. wf_mhead G sig rT \\<and> (\\<lambda>(maxl,b). wt_method G C (snd sig) rT maxl b (Phi C sig)) mb) \\<and>
             unique ms \\<and>
             (case sc of None \\<Rightarrow> C = Object
              | Some D \\<Rightarrow>
                  is_class G D \\<and>
                  (D, C) \\<notin> (subcls1 G)^* \\<and>
                  (\\<forall>(sig,rT,b)\\<in>set ms. \\<forall>D' rT' b'. method (G, D) sig = Some (D', rT', b') \\<longrightarrow> G\\<turnstile>rT\\<preceq>rT'))"
             "(a, aa, ab, b) \\<in> set G";
  
    assume uG : "unique G"; 
    assume b  : "((ac, ba), ad, ae, bb) \\<in> set b";

    from 1;
    show "wtl_method G a ba ad ae bb (make_Cert G Phi a (ac, ba))";
    proof (rule bspec [elimify], clarsimp_tac);
      assume ub : "unique b";
      assume m: "\\<forall>(sig,rT,mb)\\<in>set b. wf_mhead G sig rT \\<and> (\\<lambda>(maxl,b). wt_method G a (snd sig) rT maxl b (Phi a sig)) mb"; 
      from m b;
      show ?thesis;
      proof (rule bspec [elimify], clarsimp_tac);
        assume "wt_method G a ba ad ae bb (Phi a (ac, ba))";         
        with wfprog uG ub b 1;
        show ?thesis;
          by - (rule wtl_method_complete [elimify], assumption+, simp add: make_Cert_def unique_epsilon);
      qed; 
    qed;
  qed;
qed;

end;
