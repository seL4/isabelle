Goal "\\<forall> n. length (option_filter_n l P n) = length l";
by (induct_tac "l" 1);
by Auto_tac;
qed_spec_mp "length_option_filter_n";

Goalw[is_approx_def] "\\<forall> n. is_approx (option_filter_n a P n) a";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "P n" 1);
 by (Clarsimp_tac 1);
 by (exhaust_tac "na" 1);
  by (Clarsimp_tac 1);
 by (clarsimp_tac (claset(), simpset() addsimps [length_option_filter_n]) 1);
 by (Force_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "na" 1);
 by (Clarsimp_tac 1);
by (force_tac (claset(), simpset() addsimps [length_option_filter_n]) 1);
qed_spec_mp "is_approx_option_filter_n";

Goalw[option_filter_def] "is_approx (option_filter l P) l";
by (simp_tac (simpset() addsimps [is_approx_option_filter_n]) 1);
qed "is_approx_option_filter";


Goal "\\<forall>n n'. n < length l \\<longrightarrow> P (n+n') \\<longrightarrow> option_filter_n l P n' ! n = Some (l!n)";
by (induct_tac "l" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (exhaust_tac "n" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
qed_spec_mp "option_filter_n_Some";

Goalw [option_filter_def]
"\\<lbrakk>n < length l; P n\\<rbrakk> \\<Longrightarrow> option_filter l P ! n = Some (l!n)";
br option_filter_n_Some 1;
 ba 1;
by (Asm_simp_tac 1);
qed "option_filter_Some";

Goal "\\<lbrakk>length ins < length phi;  pc < length ins\\<rbrakk> \\<Longrightarrow> \
\      contains_dead ins (option_filter phi (mdot ins)) phi pc";
by (asm_full_simp_tac (simpset() addsimps [contains_dead_def]) 1);
br conjI 1;
br conjI 2;
by (ALLGOALS (Clarsimp_tac 
        THEN' (rtac option_filter_Some) 
        THEN' Asm_simp_tac 
        THEN' (clarsimp_tac (claset(), simpset() addsimps [mdot_def,maybe_dead_def]))));
qed "option_filter_contains_dead";

Goal "\\<lbrakk>length ins < length phi;  pc < length ins\\<rbrakk> \\<Longrightarrow> \
\      contains_targets ins (option_filter phi (mdot ins)) phi pc"; 
by (asm_full_simp_tac (simpset() addsimps [contains_targets_def]) 1);
by (Clarsimp_tac 1);
br conjI 1;
by (ALLGOALS (Clarsimp_tac 
        THEN' (rtac option_filter_Some) 
        THEN' Asm_simp_tac 
        THEN' (asm_full_simp_tac (simpset() addsimps [mdot_def,is_target_def]))
        THEN' Force_tac));
qed "option_filter_contains_targets";

Goalw[fits_def, make_cert_def] "length ins < length phi \\<Longrightarrow> fits ins (make_cert ins phi) phi";
by (Clarsimp_tac 1);
br conjI 1;
 br is_approx_option_filter 1;
by (Clarsimp_tac 1);
br conjI 1;
 br option_filter_contains_dead 1;
  ba 1;
 ba 1;
br option_filter_contains_targets 1;
 ba 1;
ba 1;
qed "fits_make_cert";


Goal "\\<exists>a'. a = rev a'"; 
by (induct_tac "a" 1); 
 by (Simp_tac 1);
by (Clarsimp_tac 1);
by (res_inst_tac [("x","a'@[a]")] exI 1);
by (Simp_tac 1);
qed "rev_surj";

Goal "\\<forall>n. n \\<le> length x \\<longrightarrow> (\\<exists>a b. x = a@b \\<and> length a = n)";
by (induct_tac "x" 1);
 by (Simp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "n" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (smp_tac 1 1);
by (Clarsimp_tac 1);
by (res_inst_tac [("x","a#aa")] exI 1);
by (Simp_tac 1);
qed_spec_mp "append_length_n";

Goal "\\<lbrakk>n < length x\\<rbrakk> \\<Longrightarrow> \\<exists>a b c. x = (rev a) @ b # c \\<and> length a = n";
by (subgoal_tac "n \\<le> length x" 1);
 by (Asm_full_simp_tac 2);
by (forward_tac [append_length_n] 1);
by (Clarsimp_tac 1);
by (cut_inst_tac [("xs","b")] neq_Nil_conv 1);
by (Clarsimp_tac 1);
by (cut_inst_tac [("a","a")] rev_surj 1);
by (Clarsimp_tac 1);
by (res_inst_tac [("x","a'")] exI 1);
by (Clarsimp_tac 1);
qed "rev_append_cons";


Goal "\\<forall>b. length a = length b \\<longrightarrow> (G \\<turnstile> (a@x) <=l (b@y)) = ((G \\<turnstile> a <=l b) \\<and> (G \\<turnstile> x <=l y))";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarify_tac 1);
by (exhaust_tac "b" 1);
 by (Clarsimp_tac 1);  
by (Clarsimp_tac 1);
qed_spec_mp "sup_loc_append";


Goalw[sup_state_def] 
"length a = length b \\<Longrightarrow> (G \\<turnstile> (i,a@x) <=s (j,b@y)) = ((G \\<turnstile> (i,a) <=s (j,b)) \\<and> (G \\<turnstile> (i,x) <=s (j,y)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_append]));
qed "sup_state_append_snd";

Goalw[sup_state_def]
"length a = length b \\<Longrightarrow> (G \\<turnstile> (a@x,i) <=s (b@y,j)) = ((G \\<turnstile> (a,i) <=s (b,j)) \\<and> (G \\<turnstile> (x,i) <=s (y,j)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_append]));
qed "sup_state_append_fst";


Goal "\\<forall> b. (G \\<turnstile> (rev a) <=l rev b) = (G \\<turnstile> a <=l b)";
by (induct_tac "a" 1);
 by (Simp_tac 1);
by (Clarsimp_tac 1);
by Safe_tac;
 by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_append, sup_loc_length]) 2);
by (exhaust_tac "b" 1); 
 bd sup_loc_length 1;
 by (Clarsimp_tac 1);
by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_append, sup_loc_length]) 1);
by (subgoal_tac "length (rev list) = length (rev lista)" 1);
 bd sup_loc_length 2;
 by (Clarsimp_tac 2);
by (dres_inst_tac [("G","G"),("x","[a]"),("y","[aa]")] sup_loc_append 1);
by (Clarsimp_tac 1);
qed_spec_mp "sup_loc_rev";


Goal "map f (rev l) = rev (map f l)";
by (induct_tac "l" 1);
by Auto_tac;
qed "map_rev";

Goalw[sup_state_def]
"(G \\<turnstile> (rev a,x) <=s (rev b,y)) = (G \\<turnstile> (a,x) <=s (b,y))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_rev, map_rev]));
qed "sup_state_rev_fst";

Goal "map x a = Y # YT \\<longrightarrow> map x (tl a) = YT \\<and> x (hd a) = Y \\<and> (\\<exists> y yt. a = y#yt)";
by (exhaust_tac "a" 1);
by Auto_tac;
qed_spec_mp "map_hd_tl";

Goalw[sup_state_def]
"(G \\<turnstile> (x#xt, a) <=s (yt, b)) = (\\<exists>y yt'. yt=y#yt' \\<and> (G \\<turnstile> x \\<preceq> y) \\<and> (G \\<turnstile> (xt,a) <=s (yt',b)))";
by Auto_tac;
bd map_hd_tl 1;
by Auto_tac;
qed "sup_state_Cons1";

Goalw [sup_loc_def]
"CFS \\<turnstile> YT <=l (X#XT) = (\\<exists>Y YT'. YT=Y#YT' \\<and> CFS \\<turnstile> Y <=o X \\<and> CFS \\<turnstile> YT' <=l XT)";
by(simp_tac (simpset() addsimps [list_all2_Cons2]) 1);
qed "sup_loc_Cons2";

Goalw[sup_state_def]
"(G \\<turnstile> (xt, a) <=s (y#yt, b)) = (\\<exists>x xt'. xt=x#xt' \\<and> (G \\<turnstile> x \\<preceq> y) \\<and> (G \\<turnstile> (xt',a) <=s (yt,b)))";
by (auto_tac (claset(), simpset() addsimps [sup_loc_Cons2]));
bd map_hd_tl 1;
by Auto_tac;
qed "sup_state_Cons2"; 

Goal "G \\<turnstile> b \\<preceq> NT \\<Longrightarrow> b = NT";
by (exhaust_tac "b" 1);
 by (exhaust_tac "ref_ty" 2);
by Auto_tac;
qed "widen_NT";

Goal "G \\<turnstile> b \\<preceq> Class C \\<Longrightarrow> \\<exists>r. b = RefT r";
by (exhaust_tac "b" 1);
by Auto_tac;
qed "widen_Class";


Goalw[sup_state_def] 
"G \\<turnstile> (a, x) <=s (b, y) \\<Longrightarrow> G \\<turnstile> (c, x) <=s (c, y)";
by Auto_tac;
qed "sup_state_ignore_fst";


Goalw[sup_ty_opt_def] 
"\\<lbrakk>G \\<turnstile> a <=o b; G \\<turnstile> b <=o c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=o c";
by (exhaust_tac "c" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "a" 1);
 by (Clarsimp_tac 1);
 by (exhaust_tac "b" 1);
  by (Clarsimp_tac 1);
 by (Clarsimp_tac 1);
by (exhaust_tac "b" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
be widen_trans 1;
ba 1;
qed "sup_ty_opt_trans";

Goal "\\<lbrakk>G \\<turnstile> a <=l b; G \\<turnstile> b <=l c\\<rbrakk> \\<Longrightarrow> \\<forall> n. n < length a \\<longrightarrow> G \\<turnstile> a!n <=o c!n";
by (Clarify_tac 1);
by (forward_tac [sup_loc_length] 1);
bd sup_loc_nth 1;
 ba 1;
bd sup_loc_nth 1;
 by (Force_tac 1);
bd sup_ty_opt_trans 1;
 ba 1;
ba 1;
qed "sup_loc_all_trans";

Goal "\\<forall> b. length a = length b \\<longrightarrow> (\\<forall> n. n < length a \\<longrightarrow> (G \\<turnstile> (a!n) <=o (b!n))) \\<longrightarrow> (G \\<turnstile> a <=l b)";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "b=[]" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [neq_Nil_conv]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("x","y")] exI 1);
by (res_inst_tac [("x","ys")] exI 1);
by (eres_inst_tac [("x","ys")] allE 1);
by (Full_simp_tac 1);
by (Clarify_tac 1);
be impE 1;
 by (Clarsimp_tac 1);
 by (eres_inst_tac [("x","Suc n")] allE 1);
 by (Clarsimp_tac 1);
by (eres_inst_tac [("x","0")] allE 1);
by (Clarsimp_tac 1);
qed_spec_mp "all_nth_sup_loc";

Goal "\\<lbrakk>G \\<turnstile> a <=l b; G \\<turnstile> b <=l c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=l c";
by (forward_tac [sup_loc_all_trans] 1);
 ba 1;
bd sup_loc_length 1;
bd sup_loc_length 1;
br all_nth_sup_loc 1;
 by (Clarsimp_tac 1);
ba 1;
qed "sup_loc_trans";

Goalw[sup_state_def] 
"\\<lbrakk>G \\<turnstile> a <=s b; G \\<turnstile> b <=s c\\<rbrakk> \\<Longrightarrow> G \\<turnstile> a <=s c";
by Safe_tac;
 br sup_loc_trans 1;
  ba 1;
 ba 1;
br sup_loc_trans 1;
 ba 1;
ba 1;
qed "sup_state_trans";

Goal "\\<forall>b. length a = length b \\<longrightarrow> (\\<forall>x\\<in>set (zip a b). x \\<in> widen G) = (G \\<turnstile> (map Some a) <=l (map Some b))";
by (induct_tac "a" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (exhaust_tac "b" 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
qed_spec_mp "all_widen_is_sup_loc";

Goal "\\<lbrakk>fits ins cert phi; i = ins!pc; i = MI meth_inv; pc < length ins; \
 \     wf_prog wf_mb G; \
\      G \\<turnstile> (x, y) <=s s1; wtl_inst i G rT s1 s1' cert mpc pc\\<rbrakk> \
\       \\<Longrightarrow> \\<exists>s2'. wtl_inst i G rT (x, y) s2' cert mpc pc \\<and> \
\                ((G \\<turnstile> s2' <=s s1') \\<or> (\\<exists> s. cert ! (Suc pc) = Some s \\<and> (G \\<turnstile> s2' <=s s)))"; 
by (exhaust_tac "meth_inv" 1); 
by (Clarsimp_tac 1);
by (cut_inst_tac [("x","x"),("n","length apTs")] rev_append_cons 1);
 by (asm_full_simp_tac (simpset() addsimps [sup_state_length_fst]) 1);
by (Clarify_tac 1);
by (subgoal_tac "length (rev aa) = length (rev apTs)" 1);
 by (Asm_full_simp_tac 2);
by (dres_inst_tac [("G","G"),("x","ba#c"),("i","y"),("j","ya"),("y","X#ST'")] sup_state_append_fst 1);
back();
back();
by (clarsimp_tac (claset(), simpset() addsimps [sup_state_rev_fst,sup_state_Cons1]) 1);
by (exhaust_tac "X = NT" 1);
 by (Clarsimp_tac 1);
 by (res_inst_tac [("x","a")] exI 1);
 by (res_inst_tac [("x","b")] exI 1);
 by (Asm_full_simp_tac 1);
 by (res_inst_tac [("x","aa")] exI 1);
 by (asm_full_simp_tac (simpset() addsimps [widen_NT]) 1);
by (Asm_full_simp_tac 1);
by (strip_tac1 1);
by (forward_tac [widen_Class] 1);
by (Clarsimp_tac 1);
by (exhaust_tac "r" 1);
 by (Clarsimp_tac 1);
 by (res_inst_tac [("x","a")] exI 1);
 by (res_inst_tac [("x","b")] exI 1);
 by (Clarsimp_tac 1);
 by (res_inst_tac [("x","aa")] exI 1);
 by (clarsimp_tac (claset(), simpset() addsimps [fits_def]) 1);
by (Clarsimp_tac 1);
bd subcls_widen_methd 1;
  ba 1;
 ba 1;
by (Clarify_tac 1);
by (res_inst_tac [("x","rT'#c")] exI 1);
by (res_inst_tac [("x","y")] exI 1);
by (Asm_full_simp_tac 1);
by (subgoal_tac "\\<exists>a b. cert ! Suc pc = Some (a, b) \\<and> G \\<turnstile> (rT' # c, y) <=s (a, b)" 1);
 by (Clarsimp_tac 1);
 by (res_inst_tac [("x","aa")] exI 1);
 by (Asm_full_simp_tac 1);
 by (clarsimp_tac (claset(), simpset() addsimps [sup_state_def, all_widen_is_sup_loc]) 1);
 br sup_loc_trans 1;
  ba 1;
 ba 1;
by (Clarsimp_tac 1);
by (subgoal_tac "G \\<turnstile> (rT' # c, y) <=s (rT # ST', ya)" 1);
 br sup_state_trans 1;
  ba 1;
 ba 1;
by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons1]) 1);
qed "method_inv_pseudo_mono";


Goalw[sup_ty_opt_def] "G \\<turnstile> a <=o Some b \\<Longrightarrow> \\<exists> x. a = Some x";
by (exhaust_tac "a" 1);
 by Auto_tac;
qed "sup_ty_opt_some";


Goalw[sup_loc_def] "\\<forall> y n. (G \\<turnstile> b <=l y) \\<longrightarrow> n < length y \\<longrightarrow> y!n = Some t \\<longrightarrow> (\\<exists>t. b!n = Some t \\<and> (G \\<turnstile> (b!n) <=o (y!n)))";
by (induct_tac "b" 1);
 by (Simp_tac 1);
by (clarsimp_tac (claset(), simpset() addsimps [list_all2_Cons1]) 1);
by (exhaust_tac "n" 1);
 by (asm_full_simp_tac (simpset() addsimps [sup_ty_opt_some]) 1);
by (smp_tac 1 1);
by (Asm_full_simp_tac 1);
qed_spec_mp "sup_loc_some";


Goalw[sup_state_def]
"\\<lbrakk>G \\<turnstile> (a, b) <=s (x, y); n < length y; y!n = Some t\\<rbrakk>\
\     \\<Longrightarrow> \\<exists>ts. b!n = Some ts \\<and> G \\<turnstile> (ts#a, b) <=s (t#x, y)";
by (Clarsimp_tac 1);
by (datac sup_loc_some 2 1);
by (Clarsimp_tac 1);
qed "mono_load";


Goalw[sup_loc_def]
"\\<forall> n y. (G \\<turnstile> a <=o b) \\<longrightarrow> n < length y \\<longrightarrow> (G \\<turnstile> x <=l y) \\<longrightarrow> (G \\<turnstile> x[n := a] <=l y[n := b])";
by (induct_tac "x" 1);
 by (Simp_tac 1);
by (clarsimp_tac ((claset(), simpset()) addIffs [sup_loc_Cons2]) 1);
by (exhaust_tac "n" 1);
 by (clarsimp_tac (claset(), simpset() addsimps [list_all2_Cons1]) 1);
by (clarsimp_tac (claset(), simpset() addsimps [list_all2_Cons1]) 1);
qed_spec_mp "sup_loc_update";


Goalw[sup_state_def] 
"\\<lbrakk>G \\<turnstile> (a, b) <=s (ts # ST', y); n < length y\\<rbrakk> \\<Longrightarrow> \
\ \\<exists> t a'. a = t#a' \\<and> G \\<turnstile> (a', b[n := Some t]) <=s (ST', y[n := Some ts])";
by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_Cons2]) 1);
by (forward_tac [map_hd_tl] 1);
by (clarsimp_tac (claset(), simpset() addsimps [sup_loc_update]) 1);
qed "mono_store"; 

Goal "(G \\<turnstile> xb \\<preceq> PrimT p) = (xb = PrimT p)";
by Safe_tac;
by (exhaust_tac "xb" 1);
by Auto_tac;
bd widen_RefT 1;
by Auto_tac;
qed "PrimT_PrimT";

Goal "\\<lbrakk>wtl_inst i G rT s1 s1' cert mpc pc; \
\      fits ins cert phi; pc < length ins; wf_prog wf_mb G; \
\      G \\<turnstile> s2 <=s s1; i = ins!pc\\<rbrakk> \\<Longrightarrow> \
\     \\<exists> s2'. wtl_inst (ins!pc) G rT s2 s2' cert mpc pc \\<and> \
\      (G \\<turnstile> s2' <=s s1' \\<or> (\\<exists>s. cert!(Suc pc) = Some s \\<and> G \\<turnstile> s2' <=s s))"; 
by (cut_inst_tac [("z","s2")] surj_pair 1); 
by (Clarify_tac 1); 
by (exhaust_tac "ins!pc" 1); 
       by (exhaust_tac "load_and_store" 1); 
          by (Clarsimp_tac 1); 
          by (datac mono_load 2 1); 
          by (clarsimp_tac (claset(), simpset() addsimps [sup_state_length_snd]) 1);
         by (clarsimp_tac (claset(), simpset() addsimps [sup_state_length_snd]) 1);
         by (datac mono_store 1 1);
         by (Clarsimp_tac 1);
        by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons1]) 1); 
       by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons1]) 1); 
      by (exhaust_tac "create_object" 1); 
      by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons1]) 1); 
     by (exhaust_tac "manipulate_object" 1); 
      by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
      be widen_trans 1; 
      ba 1; 
     by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
     br conjI 1; 
      be widen_trans 1; 
      ba 1; 
     be widen_trans 1; 
     ba 1; 
    by (exhaust_tac "check_object" 1); 
    by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
    be widen_RefT2 1; 
    br method_inv_pseudo_mono 1;
          ba 1;
         by (Asm_full_simp_tac 1);
        ba 1;
       ba 1;
      ba 1;
     ba 1;
    ba 1;   
   by (exhaust_tac "meth_ret" 1);
   by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
   br conjI 1;
    be widen_trans 1;
    ba 1;
   by (cut_inst_tac [("z","s1'")] surj_pair 1);
   by (strip_tac1 1);
   by (Clarsimp_tac 1);
  by (exhaust_tac "op_stack" 1);
     by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
    by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
   by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
  by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
 by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
by (exhaust_tac "branch" 1);
 by (Clarsimp_tac 1);
 bd sup_state_trans 1;
  ba 1;
 by (Clarsimp_tac 1);
 by (cut_inst_tac [("z","s1'")] surj_pair 1);
 by (Clarify_tac 1);
 by (Clarsimp_tac 1);
by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1); 
br conjI 1;
 br sup_state_trans 2;
  ba 2;
 ba 2;
by (Clarsimp_tac 1);
by (exhaust_tac "xa" 1);
 by (clarsimp_tac (claset(), simpset() addsimps [PrimT_PrimT]) 1);
by (Clarsimp_tac 1);
by (exhaust_tac "xb" 1);
by Auto_tac;
bd widen_RefT 1;
by Auto_tac;
qed "wtl_inst_pseudo_mono";


Goal "\\<lbrakk>wtl_inst i G rT s1 s1' cert (Suc pc) pc; G \\<turnstile> s2 <=s s1\\<rbrakk> \\<Longrightarrow> \
\ \\<exists>s2'. wtl_inst i G rT s2 s2' cert (Suc pc) pc \\<and> (G \\<turnstile> s2' <=s s1')";
by (exhaust_tac "i" 1);
by (exhaust_tac "branch" 8);
by (exhaust_tac "op_stack" 7);
by (exhaust_tac "meth_ret" 6);
by (exhaust_tac "meth_inv" 5);
by (exhaust_tac "check_object" 4);
by (exhaust_tac "manipulate_object" 3);
by (exhaust_tac "create_object" 2);
by (exhaust_tac "load_and_store" 1);
by (TRYALL Asm_full_simp_tac);
 by (pair_tac "s1'" 1);
 by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1);
 br widen_trans 1;
  ba 1;
 ba 1;
by (pair_tac "s1'" 1);
by (clarsimp_tac (claset(), simpset() addsimps [sup_state_Cons2]) 1);
br sup_state_trans 1;
 ba 1;
ba 1;
qed "wtl_inst_last_mono";

Goalw [wtl_inst_option_def] 
"\\<lbrakk>wtl_inst_option i G rT s1 s1' cert mpc pc; Suc pc = mpc; G \\<turnstile> s2 <=s s1\\<rbrakk> \\<Longrightarrow> \
\ \\<exists>s2'. wtl_inst_option i G rT s2 s2' cert mpc pc \\<and> (G \\<turnstile> s2' <=s s1')";
by (exhaust_tac "cert!pc" 1);
 by (Clarsimp_tac 1);
 bd wtl_inst_last_mono 1;
  ba 1;
 by (Asm_full_simp_tac 1);
by (Clarsimp_tac 1);
bd sup_state_trans 1;
 ba 1;
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("s2.0","(a,b)")] wtl_inst_last_mono 1);
 by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed "wtl_option_last_mono";

Goalw [wt_instr_def] 
     "\\<lbrakk>wt_instr (ins!pc) G rT phi max_pc pc; fits ins cert phi;\ 
\      pc < length ins; length ins = max_pc\\<rbrakk> \\<Longrightarrow> \ 
\     \\<exists> s. wtl_inst (ins!pc) G rT (phi!pc) s cert max_pc pc \\<and> G \\<turnstile> s <=s phi ! Suc pc";  
by (cut_inst_tac [("z","phi!pc")] surj_pair 1);
by (strip_tac1 1);
by (exhaust_tac "ins!pc" 1);
by (exhaust_tac "op_stack" 7);
by (exhaust_tac "check_object" 4);
by (exhaust_tac "manipulate_object" 3);
by (exhaust_tac "create_object" 2);
by (exhaust_tac "load_and_store" 1);
               by (TRYALL (Asm_full_simp_tac THEN_MAYBE' Force_tac));
  by (exhaust_tac "meth_inv" 1);
  by (cut_inst_tac [("z","phi!(Suc pc)")] surj_pair 1);
  by (strip_tac1 1);
  by (Clarsimp_tac 1);
  by (exhaust_tac "X = NT" 1);
   by (clarsimp_tac (claset(),simpset() addsimps [fits_def, contains_dead_def]) 1);
   by (smp_tac 1 1);
   by (Clarsimp_tac 1);
   by (Force_tac 1);
  by (Asm_full_simp_tac 1);
  by (strip_tac1 1);
  by (res_inst_tac [("x","rT#ST'")] exI 1);
  by (res_inst_tac [("x","y")] exI 1);
  by (Asm_full_simp_tac 1);
  by (res_inst_tac [("x","apTs")] exI 1);
  by (clarsimp_tac (claset(),simpset() addsimps [fits_def, contains_dead_def]) 1);
 by (exhaust_tac "meth_ret" 1);
 by (asm_full_simp_tac (simpset() addsimps [fits_def, contains_dead_def]) 1);
 by (cut_inst_tac [("z","phi!Suc pc")] surj_pair 1);
 by (strip_tac1 1);
 by (Clarsimp_tac 1);
by (exhaust_tac "branch" 1);
 by (asm_full_simp_tac (simpset() addsimps [fits_def, contains_dead_def, contains_targets_def]) 1);
 by (cut_inst_tac [("z","phi!Suc pc")] surj_pair 1);
 by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [fits_def, contains_targets_def]) 1);
by (Force_tac 1);
qed "wt_instr_imp_wtl_inst";

Goalw [wtl_inst_option_def] 
     "\\<lbrakk>fits ins cert phi; pc < length ins; wt_instr (ins!pc) G rT phi max_pc pc; \
\      max_pc = length ins\\<rbrakk> \\<Longrightarrow> \ 
\     \\<exists> s. wtl_inst_option (ins!pc) G rT (phi!pc) s cert max_pc pc \\<and> G \\<turnstile> s <=s phi ! Suc pc";
by (exhaust_tac "cert!pc" 1);
 by (Clarsimp_tac 1);
 bd wt_instr_imp_wtl_inst 1;
    ba 1;
   ba 1;
  br refl 1;
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
by (forward_tac [wt_instr_imp_wtl_inst] 1);
   ba 1;
  ba 1;
 by (Clarsimp_tac 1);
by (clarsimp_tac (claset(), simpset() addsimps [fits_def, is_approx_def]) 1);
by (eres_inst_tac [("x","pc")] allE 1);
by (Clarsimp_tac 1);
by Auto_tac;
qed "wt_inst_imp_wtl_option";

Goal "\\<lbrakk>wtl_inst_list ins G rT s0 s' cert max_pc pc; \ 
\     ins \\<noteq> []; G \\<turnstile> s <=s s0; \ 
\     s \\<noteq> s0 \\<longrightarrow> cert ! pc = Some s0\\<rbrakk> \\<Longrightarrow> \ 
\     wtl_inst_list ins G rT s s' cert max_pc pc";  
by (exhaust_tac "ins" 1); 
 by (Clarify_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (exhaust_tac "list = []" 1);
 by (Asm_full_simp_tac 1);
 by (exhaust_tac "s = s0" 1);
  by (Force_tac 1);
 by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
qed "wtl_inst_list_s";


Goal "\\<lbrakk>wtl_inst_list ins G rT s0 s' cert max_pc pc; \ 
\     ins \\<noteq> []; G \\<turnstile> s <=s s0; cert ! pc = Some s0\\<rbrakk> \\<Longrightarrow> \ 
\     wtl_inst_list ins G rT s s' cert max_pc pc"; 
by (exhaust_tac "ins" 1); 
 by (Clarify_tac 1);
by (force_tac (claset(), simpset() addsimps [wtl_inst_option_def]) 1);
qed "wtl_inst_list_cert";


Goalw [wtl_inst_option_def]
"\\<lbrakk>wtl_inst_option i G rT s1 s1' cert mpc pc; \
\ fits ins cert phi; pc < length ins; wf_prog wf_mb G; \
\ G \\<turnstile> s2 <=s s1; i = ins!pc\\<rbrakk> \\<Longrightarrow> \
\ \\<exists> s2'. wtl_inst_option (ins!pc) G rT s2 s2' cert mpc pc \\<and> \
\        (G \\<turnstile> s2' <=s s1' \\<or> (\\<exists>s. cert!(Suc pc) = Some s \\<and> G \\<turnstile> s2' <=s s))";
by (exhaust_tac "cert!pc" 1);
 by (Asm_full_simp_tac 1);
 by (datac wtl_inst_pseudo_mono 4 1);
  by (Clarsimp_tac 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
br conjI 1;
 br sup_state_trans 1;
  ba 1;
 ba 1;
by (thin_tac "G \\<turnstile> s1 <=s (a, b)" 1);
by (thin_tac "G \\<turnstile> s2 <=s s1" 1);
by (subgoal_tac "G \\<turnstile> (a,b) <=s (a,b)" 1);
 by (datac wtl_inst_pseudo_mono 4 1);
  by (Asm_full_simp_tac 1);
 by (Asm_full_simp_tac 1);
by (Simp_tac 1);
qed "wtl_option_pseudo_mono";

Goal "((l @ a # list) ! length l) = a";
by (induct_tac "l" 1);
by Auto_tac;
qed "append_cons_length_nth";

Goal "\\<forall> pc. (\\<forall>pc'. pc' < length ins \\<longrightarrow> wt_instr (ins ! pc') G rT phi (pc+length ins) (pc+pc')) \\<longrightarrow>   \
\           wf_prog wf_mb G \\<longrightarrow> \
\           fits all_ins cert phi \\<longrightarrow> (\\<exists> l. pc = length l \\<and> l@ins=all_ins) \\<longrightarrow> pc < length all_ins \\<longrightarrow>\
\           (\\<forall> s. (G \\<turnstile> s <=s (phi!pc)) \\<longrightarrow> \
\           (\\<exists>s'. wtl_inst_list ins G rT s s' cert (pc+length ins) pc))";
by (induct_tac "ins" 1);
 by (Simp_tac 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x","Suc (length l)")] allE 1); 
be impE 1; 
 by (Clarsimp_tac 1);
 by (eres_inst_tac [("x","Suc pc'")] allE 1);
 by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
be impE 1;
 by (Asm_full_simp_tac 1);
by (eres_inst_tac [("x","0")] allE 1);
by (Asm_full_simp_tac 1);
by (forw_inst_tac [("G","G"),("rT","rT"),("pc","length l"),
                   ("max_pc","Suc (length l + length list)")] wt_inst_imp_wtl_option 1);
   by (Simp_tac 1);
  by (asm_full_simp_tac (simpset() addsimps [nth_append]) 1);
 by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [nth_append]) 1);
by (Clarify_tac 1);
by (exhaust_tac "list = []" 1);
 by (Clarsimp_tac 1);
 bd wtl_option_last_mono 1;
   br refl 1;
  ba 1;
 by (Clarsimp_tac 1);
 by (dres_inst_tac [("a","(ac,bb)")] sup_state_trans 1);
  ba 1;
 by (Force_tac 1);
by (Clarsimp_tac 1);
bd wtl_option_pseudo_mono 1;
     ba 1;
    by (Simp_tac 1);
   ba 1;
  ba 1;
 by (simp_tac (simpset() addsimps [append_cons_length_nth]) 1);
by (clarsimp_tac (claset(), simpset() addsimps [append_cons_length_nth]) 1);
by (exhaust_tac "cert ! Suc (length l)" 1);
 by (Clarsimp_tac 1);
 by (dres_inst_tac [("a","(ac,bb)")] sup_state_trans 1);
  ba 1;
 by (Force_tac 1);
by (Clarsimp_tac 1);
by (subgoal_tac "G \\<turnstile> (ac, bb) <=s phi ! Suc (length l)" 1);
 by (thin_tac "G \\<turnstile> (ab, ba) <=s phi ! Suc (length l)" 1);
 by (smp_tac 2 1);
 by (Force_tac 1);
be disjE 1;
 br sup_state_trans 1;
  ba 1;
 ba 1;
by (clarsimp_tac (claset(), simpset() addsimps [fits_def, is_approx_def]) 1);
by (eres_inst_tac [("x","Suc (length l)")] allE 1);
be impE 1;
 by (exhaust_tac "length list" 1);
  by (Clarsimp_tac 1);
 by (Clarsimp_tac 1);
by (Clarsimp_tac 1);
qed_spec_mp "wt_imp_wtl_inst_list"; 



Goalw[wt_method_def, wtl_method_def]
 "\\<lbrakk>wt_method G C pTs rT mxl ins phi; fits ins cert phi; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> wtl_method G C pTs rT mxl ins cert";
by (Clarsimp_tac 1);
by (cut_inst_tac [("pc","0")] wt_imp_wtl_inst_list 1);    
      by (Force_tac 1);
     ba 1;
    ba 1;
   by (Simp_tac 1);
  by (Simp_tac 1);
 by (clarsimp_tac (claset(), simpset() addsimps [wt_start_def]) 1);
 ba 1;
by (Asm_full_simp_tac 1);
qed "fits_imp_wtl_method_complete";

Goal "\\<lbrakk>wt_method G C pTs rT mxl ins phi; wf_prog wf_mb G\\<rbrakk> \\<Longrightarrow> wtl_method G C pTs rT mxl ins (make_cert ins phi)";
by (subgoal_tac "fits ins (make_cert ins phi) phi" 1);
 br fits_make_cert 2;
 by (asm_full_simp_tac (simpset() addsimps [wt_method_def]) 2);
br fits_imp_wtl_method_complete 1;
  ba 1;
 ba 1;
ba 1;
qed "wtl_method_complete";

Goalw[wt_jvm_prog_def, wfprg_def] "\\<lbrakk>wt_jvm_prog G Phi\\<rbrakk> \\<Longrightarrow> wfprg G";
by Auto_tac;
qed "wt_imp_wfprg";

Goal "(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (a',b',c',d') \\<in> set l \\<longrightarrow> a = a' \\<longrightarrow> b=b' \\<and> c=c' \\<and> d=d'";
by (induct_tac "l" 1);
by Auto_tac;
qed_spec_mp "unique_set";

Goal "(a,b,c,d)\\<in>set l \\<longrightarrow> unique l \\<longrightarrow> (\\<epsilon> (a',b',c',d'). (a',b',c',d') \\<in> set l \\<and> a'=a) = (a,b,c,d)";
by (auto_tac (claset(), simpset() addsimps [unique_set]));
qed_spec_mp "unique_epsilon";

Goal "\\<lbrakk>wt_jvm_prog G Phi\\<rbrakk> \\<Longrightarrow> wtl_jvm_prog G (make_Cert G Phi)";
by (forward_tac [wt_imp_wfprg] 1);
by (asm_full_simp_tac (simpset() addsimps [wt_jvm_prog_def, 
    wtl_jvm_prog_def, wf_prog_def, wf_cdecl_def, wf_mdecl_def]) 1);
by Auto_tac;
bd bspec 1;
 ba 1;
by (Clarsimp_tac 1);
bd bspec 1;
back();
 ba 1;
by (clarsimp_tac (claset(), simpset() addsimps [make_Cert_def, wfprg_def]) 1);
bd wtl_method_complete 1;
 ba 1;
by (asm_full_simp_tac (simpset() addsimps [unique_epsilon]) 1);
qed "wtl_complete";




 
