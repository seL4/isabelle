(*  Title:      HOL/MicroJava/J/WellForm.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [wf_prog_def]
 "[|class G C = Some c; wf_prog wf_mb G|] ==> wf_cdecl wf_mb G (C,c)";
by (Asm_full_simp_tac 1);
by (fast_tac (set_cs addDs [map_of_SomeD]) 1);
qed "class_wf";

Goalw [wf_prog_def, ObjectC_def]
	"wf_prog wf_mb G ==> class G Object = Some (arbitrary, [], [])";
by (auto_tac (claset() addIs [map_of_SomeI], simpset()));
qed "class_Object";
Addsimps [class_Object];

Goal "wf_prog wf_mb G ==> is_class G Object";
by (Asm_simp_tac 1);
qed "is_class_Object";
Addsimps [is_class_Object];

Goal "[|G\\<turnstile>C\\<prec>C1D; wf_prog wf_mb G|] ==> D \\<noteq> C \\<and> \\<not>(D,C)\\<in>(subcls1 G)^+";
by( forward_tac [r_into_trancl] 1);
by( dtac subcls1D 1);
by(Clarify_tac 1);
by( datac class_wf 1 1);
by( rewtac wf_cdecl_def);
by(force_tac (claset(), simpset() addsimps [reflcl_trancl RS sym] 
				  delsimps [reflcl_trancl]) 1);
qed "subcls1_wfD";

Goalw [wf_cdecl_def] 
"!!r. \\<lbrakk>wf_cdecl wf_mb G (C,D,r); C \\<noteq> Object\\<rbrakk> \\<Longrightarrow> is_class G D";
by (auto_tac (claset(), simpset() addsplits [option.split_asm]));
qed "wf_cdecl_supD";

Goal "[|wf_prog wf_mb G; (C,D)\\<in>(subcls1 G)^+|] ==> \\<not>(D,C)\\<in>(subcls1 G)^+";
by(etac tranclE 1);
by(TRYALL(fast_tac (claset() addSDs [subcls1_wfD] addIs [trancl_trans])));
qed "subcls_asym";

Goal "[|wf_prog wf_mb G; (C,D)\\<in>(subcls1 G)^+|] ==> C \\<noteq> D";
by (etac trancl_trans_induct 1);
by  (auto_tac (claset() addDs [subcls1_wfD,subcls_asym],simpset()));
qed "subcls_irrefl";

Goalw [acyclic_def] "wf_prog wf_mb G ==> acyclic (subcls1 G)";
by (fast_tac (claset() addDs [subcls_irrefl]) 1);
qed "acyclic_subcls1";

Goal "wf_prog wf_mb G ==> wf ((subcls1 G)^-1)";
by (rtac finite_acyclic_wf 1);
by ( stac finite_converse 1);
by ( rtac finite_subcls1 1);
by (stac acyclic_converse 1);
by (etac acyclic_subcls1 1);
qed "wf_subcls1";

val major::prems = goal thy
  "[|wf_prog wf_mb G; !!C. \\<forall>D. (C,D)\\<in>(subcls1 G)^+ --> P D ==> P C|] ==> P C";
by(cut_facts_tac [major RS wf_subcls1] 1);
by(dtac wf_trancl 1);
by(asm_full_simp_tac (HOL_ss addsimps [trancl_converse]) 1);
by(eres_inst_tac [("a","C")] wf_induct 1);
by(resolve_tac prems 1);
by(Auto_tac);
qed "subcls_induct";

val prems = goal thy "[|is_class G C; wf_prog wf_mb G; P Object; \
\!!C D fs ms. [|C \\<noteq> Object; is_class G C; class G C = Some (D,fs,ms) \\<and> \
\   wf_cdecl wf_mb G (C,D,fs,ms) \\<and> G\\<turnstile>C\\<prec>C1D \\<and> is_class G D \\<and> P D|] ==> P C\
\ |] ==> P C";
by( cut_facts_tac prems 1);
by( rtac impE 1);
by(   atac 2);
by(  atac 2);
by( etac thin_rl 1);
by( rtac subcls_induct 1);
by(  atac 1);
by( rtac impI 1);
by( case_tac "C = Object" 1);
by(  Fast_tac 1);
by Safe_tac;
by( forward_tac [class_wf] 1);
by(  atac 1);
by( forward_tac [wf_cdecl_supD] 1);
by(  atac 1);

by( subgoal_tac "G\\<turnstile>C\\<prec>C1a" 1);
by( etac subcls1I 2);
by( rtac (hd (tl (tl (tl prems)))) 1);
by Auto_tac;
qed "subcls1_induct";

Goal "[|wf ((subcls1 G)^-1); \\<forall>D fs ms. class G C = Some (D,fs,ms) \\<longrightarrow> C \\<noteq> Object --> is_class G D|] ==> method (G,C) = \
\ (case class G C of None => arbitrary | Some (D,fs,ms) => \
\ (if C = Object then empty else method (G,D)) ++ \
\ map_of (map (\\<lambda>(s,m). (s,(C,m))) ms))";
by( stac (method_TC RS (wf_subcls1_rel RS (hd method.simps))) 1);
by( asm_simp_tac (simpset() addsplits[option.split]) 1);
by Auto_tac;
qed "method_rec_lemma";

Goal "wf_prog wf_mb G ==> method (G,C) = \
\ (case class G C of None => arbitrary | Some (D,fs,ms) => \
\ (if C = Object then empty else method (G,D)) ++ \
\ map_of (map (\\<lambda>(s,m). (s,(C,m))) ms))";
by(rtac method_rec_lemma 1);
by( clarsimp_tac (claset(), simpset() addsimps [wf_subcls1,empty_def] 
		addsplits [option.split]) 1);
by( case_tac "C = Object" 1);
by(  Force_tac 1);
by Safe_tac;
by( datac class_wf 1 1);
by( datac wf_cdecl_supD 1 1);
by( Asm_full_simp_tac 1);
qed "method_rec";

Goal "[|wf ((subcls1 G)^-1); class G C = Some (D,fs,ms); C \\<noteq> Object \\<longrightarrow> is_class G D|] ==> fields (G,C) = \
\ map (\\<lambda>(fn,ft). ((fn,C),ft)) fs @ (if C = Object then [] else fields (G,D))";
by(rtac trans 1);
by(rtac (fields_TC RS (wf_subcls1_rel RS (hd fields.simps))) 1);
by( asm_simp_tac (simpset() addsplits[option.split]) 1);
qed "fields_rec_lemma";

Goal "[|class G C = Some (D,fs,ms); wf_prog wf_mb G|] ==> fields (G,C) = \
\ map (\\<lambda>(fn,ft). ((fn,C),ft)) fs @ (if C = Object then [] else fields (G,D))";
by(rtac trans 1);
by(rtac fields_rec_lemma 1);
by(   asm_simp_tac (simpset() addsimps [wf_subcls1]) 1);
ba  1;
br refl 2;
by( datac class_wf 1 1);
by(rtac impI 1);
by( eatac wf_cdecl_supD 1 1);
qed "fields_rec";

Goal "wf_prog wf_mb G ==> method (G,Object) = empty";
by(stac method_rec 1);
by Auto_tac;
qed "method_Object";

Goal "wf_prog wf_mb G ==> fields (G,Object) = []";
by(stac fields_rec 1);
by Auto_tac;
qed "fields_Object";

Addsimps [method_Object, fields_Object];

Goalw [field_def] "wf_prog wf_mb G ==> field (G,Object) = empty";
by(Asm_simp_tac 1);
qed "field_Object";
Addsimps [field_Object];

Goal "[|is_class G C; wf_prog wf_mb G|] ==> G\\<turnstile>C\\<preceq>C Object";
by(etac subcls1_induct 1);
by(  atac 1);
by( Fast_tac 1);
by(auto_tac (HOL_cs addSDs [wf_cdecl_supD], simpset()));
by(eatac rtrancl_into_rtrancl2 1 1);
qed "subcls_C_Object";

Goalw [wf_mhead_def] "wf_mhead G sig rT ==> is_type G rT";
by Auto_tac;
qed "is_type_rTI";

Goal "[|is_class G C; wf_prog wf_mb G|] ==> \
\ \\<forall>((fn,fd),fT)\\<in>set (fields (G,C)). G\\<turnstile>C\\<preceq>C fd";
by( etac subcls1_induct 1);
by(   atac 1);
by(  Asm_simp_tac 1);
by( safe_tac HOL_cs);
by( stac fields_rec 1);
by(   atac 1);
by(  atac 1);
by( simp_tac (simpset() delsplits [split_if]) 1);
by( rtac ballI 1);
by( split_all_tac 1);
by( Simp_tac 1);
by( etac UnE 1);
by(  Force_tac 1);
by( etac (r_into_rtrancl RS rtrancl_trans) 1);
by Auto_tac;
qed "widen_fields_defpl'";

Goal "[|((fn,fd),fT) \\<in> set (fields (G,C)); wf_prog wf_mb G; is_class G C|] ==> \
\ G\\<turnstile>C\\<preceq>C fd";
by( datac widen_fields_defpl' 1 1);
by (Fast_tac 1);
qed "widen_fields_defpl";

Goal "[|is_class G C; wf_prog wf_mb G|] ==> unique (fields (G,C))";
by( etac subcls1_induct 1);
by(   atac 1);
by(  safe_tac (HOL_cs addSDs [wf_cdecl_supD]));
by(  Asm_simp_tac 1);
by( dtac subcls1_wfD 1);
by(  atac 1);
by( stac fields_rec 1);
by   Auto_tac;
by( rotate_tac ~1 1);
by( forward_tac [class_wf] 1);
by  Auto_tac;
by( asm_full_simp_tac (simpset() addsimps [wf_cdecl_def]) 1);
by( etac unique_append 1);
by(  rtac unique_map_inj 1);
by(   Clarsimp_tac 1);
by  (rtac injI 1);
by(  Asm_full_simp_tac 1);
by(auto_tac (claset() addSDs [widen_fields_defpl], simpset()));
qed "unique_fields";

Goal "[|wf_prog wf_mb G; (C',C)\\<in>(subcls1 G)^*|] ==> \
\ x \\<in> set (fields (G,C)) --> x \\<in> set (fields (G,C'))";
by(etac converse_rtrancl_induct 1);
by( safe_tac (HOL_cs addSDs [subcls1D]));
by(stac fields_rec 1);
by(  Auto_tac);
qed_spec_mp "fields_mono_lemma";

Goal
"\\<lbrakk>map_of (fields (G,C)) fn = Some f; G\\<turnstile>D\\<preceq>C C; is_class G D; wf_prog wf_mb G\\<rbrakk>\
\ \\<Longrightarrow> map_of (fields (G,D)) fn = Some f";
by (rtac map_of_SomeI 1);
by  (eatac unique_fields 1 1);
by (eatac fields_mono_lemma 1 1);
by (etac map_of_SomeD 1);
qed "fields_mono";

Goal 
"[|field (G,C) fn = Some (fd, fT); G\\<turnstile>D\\<preceq>C C; wf_prog wf_mb G|]==> \
\ map_of (fields (G,D)) (fn, fd) = Some fT";
by (dtac field_fields 1);
by (dtac rtranclD 1);
by Safe_tac;
by (ftac subcls_is_class 1);
by (dtac trancl_into_rtrancl 1);
by (fast_tac (HOL_cs addDs [fields_mono]) 1);
qed "widen_cfs_fields";

Goal "wf_prog wf_mb G ==> is_class G C \\<Longrightarrow>  \
\    method (G,C) sig = Some (md,mh,m)\
\  --> G\\<turnstile>C\\<preceq>C md \\<and> wf_mdecl wf_mb G md (sig,(mh,m))";
by( etac subcls1_induct 1);
by(   atac 1);
by(  Force_tac 1);
by( forw_inst_tac [("C","C")] method_rec 1);
by( Clarify_tac 1);
by( rotate_tac ~1 1);
by( Asm_full_simp_tac 1);
by( dtac override_SomeD 1);
by( etac disjE 1);
by(  thin_tac "?P --> ?Q" 1);
by(  Clarify_tac 2);
by(  rtac rtrancl_trans 2);
by(   atac 3);
by(  rtac r_into_rtrancl 2);
by(  fast_tac (HOL_cs addIs [subcls1I]) 2);
by (rotate_tac ~1 1);
by (ftac map_of_SomeD 1);
by( rewtac wf_cdecl_def);
by (Clarsimp_tac 1);
qed_spec_mp "method_wf_mdecl";

Goal "[|G\\<turnstile>T\\<preceq>C T'; wf_prog wf_mb G|] ==> \
\  \\<forall>D rT b. method (G,T') sig = Some (D,rT ,b) -->\
\ (\\<exists>D' rT' b'. method (G,T) sig = Some (D',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT)";
by( dtac rtranclD 1);
by( etac disjE 1);
by(  Fast_tac 1);
by( etac conjE 1);
by( etac trancl_trans_induct 1);
by(  Clarify_tac 2);
by(  EVERY[smp_tac 3 2]);
by(  fast_tac (HOL_cs addEs [widen_trans]) 2);
by( Clarify_tac 1);
by( dtac subcls1D 1);
by( Clarify_tac 1);
by( stac method_rec 1);
by(  atac 1);
by( rewtac override_def);
by( asm_simp_tac (simpset() delsimps [split_paired_Ex]) 1);
by( case_tac "\\<exists>z. map_of(map (\\<lambda>(s,m). (s, ?C, m)) ms) sig = Some z" 1);
by(  etac exE 1);
by(  asm_full_simp_tac (HOL_ss addsimps [not_None_eq RS sym]) 2);
by(  ALLGOALS (rotate_tac ~1 THEN' forward_tac[ssubst] THEN' (fn n=>atac(n+1))));
by(  ALLGOALS (asm_simp_tac (simpset() delsimps [split_paired_Ex])));
by( dtac class_wf 1);
by(  atac 1);
by( split_all_tac 1);
by( rewtac wf_cdecl_def);
by( dtac map_of_SomeD 1);
by Auto_tac;
qed_spec_mp "subcls_widen_methd";

Goal
 "[| G\\<turnstile> C\\<preceq>C D; wf_prog wf_mb G; \
\    method (G,D) sig = Some (md, rT, b) |] \
\ ==> \\<exists>mD' rT' b'. method (G,C) sig= Some(mD',rT',b') \\<and> G\\<turnstile>rT'\\<preceq>rT";
by(auto_tac (claset() addDs [subcls_widen_methd,method_wf_mdecl],
             simpset() addsimps [wf_mdecl_def,wf_mhead_def,split_def]));
qed "subtype_widen_methd";

Goal "wf_prog wf_mb G ==> is_class G C \\<Longrightarrow> \\<forall>D. method (G,C) sig = Some(D,mh,code) --> is_class G D \\<and> method (G,D) sig = Some(D,mh,code)";
by (etac subcls1_induct 1);
  ba 1;
 by (Asm_full_simp_tac 1);
by (stac method_rec 1);
 ba 1;
by (Clarify_tac 1);
by (eres_inst_tac [("x","Da")] allE 1);
by (Clarsimp_tac 1);
 by (asm_full_simp_tac (simpset() addsimps [map_of_map]) 1);
 by (Clarify_tac 1);
 by (stac method_rec 1);
  ba 1;
 by (asm_full_simp_tac (simpset() addsimps [override_def,map_of_map] addsplits [option.split]) 1);
qed_spec_mp "method_in_md";

Goal "[|is_class G C; wf_prog wf_mb G|] ==> \
\ \\<forall>f\\<in>set (fields (G,C)). is_type G (snd f)";
by( etac subcls1_induct 1);
by(   atac 1);
by(  Asm_simp_tac 1);
by( stac fields_rec 1);
by(   Fast_tac 1);
by(  atac 1);
by( Clarsimp_tac 1);
by( Safe_tac);
by(  Force_tac 2);
by( dtac class_wf 1);
by(  atac 1);
by( rewtac wf_cdecl_def);
by( Clarsimp_tac 1);
by( EVERY[dtac bspec 1, atac 1]);
by( rewtac wf_fdecl_def);
by Auto_tac;
qed_spec_mp "fields_is_type_lemma";

Goal "[|map_of (fields (G,C)) fn = Some f; wf_prog wf_mb G; is_class G C|] ==> \
\ is_type G f";
by(dtac map_of_SomeD 1);
by(datac fields_is_type_lemma 2 1);
by(Auto_tac);
qed "fields_is_type";

