(*  Title:      HOL/MicroJava/J/TypeRel.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [subcls1_def] 
  "G\\<turnstile>C\\<prec>C1D \\<Longrightarrow> C \\<noteq> Object \\<and> (\\<exists>fs ms. class G C = Some (D,fs,ms))";
by Auto_tac;
qed "subcls1D";
Goalw [subcls1_def] "\\<lbrakk>class G C = Some (D,rest); C \\<noteq> Object\\<rbrakk> \\<Longrightarrow> G\\<turnstile>C\\<prec>C1D";
by Auto_tac;
qed "subcls1I";

Goalw [subcls1_def]  
"subcls1 G = (\\<Sigma>C\\<in>{C. is_class G C} . {D. C\\<noteq>Object \\<and> fst (the (class G C))=D})";
by Auto_tac;
qed "subcls1_def2";

Goal "finite (subcls1 G)";
by(stac subcls1_def2 1);
by( rtac (finite_is_class RS finite_SigmaI) 1);
by(res_inst_tac [("B","{fst (the (class G C))}")] finite_subset 1);
by  Auto_tac;
qed "finite_subcls1";


Goal "(C,D) \\<in> (subcls1 G)^+ ==> is_class G C";
by(etac trancl_trans_induct 1);
by (auto_tac (HOL_cs addSDs [subcls1D],simpset()));
qed "subcls_is_class";

Goal "G\\<turnstile>C\\<preceq>C D \\<Longrightarrow> is_class G D \\<longrightarrow> is_class G C";
by (etac rtrancl_induct 1);
by  (dtac subcls1D 2);
by  Auto_tac;
qed_spec_mp "subcls_is_class2"; 

(* A particular thm about wf;
   looks like it is an odd instance of something more general
*)
Goalw [wf_def] "wf{((A,x),(B,y)) . A=B \\<and> wf(R(A)) \\<and> (x,y)\\<in>R(A)}";
by(full_simp_tac (simpset() delcongs [imp_cong]) 1);
by(strip_tac 1);
by(rename_tac "A x" 1);
by(case_tac "wf(R A)" 1);
by (eres_inst_tac [("a","x")] wf_induct 1);
by (EVERY1[etac allE, etac allE, etac mp, rtac allI, rtac allI]);
by (Fast_tac 1);
by(rewrite_goals_tac [wf_def]);
by(Blast_tac 1);
qed "wf_rel_lemma";


(* Proving the termination conditions *)

goalw thy [subcls1_rel_def] "wf subcls1_rel";
by(rtac (wf_rel_lemma RS wf_subset) 1);
by(Force_tac 1);
qed "wf_subcls1_rel";

val method_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (method.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);

val fields_TC = prove_goalw_cterm [subcls1_rel_def]
 (cterm_of (sign_of thy) (HOLogic.mk_Trueprop (hd (tl (fields.tcs)))))
 (K [auto_tac (claset() addIs [subcls1I], simpset())]);

Goalw [field_def] 
"field (G,C) fn = Some (fd, fT) \\<Longrightarrow> map_of (fields (G,C)) (fn, fd) = Some fT";
by (rtac table_of_remap_SomeD 1);
by (Asm_full_simp_tac 1);
qed "field_fields";

AddSIs   [widen.refl,widen.null];
Addsimps [widen.refl];

Goal "(G\\<turnstile>PrimT pT\\<preceq>RefT rT) = False";
br iffI 1;
be widen.elim 1;
by Auto_tac;
qed "widen_PrimT_RefT";
AddIffs [widen_PrimT_RefT];

Goal "G\\<turnstile>S\\<preceq>T ==> S=RefT R --> (\\<exists>t. T=RefT t)";
by (etac widen.elim 1);
by Auto_tac;
qed "widen_RefT_lemma";
Goal "G\\<turnstile>RefT R\\<preceq>T ==> \\<exists>t. T=RefT t"; 
by (dtac widen_RefT_lemma 1);
by Auto_tac;
qed "widen_RefT";

Goal "G\\<turnstile>S\\<preceq>T ==> T=RefT R --> (\\<exists>t. S=RefT t)";
by (etac widen.elim 1);
by Auto_tac;
qed "widen_RefT2_lemma";
Goal "G\\<turnstile>S\\<preceq>RefT R ==> \\<exists>t. S=RefT t";
by (dtac widen_RefT2_lemma 1);
by Auto_tac;
qed "widen_RefT2";

Goal "G\\<turnstile>S\\<preceq>T ==> S = Class C --> (\\<exists>D. T=Class D)";
by (etac widen.elim 1);
by Auto_tac;
qed "widen_Class_lemma";
Goal "G\\<turnstile>Class C\\<preceq>T ==> \\<exists>D. T=Class D";
by (dtac widen_Class_lemma 1);
by Auto_tac;
qed "widen_Class";

Goal "(G\\<turnstile>Class C\\<preceq>RefT NullT) = False"; 
br iffI 1;
be widen.elim 1;
by(Auto_tac);
qed "widen_Class_NullT";
AddIffs [widen_Class_NullT];

Goal "(G\\<turnstile>Class C\\<preceq> Class D) = (G\\<turnstile>C\\<preceq>C D)";
br iffI 1;
be widen.elim 1;
by(Auto_tac);
bes widen.intrs 1;
qed "widen_Class_Class";
AddIffs [widen_Class_Class];

Goal "G\\<turnstile>S\\<preceq>U ==> \\<forall>T. G\\<turnstile>U\\<preceq>T --> G\\<turnstile>S\\<preceq>T";
by( etac widen.induct 1);
by   Safe_tac;
by(  ALLGOALS (forward_tac [widen_Class, widen_RefT]));
by  Safe_tac;
by(eatac rtrancl_trans 1 1);
qed_spec_mp "widen_trans";
