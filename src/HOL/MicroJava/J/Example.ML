open Example;

AddIs [widen.null];

Addsimps [inj_cnam_, inj_vnam_];
Addsimps [Base_not_Object,Ext_not_Object];
Addsimps [Base_not_Object RS not_sym,Ext_not_Object RS not_sym];

val map_of_Cons = prove_goalw thy [get_def thy "map_of_list"] 
"map_of (p#ps) = (map_of ps)(fst p |-> snd p)" (K [Simp_tac 1]);
val map_of_Cons1 = prove_goalw Map.thy [get_def thy "map_of_list"] 
"map_of ((x,y)#ps) x = Some y" (K [Simp_tac 1]);
val map_of_Cons2 = prove_goalw Map.thy [get_def thy "map_of_list"] 
"!!X. x\\<noteq>k ==> map_of ((k,y)#ps) x = map_of ps x" (K [Asm_simp_tac 1]);
Delsimps[map_of_Cons]; (* sic! *)
Addsimps[map_of_Cons1, map_of_Cons2];

val class_tprg_Object = prove_goalw thy [class_def, ObjectC_def] 
 	"class tprg Object = Some (None, [], [])" 
	(K [Simp_tac 1]);
val class_tprg_Base = prove_goalw thy [class_def, ObjectC_def, BaseC_def, 
 ExtC_def] "class tprg Base = Some (Some Object, \
	\ [(vee, PrimT Boolean)], \
        \ [((foo, [Class Base]), Class Base, foo_Base)])" (K [
	Simp_tac 1]);
val class_tprg_Ext = prove_goalw thy [class_def, ObjectC_def, BaseC_def, 
 ExtC_def] "class tprg Ext = Some (Some Base, \
	\ [(vee, PrimT Integer)], \
        \ [((foo, [Class Base]), Class Ext, foo_Ext)])" (K [
	Simp_tac 1]);
Addsimps [class_tprg_Object, class_tprg_Base, class_tprg_Ext];

Goal "!!X. (Object,C) \\<in> (subcls1 tprg)^+ ==> R";
by (auto_tac (claset() addSDs [tranclD,subcls1D],simpset()));
qed "not_Object_subcls";
AddSEs [not_Object_subcls];

Goal "tprg\\<turnstile>Object\\<preceq>C C ==> C = Object";
be rtrancl_induct 1;
by  Auto_tac;
bd subcls1D 1;
by Auto_tac;
qed "subcls_ObjectD";
AddSDs[subcls_ObjectD];

Goal "!!X. (Base, Ext) \\<in> (subcls1 tprg)^+ ==> R";
by (auto_tac (claset() addSDs [tranclD,subcls1D],simpset()));
qed "not_Base_subcls_Ext";
AddSEs [not_Base_subcls_Ext];

Goalw [class_def, ObjectC_def, BaseC_def, ExtC_def] "class tprg C = Some z ==> C=Object \\<or> C=Base \\<or> C=Ext";
by (auto_tac (claset(),simpset()addsimps[]addsplits[split_if_asm]));
qed "class_tprgD";

Goal "(C,C) \\<in> (subcls1 tprg)^+ ==> R";
by (auto_tac (claset() addSDs [tranclD,subcls1D],simpset()));
by (ftac class_tprgD 1);
by (auto_tac (claset() addSDs [],simpset()));
bd rtranclD 1;
by Auto_tac;
qed "not_class_subcls_class";
AddSEs [not_class_subcls_class];

goalw thy [ObjectC_def, BaseC_def, ExtC_def] "unique tprg";
by (Simp_tac 1);
qed "unique_classes";

bind_thm ("subcls_direct", subcls1I RS r_into_rtrancl);

Goalw [] "tprg\\<turnstile>Ext\\<preceq>C Base";
br subcls_direct 1;
by (Simp_tac 1);
qed "Ext_subcls_Base";
Addsimps [Ext_subcls_Base];

Goalw [] "tprg\\<turnstile>Class Ext\\<preceq> Class Base";
br widen.subcls 1;
by (Simp_tac 1);
qed "Ext_widen_Base";
Addsimps [Ext_widen_Base];

AddSIs ty_expr_ty_exprs_wt_stmt.intrs;


Goal "acyclic (subcls1 tprg)";
br acyclicI 1;
by Safe_tac ;
qed "acyclic_subcls1_";

val wf_subcls1_=acyclic_subcls1_ RS(finite_subcls1 RS finite_acyclic_wf_converse);


Addsimps[is_class_def];

val fields_rec_ = wf_subcls1_ RSN (1, fields_rec_lemma);

Goal "fields (tprg, Object) = []";
by (stac fields_rec_ 1);
by   Auto_tac;
qed "fields_Object";
Addsimps [fields_Object];

Goal "fields (tprg,Base) = [((vee, Base), PrimT Boolean)]";
by (stac fields_rec_ 1);
by   Auto_tac;
qed "fields_Base";
Addsimps [fields_Base];

Goal "fields (tprg, Ext)  = [((vee, Ext ), PrimT Integer)] @\
                                    \ fields (tprg, Base)";
br trans 1;
br  fields_rec_ 1;
by   Auto_tac;
qed "fields_Ext";
Addsimps [fields_Ext];

val method_rec_ = wf_subcls1_ RS method_rec_lemma;

Goal "method (tprg,Object) = map_of []";
by (stac method_rec_ 1);
by  Auto_tac;
qed "method_Object";
Addsimps [method_Object];

Goal "method (tprg, Base) = map_of \
\ [((foo, [Class Base]), Base, (Class Base, foo_Base))]";
br trans 1;
br  method_rec_ 1;
by  Auto_tac;
qed "method_Base";
Addsimps [method_Base];

Goal "method (tprg, Ext) = (method (tprg, Base) \\<oplus> map_of \
\ [((foo, [Class Base]), Ext , (Class Ext, foo_Ext))])";
br trans 1;
br  method_rec_ 1;
by  Auto_tac;
qed "method_Ext";
Addsimps [method_Ext];

Goalw [wf_mdecl_def,wf_mhead_def,wf_java_mdecl_def,foo_Base_def] 
"wf_mdecl wf_java_mdecl tprg Base ((foo, [Class Base]), (Class Base, foo_Base))";
by Auto_tac;
qed "wf_foo_Base";

Goalw [wf_mdecl_def,wf_mhead_def,wf_java_mdecl_def,foo_Ext_def] 
"wf_mdecl wf_java_mdecl tprg Ext ((foo, [Class Base]), (Class Ext, foo_Ext))";
by Auto_tac;
br  ty_expr_ty_exprs_wt_stmt.Cast 1;
by   (Simp_tac 2);
br   cast.subcls 2;
by   (rewtac field_def);
by   Auto_tac;
qed "wf_foo_Ext";

Goalw [wf_cdecl_def, wf_fdecl_def, ObjectC_def] 
"wf_cdecl wf_java_mdecl tprg ObjectC";
by (Simp_tac 1);
qed "wf_ObjectC";

Goalw [wf_cdecl_def, wf_fdecl_def, BaseC_def] 
"wf_cdecl wf_java_mdecl tprg BaseC";
by (Simp_tac 1);
by (fold_goals_tac [BaseC_def]);
br (wf_foo_Base RS conjI) 1;
by Auto_tac;
qed "wf_BaseC";

Goalw [wf_cdecl_def, wf_fdecl_def, ExtC_def] 
"wf_cdecl wf_java_mdecl tprg ExtC";
by (Simp_tac 1);
by (fold_goals_tac [ExtC_def]);
br (wf_foo_Ext RS conjI) 1;
by Auto_tac;
bd rtranclD 1;
by Auto_tac;
qed "wf_ExtC";

Goalw [wf_prog_def,Let_def] 
"wf_prog wf_java_mdecl tprg";
by(simp_tac (simpset() addsimps [wf_ObjectC,wf_BaseC,wf_ExtC,unique_classes])1);
qed "wf_tprg";

Goalw [appl_methds_def] 
"appl_methds tprg Base (foo, [NT]) = \
\ {((Class Base, Class Base), [Class Base])}";
by (Simp_tac 1);
by (subgoal_tac "tprg\\<turnstile>NT\\<preceq> Class Base" 1);
by  (auto_tac (claset(), simpset() addsimps [map_of_Cons,foo_Base_def]));
qed "appl_methds_foo_Base";

Goalw [max_spec_def] "max_spec tprg Base (foo, [NT]) = \
\ {((Class Base, Class Base), [Class Base])}";
by (auto_tac (claset(), simpset() addsimps [appl_methds_foo_Base]));
qed "max_spec_foo_Base";

fun t thm = resolve_tac ty_expr_ty_exprs_wt_stmt.intrs 1 thm;
Goalw [test_def] "(tprg, empty(e\\<mapsto>Class Base))\\<turnstile>\ 
\ Expr(e::=NewC Ext);; Expr(LAcc e..foo({?pTs'}[Lit Null]))\\<surd>";
(* ?pTs' = [Class Base] *)
by t;		(* ;; *)
by  t;		(* Expr *)
by  t;		(* LAss *)
by    t;	(* LAcc *)
by     (Simp_tac 1);
by    (Simp_tac 1);
by   t;	(* NewC *)
by   (Simp_tac 1);
by  (Simp_tac 1);
by t;	(* Expr *)
by t;	(* Call *)
by   t;	(* LAcc *)
by    (Simp_tac 1);
by   (Simp_tac 1);
by  t;	(* Cons *)
by   t;	(* Lit *)
by   (Simp_tac 1);
by  t;	(* Nil *)
by (Simp_tac 1);
br max_spec_foo_Base 1;
qed "wt_test";

fun e thm = resolve_tac (NewCI::eval_evals_exec.intrs) 1 thm;

Delsplits[split_if];
Addsimps[init_vars_def,c_hupd_def,cast_ok_def];
Goalw [test_def] 
" [|new_Addr (heap (snd s0)) = (a, None)|] ==> \
\ tprg\\<turnstile>s0 -test-> ?s";
(* ?s = s3 *)
by e;		(* ;; *)
by  e;		(* Expr *)
by  e;		(* LAss *)
by   e;	(* NewC *)
by    (Force_tac 1);
by   (Force_tac 1);
by  (Simp_tac 1);
be thin_rl 1;
by e;	(* Expr *)
by e;	(* Call *)
by       e;	(* LAcc *)
by      (Force_tac 1);
by     e;	(* Cons *)
by      e;	(* Lit *)
by     e;	(* Nil *)
by    (Simp_tac 1);
by   (force_tac (claset(), simpset() addsimps [foo_Ext_def]) 1);
by  (Simp_tac 1);
by  e;	(* Expr *)
by  e;	(* FAss *)
by       e;(* Cast *)
by        e;(* LAcc *)
by       (Simp_tac 1);
by      (Simp_tac 1);
by     (Simp_tac 1);
by     e;(* XcptE *)
by    (Simp_tac 1);
by   (EVERY'[rtac (surjective_pairing RS sym RSN (2,trans)), stac Pair_eq,
             Force_tac] 1);
by  (Simp_tac 1);
by (Simp_tac 1);
by e;	(* XcptE *)
bind_thm ("exec_test", simplify (simpset()) (result()));
