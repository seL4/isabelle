(*  Title:      HOL/MicroJava/J/State.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [obj_ty_def] "obj_ty (C,fs) = Class C";
by (Simp_tac 1);
qed "obj_ty_def2";
Addsimps [obj_ty_def2];

Goalw [new_Addr_def] 
"(a,x) = new_Addr h ==> h a = None \\<and> x = None | x = Some OutOfMemory";
by(asm_full_simp_tac (simpset() addsimps [Pair_fst_snd_eq,select_split]) 1);
by(rtac someI 1);
by(rtac disjI2 1);
by(res_inst_tac [("r","snd (?a,Some OutOfMemory)")] trans 1);
by Auto_tac;
qed "new_AddrD";


Goalw [raise_if_def] "raise_if True x y \\<noteq> None";
by Auto_tac;
qed "raise_if_True";

Goalw [raise_if_def] "raise_if False x y = y";
by Auto_tac;
qed "raise_if_False";

Goalw [raise_if_def] "raise_if c x (Some y) \\<noteq> None";
by Auto_tac;
qed "raise_if_Some";

Goalw [raise_if_def] "raise_if c z (if x = None then Some y else x) \\<noteq> None";
by(induct_tac "x" 1);
by Auto_tac;
qed "raise_if_Some2";

Addsimps [raise_if_True,raise_if_False,raise_if_Some,raise_if_Some2];

Goalw [raise_if_def] 
  "raise_if c x y = Some z \\<longrightarrow> c \\<and>  Some z = Some x |  y = Some z"; 
by Auto_tac;
qed_spec_mp "raise_if_SomeD";

Goalw [raise_if_def] "raise_if c x y = None --> \\<not> c \\<and>  y = None";
by Auto_tac;
qed_spec_mp "raise_if_NoneD";

Goalw [np_def, raise_if_def] "np a' x' = None --> x' = None \\<and>  a' \\<noteq> Null"; 
by Auto_tac;
qed_spec_mp "np_NoneD";

Goalw [np_def, raise_if_def] "a' \\<noteq> Null --> np a' x' = x'";
by Auto_tac;
qed_spec_mp "np_None";

Goalw [np_def, raise_if_def] "np a' (Some xc) = Some xc";
by Auto_tac;
qed "np_Some";

Goalw [np_def, raise_if_def] "np Null None = Some NullPointer";
by Auto_tac;
qed "np_Null";

Goalw [np_def, raise_if_def] "np (Addr a) None = None";
by Auto_tac;
qed "np_Addr";

Addsimps[np_None, np_Some,np_Null,np_Addr];

Goalw [raise_if_def] "(np Null (raise_if c xc None)) = \
\ Some (if c then xc else NullPointer)";
by (Simp_tac 1);
qed "np_raise_if";
Addsimps[np_raise_if];





