(*  Title:      HOL/MicroJava/J/State.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

val the_Addr_Addr = prove_goalw thy [the_Addr_def] 
	"the_Addr (Addr a) = a" (K [Auto_tac]);

Addsimps [the_Addr_Addr];

val obj_ty_def2 = prove_goalw thy [obj_ty_def] "obj_ty (C,fs) = Class C" 
	(K [Simp_tac 1]);

Addsimps [obj_ty_def2];

val new_AddrD = prove_goalw thy [new_Addr_def] 
"\\<And>X. (a,x) = new_Addr h \\<Longrightarrow> h a = None \\<and>  x = None |  x = Some OutOfMemory" (K[
	asm_full_simp_tac (simpset() addsimps [Pair_fst_snd_eq,select_split]) 1,
	rtac selectI 1,
	rtac disjI2 1,
	res_inst_tac [("r","snd (a,Some OutOfMemory)")] trans 1,
	 Auto_tac ]);

val raise_if_True = prove_goalw thy [raise_if_def] 
	"raise_if True x y \\<noteq> None"
(K [split_tac [expand_if] 1,Auto_tac]);

val raise_if_False = prove_goalw thy [raise_if_def] 
	"raise_if False x y = y"
(K [Auto_tac]);

val raise_if_Some = prove_goalw thy [raise_if_def] 
	"raise_if c x (Some y) \\<noteq> None" (K [Auto_tac]);

val raise_if_Some2 = prove_goalw thy [raise_if_def] 
"raise_if c z (if x = None then Some y else x) \\<noteq> None" (K[
	induct_tac "x" 1,
	Auto_tac]);
val if_None_eq = prove_goal thy 
"(if x = None then None else x) = x" (K[
	induct_tac "x" 1,
	Auto_tac]);

Addsimps [raise_if_True,raise_if_False,raise_if_Some,raise_if_Some2,if_None_eq];

val raise_if_SomeD = prove_goalw thy [raise_if_def] 
	"raise_if c x y = Some z \\<longrightarrow> c \\<and>  Some z = Some x |  y = Some z" 
(K [split_tac [expand_if] 1,Auto_tac]) RS mp;

val raise_if_NoneD = prove_goalw thy [raise_if_def] 
	"raise_if c x y = None \\<longrightarrow> \\<not> c \\<and>  y = None"
(K [split_tac [expand_if] 1,Auto_tac]) RS mp;


val np_NoneD = (prove_goalw thy [np_def, raise_if_def] 
	"np a' x' = None \\<longrightarrow> x' = None \\<and>  a' \\<noteq> Null" (fn _ => [
	split_tac [expand_if] 1,
	Auto_tac ])) RS mp;
val np_None = (prove_goalw thy [np_def, raise_if_def] 
	"a' \\<noteq> Null \\<longrightarrow> np a' x' = x'" (fn _ => [
	split_tac [expand_if] 1,
	Auto_tac ])) RS mp;
val np_Some = prove_goalw thy [np_def, raise_if_def] "np a' (Some xc) = Some xc"
	(fn _ => [Auto_tac ]);
val np_Null = prove_goalw thy [np_def, raise_if_def] 
	"np Null None = Some NullPointer" (fn _ => [
	Auto_tac ]);
val np_Addr = prove_goalw thy [np_def, raise_if_def] "np (Addr a) None = None" 
	(fn _ => [Auto_tac ]);
Addsimps[np_None, np_Some,np_Null,np_Addr];






