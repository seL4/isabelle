(*  Title:      HOL/MicroJava/J/Prog.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

val finite_is_class = prove_goalw thy [is_class_def,class_def,o_def] "finite {C. is_class G C}" (K [
	rtac finite_map_of 1]);

val is_classI = prove_goalw thy [is_class_def]
"\\<And>G. class G C = Some c \\<Longrightarrow> is_class G C" (K [Auto_tac]);

val is_classD = prove_goalw thy [is_class_def]
"\\<And>G. is_class G C \\<Longrightarrow> \\<exists>sc fs ms. class G C = Some (sc,fs,ms)" (K [
	not_None_tac 1, pair_tac "y" 1, pair_tac "ya" 1, Auto_tac]);
