(*  Title:      HOL/MicroJava/BV/BVLcorrect.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

    Correctness of the lightweight bytecode verifier
*)

LBVCorrect = LBVSpec +

constdefs
fits :: "[method_type,instr list,jvm_prog,ty,state_type,state_type,certificate] \\<Rightarrow> bool"
"fits phi is G rT s0 s2 cert \\<equiv> fits_partial phi 0 is G rT s0 s2 cert"

fits_partial :: "[method_type,nat,instr list,jvm_prog,ty,state_type,state_type,certificate] \\<Rightarrow> bool" 
"fits_partial phi pc is G rT s0 s2 cert \\<equiv> (\\<forall> a b i s1. (a@(i#b) = is) \\<longrightarrow> 
                   wtl_inst_list a G rT s0 s1 cert (pc+length is) pc \\<longrightarrow> 
                   wtl_inst_list (i#b) G rT s1 s2 cert (pc+length is) (pc+length a) \\<longrightarrow> 
                      ((cert!(pc+length a)      = None   \\<longrightarrow> phi!(pc+length a) = s1) \\<and> 
                       (\\<forall> t. cert!(pc+length a) = Some t \\<longrightarrow> phi!(pc+length a) = t)))"
  
  
end
