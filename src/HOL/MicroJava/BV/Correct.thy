(*  Title:      HOL/MicroJava/BV/Correct.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

The invariant for the type safety proof.
*)

Correct = BVSpec + 

constdefs
 approx_val :: "[jvm_prog,aheap,val,ty option] \\<Rightarrow> bool"
"approx_val G h v any \\<equiv> case any of None \\<Rightarrow> True | Some T \\<Rightarrow> G,h\\<turnstile>v\\<Colon>\\<preceq>T"

 approx_loc :: "[jvm_prog,aheap,val list,locvars_type] \\<Rightarrow> bool"
"approx_loc G hp loc LT \\<equiv> 
   length loc=length LT \\<and> (\\<forall>(val,any)\\<in>set (zip loc LT). approx_val G hp val any)" 

 approx_stk :: "[jvm_prog,aheap,opstack,opstack_type] \\<Rightarrow> bool"
"approx_stk G hp stk ST \\<equiv> approx_loc G hp stk (map Some ST)"

 correct_frame  :: "[jvm_prog,aheap,state_type,nat,bytecode] \\<Rightarrow> frame \\<Rightarrow> bool"
"correct_frame G hp \\<equiv> \\<lambda>(ST,LT) maxl ins (stk,loc,C,sig,pc).
   approx_stk G hp stk ST  \\<and> approx_loc G hp loc LT \\<and> 
   pc < length ins \\<and> length loc=length(snd sig)+maxl+1"

consts
 correct_frames  :: "[jvm_prog,aheap,prog_type,ty,sig,frame list] \\<Rightarrow> bool"
primrec
"correct_frames G hp phi rT0 sig0 [] = True"

"correct_frames G hp phi rT0 sig0 (f#frs) =
	(let (stk,loc,C,sig,pc) = f;
	     (ST,LT) = (phi C sig) ! pc
	 in
         (\\<exists>rT maxl ins.
         method (G,C) sig = Some(C,rT,(maxl,ins)) \\<and>
	 (\\<exists>mn pTs k. pc = k+1 \\<and> ins!k = MI(Invoke mn pTs) \\<and>
         (mn,pTs) = sig0 \\<and> 
         (\\<exists>apTs D ST'.
         fst((phi C sig)!k) = (rev apTs) @ (Class D) # ST' \\<and>
         length apTs = length pTs \\<and>
         (\\<exists>D' rT' maxl' ins'.
           method (G,D) (mn,pTs) = Some(D',rT',(maxl',ins')) \\<and>
           G \\<turnstile> rT0 \\<preceq> rT') \\<and>
	 correct_frame G hp (tl ST, LT) maxl ins f \\<and> 
	 correct_frames G hp phi rT sig frs))))"


constdefs
 correct_state :: "[jvm_prog,prog_type,jvm_state] \\<Rightarrow> bool"
                  ("_,_\\<turnstile>JVM _\\<surd>"  [51,51] 50)
"correct_state G phi \\<equiv> \\<lambda>(xp,hp,frs).
   case xp of
     None \\<Rightarrow> (case frs of
	           [] \\<Rightarrow> True
             | (f#fs) \\<Rightarrow> G\\<turnstile>h hp\\<surd> \\<and>
			(let (stk,loc,C,sig,pc) = f
		         in
                         \\<exists>rT maxl ins.
                         method (G,C) sig = Some(C,rT,(maxl,ins)) \\<and>
			 correct_frame G hp ((phi C sig) ! pc) maxl ins f \\<and> 
		         correct_frames G hp phi rT sig fs))
   | Some x \\<Rightarrow> True" 

end
