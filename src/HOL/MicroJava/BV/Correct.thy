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
"correct_frame G hp \\<equiv> \\<lambda>(ST,LT) maxl ins (stk,loc,C,ml,pc).
   approx_stk G hp stk ST  \\<and> approx_loc G hp loc LT \\<and> 
   pc < length ins \\<and> length loc=length(snd ml)+maxl+1"

consts
 correct_frames  :: "[jvm_prog,aheap,prog_type,ty,cname,sig,frame list] \\<Rightarrow> bool"
primrec
"correct_frames G hp phi rT0 C0 ml0 [] = False"

"correct_frames G hp phi rT0 C0 ml0 (f#frs) =
	(let (stk,loc,C,ml,pc) = f;
	     (ST,LT) = (phi C ml) ! pc
	 in
         (\\<exists>rT maxl ins.
         cmethd (G,C) ml = Some(C,rT,(maxl,ins)) \\<and>
	 (\\<exists>mn pTs k. pc = k+1 \\<and> ins!k = MI(Invokevirtual mn pTs) \\<and>
         (mn,pTs) = ml0 \\<and> 
         (\\<exists>apTs D ST'.
         fst((phi C ml)!k) = (rev apTs) @ (Class D) # ST' \\<and>
         length apTs = length pTs \\<and>
         (\\<exists>D' rT' maxl' ins'.
           cmethd (G,D) (mn,pTs) = Some(D',rT',(maxl',ins')) \\<and>
           G \\<turnstile> rT0 \\<preceq> rT') \\<and>
	 correct_frame G hp (tl ST, LT) maxl ins f \\<and> 
	 correct_frames G hp phi rT C ml frs))))"


constdefs
 correct_state :: "[jvm_prog,prog_type,jvm_state] \\<Rightarrow> bool"
"correct_state G phi \\<equiv> \\<lambda>(xp,hp,frs).
   case xp of
     None \\<Rightarrow> (case frs of
	           [] \\<Rightarrow> True
             | (f#fs) \\<Rightarrow> (let (stk,loc,C,ml,pc) = f
		         in
                         \\<exists>rT maxl ins.
                         cmethd (G,C) ml = Some(C,rT,(maxl,ins)) \\<and>
		         G,hp\\<turnstile>\\<surd> \\<and> 
			 correct_frame G hp ((phi C ml) ! pc) maxl ins f \\<and> 
		         correct_frames G hp phi rT C ml fs))
   | Some x \\<Rightarrow> True" 

end
