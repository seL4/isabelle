(* first some logical trading *)

val prems = goal Focus_ex.thy
"is_g(g) = \ 
\ (? f. is_f(f) &  (!x.(? z. <g$x,z> = f$<x,z> &  \
\                  (! w y. <y,w> = f$<x,w>  --> z << w))))";
by (simp_tac (HOL_ss addsimps [is_g,is_net_g]) 1);
by (fast_tac HOL_cs 1);
val lemma1 = result();

val prems = goal Focus_ex.thy
"(? f. is_f(f) &  (!x. (? z. <g$x,z> = f$<x,z> &  \
\                 (!w y. <y,w> = f$<x,w>  --> z << w)))) \
\ = \ 
\ (? f. is_f(f) &  (!x. ? z.\
\       g$x = cfst$(f$<x,z>) &  \
\         z = csnd$(f$<x,z>) &  \
\       (! w y.  <y,w> = f$<x,w> --> z << w)))";
by (rtac iffI 1);
by (etac exE 1);
by (res_inst_tac [("x","f")] exI 1);
by (REPEAT (etac conjE 1));
by (etac conjI 1);
by (strip_tac 1);
by (etac allE 1);
by (etac exE 1);
by (res_inst_tac [("x","z")] exI 1);
by (REPEAT (etac conjE 1));
by (rtac conjI 1);
by (rtac conjI 2);
by (atac 3);
by (dtac sym 1);
by (asm_simp_tac HOLCF_ss 1);
by (dtac sym 1);
by (asm_simp_tac HOLCF_ss 1);
by (etac exE 1);
by (res_inst_tac [("x","f")] exI 1);
by (REPEAT (etac conjE 1));
by (etac conjI 1);
by (strip_tac 1);
by (etac allE 1);
by (etac exE 1);
by (res_inst_tac [("x","z")] exI 1);
by (REPEAT (etac conjE 1));
by (rtac conjI 1);
by (atac 2);
by (rtac trans 1);
by (rtac (surjective_pairing_Cprod2) 2);
by (etac subst 1);
by (etac subst 1);
by (rtac refl 1);
val lemma2 = result();

(* direction def_g(g) --> is_g(g) *)

val prems = goal Focus_ex.thy "def_g(g) --> is_g(g)";
by (simp_tac (HOL_ss addsimps [def_g,lemma1, lemma2]) 1);
by (rtac impI 1);
by (etac exE 1);
by (res_inst_tac [("x","f")] exI 1);
by (REPEAT (etac conjE 1));
by (etac conjI 1);
by (strip_tac 1);
by (res_inst_tac [("x","fix$(LAM k. csnd$(f$<x,k>))")] exI 1);
by (rtac conjI 1);
 by (asm_simp_tac HOLCF_ss 1);
 by (rtac trans 1);
  by (rtac surjective_pairing_Cprod2 2);
 by (rtac cfun_arg_cong 1);
 by (rtac trans 1);
  by (rtac fix_eq 1);
 by (Simp_tac 1);
by (strip_tac 1);
by (rtac fix_least 1);
by (Simp_tac 1);
by (etac exE 1);
by (dtac sym 1);
back();
by (asm_simp_tac HOLCF_ss 1);
val lemma3 = result();

(* direction is_g(g) --> def_g(g) *)
val prems = goal Focus_ex.thy "is_g(g) --> def_g(g)";
by (simp_tac (HOL_ss delsimps (ex_simps @ all_simps)
                     addsimps [lemma1,lemma2,def_g]) 1);
by (rtac impI 1);
by (etac exE 1);
by (res_inst_tac [("x","f")] exI 1);
by (REPEAT (etac conjE 1));
by (etac conjI 1);
by (rtac ext_cfun 1);
by (eres_inst_tac [("x","x")] allE 1);
by (etac exE 1);
by (REPEAT (etac conjE 1));
by (subgoal_tac "fix$(LAM k. csnd$(f$<x, k>)) = z" 1);
 by (asm_simp_tac HOLCF_ss 1);
by (subgoal_tac "! w y. f$<x, w> = <y, w>  --> z << w" 1);
by (rtac sym 1);
by (rtac fix_eqI 1);
by (asm_simp_tac HOLCF_ss 1);
by (rtac allI 1);
by (simp_tac HOLCF_ss 1);
by (strip_tac 1);
by (subgoal_tac "f$<x, za> = <cfst$(f$<x,za>),za>" 1);
by (fast_tac HOL_cs 1);
by (rtac trans 1);
by (rtac (surjective_pairing_Cprod2 RS sym) 1);
by (etac cfun_arg_cong 1);
by (strip_tac 1);
by (REPEAT (etac allE 1));
by (etac mp 1);
by (etac sym 1);
val lemma4 = result();

(* now we assemble the result *)

val prems = goal Focus_ex.thy "def_g = is_g";
by (rtac ext 1);
by (rtac iffI 1);
by (etac (lemma3 RS mp) 1);
by (etac (lemma4 RS mp) 1);
val loopback_eq = result();

val prems = goal Focus_ex.thy 
"(? f.\
\ is_f(f::'b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream))\
\ -->\
\ (? g. def_g(g::'b stream -> 'c stream ))";
by (simp_tac (HOL_ss addsimps [def_g]) 1);
val L2 = result();

val prems = goal Focus_ex.thy 
"(? f.\
\ is_f(f::'b stream * ('b,'c) tc stream -> 'c stream * ('b,'c) tc stream))\
\ -->\
\ (? g. is_g(g::'b stream -> 'c stream ))";
by (rtac (loopback_eq RS subst) 1);
by (rtac L2 1);
val conservative_loopback = result();
