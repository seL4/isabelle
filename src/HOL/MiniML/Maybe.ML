(* Title:     HOL/MiniML/Maybe.ML
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

(* constructor laws for option_bind *)
goalw thy [option_bind_def] "option_bind (Some s) f = (f s)";
by (Simp_tac 1);
qed "option_bind_Some";

goalw thy [option_bind_def] "option_bind None f = None";
by (Simp_tac 1);
qed "option_bind_None";

Addsimps [option_bind_Some,option_bind_None];

(* expansion of option_bind *)
goal thy
  "P(option_bind res f) = ((res = None --> P None) & (!s. res = Some s --> P(f s)))";
by (option.induct_tac "res" 1);
by (fast_tac (HOL_cs addss !simpset) 1);
by (Asm_simp_tac 1);
qed "expand_option_bind";

goal thy
  "((option_bind m f) = None) = ((m=None) | (? p. m = Some p & f p = None))";
by(simp_tac (!simpset addsplits [expand_option_bind]) 1);
qed "option_bind_eq_None";

Addsimps [option_bind_eq_None];

(* auxiliary lemma *)
goal Maybe.thy "(y = Some x) = (Some x = y)";
by( simp_tac (!simpset addsimps [eq_sym_conv]) 1);
qed "rotate_Some";
