(*  Title:      CCL/ex/Flag.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

(******)

val flag_defs = [Colour_def,red_def,white_def,blue_def,ccase_def];

(******)

val ColourXH = mk_XH_tac (the_context ()) (simp_type_defs @flag_defs) [] 
          "a : Colour <-> (a=red | a=white | a=blue)";

val Colour_case = XH_to_E ColourXH;

val redT = mk_canT_tac (the_context ()) [ColourXH] "red : Colour";
val whiteT = mk_canT_tac (the_context ()) [ColourXH] "white : Colour";
val blueT = mk_canT_tac (the_context ()) [ColourXH] "blue : Colour";


val ccaseT = mk_ncanT_tac (the_context ()) flag_defs case_rls case_rls
     "[| c:Colour; \
\        c=red ==> r : C(red); c=white ==> w : C(white); c=blue ==> b : C(blue) |] ==> \
\     ccase(c,r,w,b) : C(c)";

(***)

val prems = goalw (the_context ()) [flag_def]
    "flag : List(Colour)->List(Colour)*List(Colour)*List(Colour)";
by (typechk_tac [redT,whiteT,blueT,ccaseT] 1);
by clean_ccs_tac;
by (etac (ListPRI RS (ListPR_wf RS wfI)) 1);
by (assume_tac 1);
result();


val prems = goalw (the_context ()) [flag_def]
    "flag : PROD l:List(Colour).{x:List(Colour)*List(Colour)*List(Colour).FLAG(x,l)}";
by (gen_ccs_tac [redT,whiteT,blueT,ccaseT] 1);
by (REPEAT_SOME (ares_tac [ListPRI RS (ListPR_wf RS wfI)]));
