structure ReduceAxiomsN =
(* Author: Jia Meng, Cambridge University Computer Laboratory
   
   Two filtering strategies *)

struct

val pass_mark = ref 0.5;
val strategy = ref 1;

fun pol_to_int true = 1
  | pol_to_int false = ~1;

fun part refs [] (s1,s2) = (s1,s2)
  | part refs (s::ss) (s1,s2) = if (s mem refs) then (part refs ss (s::s1,s2)) else (part refs ss (s1,s::s2));


fun pol_mem _ [] = false
  | pol_mem (pol,const) ((p,c)::pcs) = if ((pol = not p) andalso (const = c)) then true else pol_mem (pol,const) pcs;


fun part_w_pol refs [] (s1,s2) = (s1,s2)
  | part_w_pol refs (s::ss) (s1,s2) = if (pol_mem s refs) then (part_w_pol refs ss (s::s1,s2)) else (part_w_pol refs ss (s1,s::s2));


fun add_term_consts_rm ncs (Const(c, _)) cs = if (c mem ncs) then cs else (c ins_string cs)
  | add_term_consts_rm ncs (t $ u) cs =
      add_term_consts_rm ncs t (add_term_consts_rm ncs u cs)
  | add_term_consts_rm ncs (Abs(_,_,t)) cs = add_term_consts_rm ncs t cs
  | add_term_consts_rm ncs _ cs = cs;

fun term_consts_rm ncs t = add_term_consts_rm ncs t [];

fun consts_of_term term = term_consts_rm ["Trueprop","==>","all","Ex","op &", "op |", "Not", "All", "op -->", "op =", "==", "True", "False"] term;


fun add_term_pconsts_rm ncs (Const(c,_)) pol cs = if (c mem ncs) then cs else ((pol,c) ins cs)
  | add_term_pconsts_rm ncs (Const("Not",_)$P) pol cs = add_term_pconsts_rm ncs P (not pol) cs
  | add_term_pconsts_rm ncs (P$Q) pol cs = 
    add_term_pconsts_rm ncs P pol (add_term_pconsts_rm ncs Q pol cs)
  | add_term_pconsts_rm ncs (Abs(_,_,t)) pol cs = add_term_pconsts_rm ncs t pol cs
  | add_term_pconsts_rm ncs _ _ cs = cs;


fun term_pconsts_rm ncs t = add_term_pconsts_rm ncs t true [];


fun pconsts_of_term term = term_pconsts_rm ["Trueprop","==>","all","Ex","op &", "op |", "Not", "All", "op -->", "op =", "==", "True", "False"] term;

fun consts_in_goal goal = consts_of_term goal;
fun get_goal_consts cs = foldl (op union_string) [] (map consts_in_goal cs);


fun pconsts_in_goal goal = pconsts_of_term goal;
fun get_goal_pconsts cs = foldl (op union) [] (map pconsts_in_goal cs);


(*************************************************************************)
(*            the first relevance filtering strategy                     *)
(*************************************************************************)

fun find_clause_weight_s_1 (refconsts : string list) consts wa = 
    let val (rel,irrel) = part refconsts consts ([],[])
    in
	((real (length rel))/(real (length consts))) * wa
    end;

fun find_clause_weight_m_1 [] (_,w) = w 
  | find_clause_weight_m_1 ((_,(refconsts,wa))::y) (consts,w) =
    let val w' = find_clause_weight_s_1 refconsts consts wa
    in
	if (w < w') then find_clause_weight_m_1 y (consts,w')
	else find_clause_weight_m_1 y (consts,w)
    end;


fun relevant_clauses_ax_g_1 _ []  _ (ax,r) = (ax,r)
  | relevant_clauses_ax_g_1 gconsts  ((clsthm,(consts,_))::y) P (ax,r) =
    let val weight = find_clause_weight_s_1 gconsts consts 1.0
    in
	if  P <= weight then relevant_clauses_ax_g_1 gconsts y P ((clsthm,(consts,weight))::ax,r)
	else relevant_clauses_ax_g_1 gconsts y P (ax,(clsthm,(consts,weight))::r)
    end;


fun relevant_clauses_ax_1 rel_axs  [] P (addc,tmpc) keep = 
    (case addc of [] => rel_axs @ keep
		| _ => case tmpc of [] => addc @ rel_axs @ keep
				  | _ => relevant_clauses_ax_1 addc tmpc P ([],[]) (rel_axs @ keep))
  | relevant_clauses_ax_1 rel_axs ((clsthm,(consts,weight))::e_axs) P (addc,tmpc) keep = 
    let val weight' = find_clause_weight_m_1 rel_axs (consts,weight) 
	val e_ax' = (clsthm,(consts, weight'))
    in
	
	if P <= weight' then relevant_clauses_ax_1 rel_axs e_axs P ((clsthm,(consts,weight'))::addc,tmpc) keep
	else relevant_clauses_ax_1 rel_axs e_axs P (addc,(clsthm,(consts,weight'))::tmpc) keep 
    end;


fun initialize [] ax_weights = ax_weights
  | initialize ((cls,thm)::clss_thms) ax_weights =
    let val tm = prop_of thm
	val consts = consts_of_term tm
    in
	initialize clss_thms (((cls,thm),(consts,0.0))::ax_weights)
    end;

fun relevance_filter1_aux axioms goals = 
    let val pass = !pass_mark
	val axioms_weights = initialize axioms []
	val goals_consts = get_goal_consts goals
	val (rel_clauses,nrel_clauses) = relevant_clauses_ax_g_1 goals_consts axioms_weights pass ([],[]) 
    in
	relevant_clauses_ax_1 rel_clauses nrel_clauses pass ([],[]) []
    end;

fun relevance_filter1 axioms goals = map fst (relevance_filter1_aux axioms goals);




(*************************************************************************)
(*            the second relevance filtering strategy                    *)
(*************************************************************************)

fun find_clause_weight_s_2 (refpconsts : (bool * string) list) pconsts wa = 
    let val (rel,irrel) = part_w_pol refpconsts pconsts ([],[])
    in
	((real (length rel))/(real (length pconsts))) * wa
    end;

fun find_clause_weight_m_2 [] (_,w) = w 
  | find_clause_weight_m_2 ((_,(refpconsts,wa))::y) (pconsts,w) =
    let val w' = find_clause_weight_s_2 refpconsts pconsts wa
    in
	if (w < w') then find_clause_weight_m_2 y (pconsts,w')
	else find_clause_weight_m_2 y (pconsts,w)
    end;


fun relevant_clauses_ax_g_2 _ []  _ (ax,r) = (ax,r)
  | relevant_clauses_ax_g_2 gpconsts  ((clsthm,(pconsts,_))::y) P (ax,r) =
    let val weight = find_clause_weight_s_2 gpconsts pconsts 1.0
    in
	if  P <= weight then relevant_clauses_ax_g_2 gpconsts y P ((clsthm,(pconsts,weight))::ax,r)
	else relevant_clauses_ax_g_2 gpconsts y P (ax,(clsthm,(pconsts,weight))::r)
    end;


fun relevant_clauses_ax_2 rel_axs  [] P (addc,tmpc) keep = 
    (case addc of [] => rel_axs @ keep
		| _ => case tmpc of [] => addc @ rel_axs @ keep
				  | _ => relevant_clauses_ax_2 addc tmpc P ([],[]) (rel_axs @ keep))
  | relevant_clauses_ax_2 rel_axs ((clsthm,(pconsts,weight))::e_axs) P (addc,tmpc) keep = 
    let val weight' = find_clause_weight_m_2 rel_axs (pconsts,weight) 
	val e_ax' = (clsthm,(pconsts, weight'))
    in
	
	if P <= weight' then relevant_clauses_ax_2 rel_axs e_axs P ((clsthm,(pconsts,weight'))::addc,tmpc) keep
	else relevant_clauses_ax_2 rel_axs e_axs P (addc,(clsthm,(pconsts,weight'))::tmpc) keep 
    end;


fun initialize_w_pol [] ax_weights = ax_weights
  | initialize_w_pol ((cls,thm)::clss_thms) ax_weights =
    let val tm = prop_of thm
	val consts = pconsts_of_term tm
    in
	initialize_w_pol clss_thms (((cls,thm),(consts,0.0))::ax_weights)
    end;


fun relevance_filter2_aux axioms goals = 
    let val pass = !pass_mark
	val axioms_weights = initialize_w_pol axioms []
	val goals_consts = get_goal_pconsts goals
	val (rel_clauses,nrel_clauses) = relevant_clauses_ax_g_2 goals_consts axioms_weights pass ([],[]) 
    in
	relevant_clauses_ax_2 rel_clauses nrel_clauses pass ([],[]) []
    end;

fun relevance_filter2 axioms goals = map fst (relevance_filter2_aux axioms goals);




(******************************************************************)
(* Generic functions for relevance filtering                      *)
(******************************************************************)

exception RELEVANCE_FILTER of string;

fun relevance_filter axioms goals = 
    let val cls = (case (!strategy) of 1 => relevance_filter1 axioms goals
				     | 2 => relevance_filter2 axioms goals
				     | _ => raise RELEVANCE_FILTER("strategy doesn't exists"))
    in
	cls
    end;


end;