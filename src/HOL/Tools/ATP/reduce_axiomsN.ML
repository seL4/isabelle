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
(*       the third relevance filtering strategy                   *)
(******************************************************************)

(*** unit clauses ***)
datatype clause_type = Unit_neq | Unit_geq | Other

val add_unit = ref true;


fun literals_of_term args (Const ("Trueprop",_) $ P) = literals_of_term args P
  | literals_of_term args (Const ("op |",_) $ P $ Q) = 
    literals_of_term (literals_of_term args P) Q
  | literals_of_term args P = (P::args);


fun is_ground t = if (term_vars t = []) then (term_frees t = []) else false;


fun eq_clause_type (P,Q) = 
    if ((is_ground P) orelse (is_ground Q)) then Unit_geq else Other;

fun unit_clause_type (Const ("op =",_) $ P $ Q) = eq_clause_type (P,Q)
  | unit_clause_type _ = Unit_neq;

fun clause_type tm = 
    let val lits = literals_of_term [] tm
	val nlits = length lits
    in 
	if (nlits > 1) then Other
	else unit_clause_type (hd lits)
    end;

(*** constants with types ***)

datatype const_typ =  CTVar | CType of string * const_typ list

fun uni_type (CType (con1,args1)) (CType (con2,args2)) = (con1 = con2) andalso (uni_types args1 args2)
  | uni_type (CType (_,_)) CTVar = true
  | uni_type CTVar CTVar = true
  | uni_type CTVar _ = false

and 
     uni_types [] [] = true
      | uni_types (a1::as1) (a2::as2) = (uni_type a1 a2) andalso (uni_types as1 as2);



fun uni_constants (c1,ctp1) (c2,ctp2) = (c1 = c2) andalso (uni_types ctp1 ctp2);

fun uni_mem _ [] = false
  | uni_mem (c,c_typ) ((c1,c_typ1)::ctyps) = (uni_constants (c,c_typ) (c1,c_typ1)) orelse (uni_mem (c,c_typ) ctyps);



fun const_typ_of (Type (c,typs)) = CType (c,map const_typ_of typs) 
  | const_typ_of (TFree(_,_)) = CTVar
  | const_typ_of (TVar(_,_)) = CTVar


fun const_w_typ thy (c,tp) = 
    let val tvars = Sign.const_typargs thy (c,tp)
    in
	(c,map const_typ_of tvars)
    end;

fun add_term_consts_typs_rm thy ncs (Const(c, tp)) cs = if (c mem ncs) then cs else (const_w_typ thy (c,tp) ins cs)
  | add_term_consts_typs_rm thy ncs (t $ u) cs =
      add_term_consts_typs_rm thy ncs  t (add_term_consts_typs_rm thy ncs u cs)
  | add_term_consts_typs_rm thy ncs (Abs(_,_,t)) cs = add_term_consts_typs_rm thy ncs t cs
  | add_term_consts_typs_rm thy ncs _ cs = cs;

fun term_consts_typs_rm thy ncs t = add_term_consts_typs_rm thy ncs t [];

fun consts_typs_of_term thy term = term_consts_typs_rm thy ["Trueprop","==>","all","Ex","op &", "op |", "Not", "All", "op -->", "op =", "==", "True", "False"] term;


fun consts_typs_in_goal thy goal = consts_typs_of_term thy goal;

fun get_goal_consts_typs thy cs = foldl (op union) [] (map (consts_typs_in_goal thy) cs)


(******** filter clauses ********)

fun part3 gctyps [] (s1,s2) = (s1,s2)
  | part3 gctyps (s::ss) (s1,s2) = if (uni_mem s gctyps) then part3 gctyps ss (s::s1,s2) else part3 gctyps ss (s1,s::s2);


fun find_clause_weight_s_3 gctyps consts_typs wa =
    let val (rel,irrel) = part3 gctyps consts_typs ([],[])
    in
	((real (length rel))/(real (length consts_typs))) * wa
    end;


fun find_clause_weight_m_3 [] (_,w) = w
  | find_clause_weight_m_3 ((_,(_,(refconsts_typs,wa)))::y) (consts_typs,w) =
    let val w' = find_clause_weight_s_3 refconsts_typs consts_typs wa
    in
	if (w < w') then find_clause_weight_m_3 y (consts_typs,w')
	else find_clause_weight_m_3 y (consts_typs,w)
    end;


fun relevant_clauses_ax_g_3 _ [] _ (ax,r) = (ax,r)
  | relevant_clauses_ax_g_3 gctyps ((cls_typ,(clsthm,(consts_typs,_)))::y) P (ax,r) =
    let val weight = find_clause_weight_s_3 gctyps consts_typs 1.0
    in
	if P <= weight then relevant_clauses_ax_g_3 gctyps y P ((cls_typ,(clsthm,(consts_typs,weight)))::ax,r)
	else relevant_clauses_ax_g_3 gctyps y P (ax,(cls_typ,(clsthm,(consts_typs,weight)))::r)
    end;

fun relevant_clauses_ax_3 rel_axs [] P (addc,tmpc) keep =
    (case addc of [] => (rel_axs @ keep,tmpc)
		| _ => case tmpc of [] => (addc @ rel_axs @ keep,[])
				  | _ => relevant_clauses_ax_3 addc tmpc P ([],[]) (rel_axs @ keep))
  | relevant_clauses_ax_3 rel_axs ((cls_typ,(clsthm,(consts_typs,weight)))::e_axs) P (addc,tmpc) keep =
    let val weight' = find_clause_weight_m_3 rel_axs (consts_typs,weight)
	val e_ax' = (cls_typ,(clsthm,(consts_typs,weight')))
    in
	if P <= weight' then relevant_clauses_ax_3 rel_axs e_axs P (e_ax'::addc,tmpc) keep
	else relevant_clauses_ax_3 rel_axs e_axs P (addc,e_ax'::tmpc) keep
    end;

fun initialize3 thy [] ax_weights = ax_weights
  | initialize3 thy ((cls,thm)::clss_thms) ax_weights =
    let val tm = prop_of thm
	val cls_type = clause_type tm
	val consts = consts_typs_of_term thy tm
    in
	initialize3 thy clss_thms ((cls_type,((cls,thm),(consts,0.0)))::ax_weights)
    end;

fun add_unit_clauses ax [] = ax
  | add_unit_clauses ax ((cls_typ,consts_weight)::cs) =
    case cls_typ of Unit_neq => add_unit_clauses ((cls_typ,consts_weight)::ax) cs
		  | Unit_geq => add_unit_clauses ((cls_typ,consts_weight)::ax) cs
		  | Other => add_unit_clauses ax cs;

fun relevance_filter3_aux thy axioms goals = 
    let val pass = !pass_mark
	val axioms_weights = initialize3 thy axioms []
	val goals_consts_typs = get_goal_consts_typs thy goals
	val (rel_clauses,nrel_clauses) = relevant_clauses_ax_g_3 goals_consts_typs axioms_weights pass ([],[]) 
	val (ax,r) = relevant_clauses_ax_3 rel_clauses nrel_clauses pass ([],[]) []
    in
	if (!add_unit) then add_unit_clauses ax r else ax
    end;

fun relevance_filter3 thy axioms goals = map fst (map snd (relevance_filter3_aux thy axioms goals));
    


(******************************************************************)
(* Generic functions for relevance filtering                      *)
(******************************************************************)

exception RELEVANCE_FILTER of string;

fun relevance_filter thy axioms goals = 
    let val cls = (case (!strategy) of 1 => relevance_filter1 axioms goals
				     | 2 => relevance_filter2 axioms goals
				     | 3 => relevance_filter3 thy axioms goals
				     | _ => raise RELEVANCE_FILTER("strategy doesn't exists"))
    in
	cls
    end;


end;