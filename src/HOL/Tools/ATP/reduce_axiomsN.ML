(* Authors: Jia Meng, NICTA and Lawrence C Paulson, Cambridge University Computer Laboratory
   ID: $Id$
   Filtering strategies *)

structure ReduceAxiomsN =
struct

val pass_mark = ref 0.5;
val strategy = ref 1;

fun pol_to_int true = 1
  | pol_to_int false = ~1;

fun part refs [] (s1,s2) = (s1,s2)
  | part refs (s::ss) (s1,s2) = 
      if (s mem refs) then part refs ss (s::s1,s2) else part refs ss (s1,s::s2);


fun pol_mem _ [] = false
  | pol_mem (pol,const) ((p,c)::pcs) =
      (pol = not p andalso const = c) orelse pol_mem (pol,const) pcs;


fun part_w_pol refs [] (s1,s2) = (s1,s2)
  | part_w_pol refs (s::ss) (s1,s2) =
      if (pol_mem s refs) then part_w_pol refs ss (s::s1,s2) 
      else part_w_pol refs ss (s1,s::s2);


fun add_term_consts_rm ncs (Const(c, _)) cs =
      if (c mem ncs) then cs else (c ins_string cs)
  | add_term_consts_rm ncs (t $ u) cs =
      add_term_consts_rm ncs t (add_term_consts_rm ncs u cs)
  | add_term_consts_rm ncs (Abs(_,_,t)) cs = add_term_consts_rm ncs t cs
  | add_term_consts_rm ncs _ cs = cs;

fun term_consts_rm ncs t = add_term_consts_rm ncs t [];

val standard_consts =
  ["Trueprop","==>","all","Ex","op &","op |","Not","All","op -->","op =","==","True","False"];

val consts_of_term = term_consts_rm standard_consts;


fun add_term_pconsts_rm ncs (Const(c,_)) pol cs = if c mem ncs then cs else ((pol,c) ins cs)
  | add_term_pconsts_rm ncs (Const("Not",_)$P) pol cs = add_term_pconsts_rm ncs P (not pol) cs
  | add_term_pconsts_rm ncs (P$Q) pol cs = 
    add_term_pconsts_rm ncs P pol (add_term_pconsts_rm ncs Q pol cs)
  | add_term_pconsts_rm ncs (Abs(_,_,t)) pol cs = add_term_pconsts_rm ncs t pol cs
  | add_term_pconsts_rm ncs _ _ cs = cs;


fun term_pconsts_rm ncs t = add_term_pconsts_rm ncs t true [];

val pconsts_of_term = term_pconsts_rm standard_consts;

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
	(real (length rel) / real (length consts)) * wa
    end;

fun find_clause_weight_m_1 [] (_,w) = w 
  | find_clause_weight_m_1 ((_,(refconsts,wa))::y) (consts,w) =
      let val w' = find_clause_weight_s_1 refconsts consts wa
      in
	if w < w' then find_clause_weight_m_1 y (consts,w')
	else find_clause_weight_m_1 y (consts,w)
      end;


fun relevant_clauses_ax_g_1 _ []  _ (ax,r) = (ax,r)
  | relevant_clauses_ax_g_1 gconsts  ((clstm,(consts,_))::y) P (ax,r) =
      let val weight = find_clause_weight_s_1 gconsts consts 1.0
      in
	if  P <= weight 
	then relevant_clauses_ax_g_1 gconsts y P ((clstm,(consts,weight))::ax,r)
	else relevant_clauses_ax_g_1 gconsts y P (ax,(clstm,(consts,weight))::r)
      end;


fun relevant_clauses_ax_1 rel_axs  [] P (addc,tmpc) keep = 
    (case addc of [] => rel_axs @ keep
		| _ => case tmpc of [] => addc @ rel_axs @ keep
				  | _ => relevant_clauses_ax_1 addc tmpc P ([],[]) (rel_axs @ keep))
  | relevant_clauses_ax_1 rel_axs ((clstm,(consts,weight))::e_axs) P (addc,tmpc) keep = 
      let val weight' = find_clause_weight_m_1 rel_axs (consts,weight) 
	  val e_ax' = (clstm,(consts, weight'))
      in
	if P <= weight' 
	then relevant_clauses_ax_1 rel_axs e_axs P ((clstm,(consts,weight'))::addc,tmpc) keep
	else relevant_clauses_ax_1 rel_axs e_axs P (addc,(clstm,(consts,weight'))::tmpc) keep 
      end;


fun initialize [] ax_weights = ax_weights
  | initialize ((tm,name)::tms_names) ax_weights =
      let val consts = consts_of_term tm
      in
	  initialize tms_names (((tm,name),(consts,0.0))::ax_weights)
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
  | relevant_clauses_ax_g_2 gpconsts  ((clstm,(pconsts,_))::y) P (ax,r) =
    let val weight = find_clause_weight_s_2 gpconsts pconsts 1.0
    in
	if  P <= weight then relevant_clauses_ax_g_2 gpconsts y P ((clstm,(pconsts,weight))::ax,r)
	else relevant_clauses_ax_g_2 gpconsts y P (ax,(clstm,(pconsts,weight))::r)
    end;


fun relevant_clauses_ax_2 rel_axs  [] P (addc,tmpc) keep = 
    (case addc of [] => rel_axs @ keep
		| _ => case tmpc of [] => addc @ rel_axs @ keep
				  | _ => relevant_clauses_ax_2 addc tmpc P ([],[]) (rel_axs @ keep))
  | relevant_clauses_ax_2 rel_axs ((clstm,(pconsts,weight))::e_axs) P (addc,tmpc) keep = 
    let val weight' = find_clause_weight_m_2 rel_axs (pconsts,weight) 
	val e_ax' = (clstm,(pconsts, weight'))
    in
	
	if P <= weight' then relevant_clauses_ax_2 rel_axs e_axs P ((clstm,(pconsts,weight'))::addc,tmpc) keep
	else relevant_clauses_ax_2 rel_axs e_axs P (addc,(clstm,(pconsts,weight'))::tmpc) keep 
    end;


fun initialize_w_pol [] ax_weights = ax_weights
  | initialize_w_pol ((tm,name)::tms_names) ax_weights =
    let val consts = pconsts_of_term tm
    in
	initialize_w_pol tms_names (((tm,name),(consts,0.0))::ax_weights)
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

(*Whether all "simple" unit clauses should be included*)
val add_unit = ref true;

fun literals_of_term args (Const ("Trueprop",_) $ P) = literals_of_term args P
  | literals_of_term args (Const ("op |",_) $ P $ Q) = 
    literals_of_term (literals_of_term args P) Q
  | literals_of_term args P = P::args;

fun is_ground t = (term_vars t = []) andalso (term_frees t = []);

fun eq_clause_type (P,Q) = 
    if ((is_ground P) orelse (is_ground Q)) then Unit_geq else Other;

fun unit_clause_type (Const ("op =",_) $ P $ Q) = eq_clause_type (P,Q)
  | unit_clause_type _ = Unit_neq;

fun clause_type tm = 
    case literals_of_term [] tm of
        [lit] => unit_clause_type lit
      | _ => Other;

(*** constants with types ***)

datatype const_typ =  CTVar | CType of string * const_typ list

fun uni_type (CType(con1,args1)) (CType(con2,args2)) = con1=con2 andalso uni_types args1 args2
  | uni_type (CType _) CTVar = true
  | uni_type CTVar CTVar = true
  | uni_type CTVar _ = false
and uni_types [] [] = true
  | uni_types (a1::as1) (a2::as2) = uni_type a1 a2 andalso uni_types as1 as2;


fun uni_constants (c1,ctp1) (c2,ctp2) = (c1 = c2) andalso (uni_types ctp1 ctp2);

fun uni_mem _ [] = false
  | uni_mem (c,c_typ) ((c1,c_typ1)::ctyps) =
      uni_constants (c1,c_typ1) (c,c_typ) orelse uni_mem (c,c_typ) ctyps;

fun const_typ_of (Type (c,typs)) = CType (c,map const_typ_of typs) 
  | const_typ_of (TFree(_,_)) = CTVar
  | const_typ_of (TVar(_,_)) = CTVar


fun const_w_typ thy (c,typ) = 
    let val tvars = Sign.const_typargs thy (c,typ)
    in (c, map const_typ_of tvars) end;

fun add_term_consts_typs_rm thy ncs (Const(c, typ)) cs =
      if (c mem ncs) then cs else (const_w_typ thy (c,typ) ins cs)
  | add_term_consts_typs_rm thy ncs (t $ u) cs =
      add_term_consts_typs_rm thy ncs  t (add_term_consts_typs_rm thy ncs u cs)
  | add_term_consts_typs_rm thy ncs (Abs(_,_,t)) cs = add_term_consts_typs_rm thy ncs t cs
  | add_term_consts_typs_rm thy ncs _ cs = cs;

fun term_consts_typs_rm thy ncs t = add_term_consts_typs_rm thy ncs t [];

fun consts_typs_of_term thy = term_consts_typs_rm thy standard_consts;

fun get_goal_consts_typs thy cs = foldl (op union) [] (map (consts_typs_of_term thy) cs)

fun lookup_or_zero (c,tab) =
    case Symtab.lookup tab c of
        NONE => 0
      | SOME n => n

fun count_term_consts (Const(c,_), tab) =
      Symtab.update (c, 1 + lookup_or_zero (c,tab)) tab
  | count_term_consts (t $ u, tab) =
      count_term_consts (t, count_term_consts (u, tab))
  | count_term_consts (Abs(_,_,t), tab) = count_term_consts (t, tab)
  | count_term_consts (_, tab) = tab;

fun count_axiom_consts ((tm,_), tab) = count_term_consts (tm, tab);


(******** filter clauses ********)

(*The default ignores the constant-count and gives the old Strategy 3*)
val weight_fn = ref (fn x : real => 1.0);

fun add_ct_weight ctab ((c,_), w) =
  w + !weight_fn (100.0 / real (Option.valOf (Symtab.lookup ctab c)));

fun consts_typs_weight ctab =
    List.foldl (add_ct_weight ctab) 0.0;

fun clause_weight_s_3 ctab gctyps consts_typs =
    let val rel = filter (fn s => uni_mem s gctyps) consts_typs
    in
	(consts_typs_weight ctab rel) / (consts_typs_weight ctab consts_typs)
    end;

fun find_clause_weight_s_3_alt ctab consts_typs (_,(refconsts_typs,wa)) =
    wa * clause_weight_s_3 ctab refconsts_typs consts_typs;

fun relevant_clauses_ax_3 ctab rel_axs [] P (addc,tmpc) keep =
      if null addc orelse null tmpc 
      then (addc @ rel_axs @ keep, tmpc)   (*termination!*)
      else relevant_clauses_ax_3 ctab addc tmpc P ([],[]) (rel_axs @ keep)
  | relevant_clauses_ax_3 ctab rel_axs ((clstm,(consts_typs,weight))::e_axs) P (addc,tmpc) keep =
      let val weights = map (find_clause_weight_s_3_alt ctab consts_typs) rel_axs
          val weight' = List.foldl Real.max weight weights
	  val e_ax' = (clstm, (consts_typs,weight'))
      in
	if P <= weight' 
	then relevant_clauses_ax_3 ctab rel_axs e_axs P (e_ax'::addc, tmpc) keep
	else relevant_clauses_ax_3 ctab rel_axs e_axs P (addc, e_ax'::tmpc) keep
      end;

fun weight_of_axiom thy (tm,name) =
    ((tm,name), (consts_typs_of_term thy tm));

fun safe_unit_clause ((clstm,_), _) = 
      case clause_type clstm of
	  Unit_neq => true
	| Unit_geq => true
	| Other => false;

fun relevance_filter3_aux thy axioms goals = 
    let val pass = !pass_mark
	val const_tab = List.foldl count_axiom_consts Symtab.empty axioms
	val goals_consts_typs = get_goal_consts_typs thy goals
	fun relevant [] (ax,r) = (ax,r)
	  | relevant ((clstm,consts_typs)::y) (ax,r) =
	      let val weight = clause_weight_s_3 const_tab goals_consts_typs consts_typs
		  val ccc = (clstm, (consts_typs,weight))
	      in
		if pass <= weight 
		then relevant y (ccc::ax, r)
		else relevant y (ax, ccc::r)
	      end
	val (rel_clauses,nrel_clauses) =
	    relevant (map (weight_of_axiom thy) axioms) ([],[]) 
	val (ax,r) = relevant_clauses_ax_3 const_tab rel_clauses nrel_clauses pass ([],[]) []
    in
	if !add_unit then (filter safe_unit_clause r) @ ax 
	else ax
    end;

fun relevance_filter3 thy axioms goals =
  map #1 (relevance_filter3_aux thy axioms goals);
    

(******************************************************************)
(* Generic functions for relevance filtering                      *)
(******************************************************************)

exception RELEVANCE_FILTER of string;

fun relevance_filter thy axioms goals = 
  case (!strategy) of 1 => relevance_filter1 axioms goals
		    | 2 => relevance_filter2 axioms goals
		    | 3 => relevance_filter3 thy axioms goals
		    | _ => raise RELEVANCE_FILTER("strategy doesn't exist");

end;