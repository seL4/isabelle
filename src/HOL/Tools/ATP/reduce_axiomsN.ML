(* Authors: Jia Meng, NICTA and Lawrence C Paulson, Cambridge University Computer Laboratory
   ID: $Id$
   Filtering strategies *)

structure ReduceAxiomsN =
struct

val pass_mark = ref 0.6;
val reduction_factor = ref 1.0;

(*Whether all "simple" unit clauses should be included*)
val add_unit = ref false;
val unit_pass_mark = ref 0.0;


(*Including equality in this list might be expected to stop rules like subset_antisym from
  being chosen, but for some reason filtering works better with them listed.*)
val standard_consts =
  ["Trueprop","==>","all","Ex","op &","op |","Not","All","op -->",
   "op =","==","True","False"];


(*** unit clauses ***)
datatype clause_kind = Unit_neq | Unit_geq | Other


fun literals_of_term args (Const ("Trueprop",_) $ P) = literals_of_term args P
  | literals_of_term args (Const ("op |",_) $ P $ Q) = 
    literals_of_term (literals_of_term args P) Q
  | literals_of_term args P = P::args;

fun is_ground t = (term_vars t = []) andalso (term_frees t = []);

fun eq_clause_type (P,Q) = 
    if ((is_ground P) orelse (is_ground Q)) then Unit_geq else Other;

fun unit_clause_type (Const ("op =",_) $ P $ Q) = eq_clause_type (P,Q)
  | unit_clause_type _ = Unit_neq;

fun clause_kind tm = 
    case literals_of_term [] tm of
        [lit] => unit_clause_type lit
      | _ => Other;

(*** constants with types ***)

(*An abstraction of Isabelle types*)
datatype const_typ =  CTVar | CType of string * const_typ list

fun uni_type (CType(con1,args1)) (CType(con2,args2)) = con1=con2 andalso uni_types args1 args2
  | uni_type (CType _) CTVar = true
  | uni_type CTVar CTVar = true
  | uni_type CTVar _ = false
and uni_types [] [] = true
  | uni_types (a1::as1) (a2::as2) = uni_type a1 a2 andalso uni_types as1 as2;


fun uni_constants (c1,ctp1) (c2,ctp2) = (c1=c2) andalso uni_types ctp1 ctp2;

fun uni_mem _ [] = false
  | uni_mem (c,c_typ) ((c1,c_typ1)::ctyps) =
      uni_constants (c1,c_typ1) (c,c_typ) orelse uni_mem (c,c_typ) ctyps;

fun const_typ_of (Type (c,typs)) = CType (c, map const_typ_of typs) 
  | const_typ_of (TFree _) = CTVar
  | const_typ_of (TVar _) = CTVar


fun const_with_typ thy (c,typ) = 
    let val tvars = Sign.const_typargs thy (c,typ)
    in (c, map const_typ_of tvars) end
    handle TYPE _ => (c,[]);   (*Variable (locale constant): monomorphic*)   

(*Free variables are counted, as well as constants, to handle locales*)
fun add_term_consts_typs_rm thy (Const(c, typ)) cs =
      if (c mem standard_consts) then cs 
      else const_with_typ thy (c,typ) ins cs
  | add_term_consts_typs_rm thy (Free(c, typ)) cs =
      const_with_typ thy (c,typ) ins cs
  | add_term_consts_typs_rm thy (t $ u) cs =
      add_term_consts_typs_rm thy t (add_term_consts_typs_rm thy u cs)
  | add_term_consts_typs_rm thy (Abs(_,_,t)) cs = add_term_consts_typs_rm thy t cs
  | add_term_consts_typs_rm thy _ cs = cs;

fun consts_typs_of_term thy t = add_term_consts_typs_rm thy t [];

fun get_goal_consts_typs thy cs = foldl (op union) [] (map (consts_typs_of_term thy) cs)


(**** Constant / Type Frequencies ****)

local

fun cons_nr CTVar = 0
  | cons_nr (CType _) = 1;

in

fun const_typ_ord TU =
  case TU of
    (CType (a, Ts), CType (b, Us)) =>
      (case fast_string_ord(a,b) of EQUAL => dict_ord const_typ_ord (Ts,Us) | ord => ord)
  | (T, U) => int_ord (cons_nr T, cons_nr U);

end;

structure CTtab = TableFun(type key = const_typ list val ord = dict_ord const_typ_ord);

fun count_axiom_consts thy ((t,_), tab) = 
  let fun count_const (a, T, tab) =
	let val (c, cts) = const_with_typ thy (a,T)
	    val cttab = Option.getOpt (Symtab.lookup tab c, CTtab.empty)
	    val n = Option.getOpt (CTtab.lookup cttab cts, 0)
	in 
	    Symtab.update (c, CTtab.update (cts, n+1) cttab) tab
	end
      fun count_term_consts (Const(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (Free(a,T), tab) = count_const(a,T,tab)
	| count_term_consts (t $ u, tab) =
	    count_term_consts (t, count_term_consts (u, tab))
	| count_term_consts (Abs(_,_,t), tab) = count_term_consts (t, tab)
	| count_term_consts (_, tab) = tab
  in  count_term_consts (t, tab)  end;


(******** filter clauses ********)

(*The default ignores the constant-count and gives the old Strategy 3*)
val weight_fn = ref (fn x : real => 1.0);

fun const_weight ctab (c, cts) =
  let val pairs = CTtab.dest (Option.valOf (Symtab.lookup ctab c))
      fun add ((cts',m), n) = if uni_types cts cts' then m+n else n
  in  List.foldl add 0 pairs  end;

fun add_ct_weight ctab ((c,T), w) =
  w + !weight_fn (real (const_weight ctab (c,T)));

fun consts_typs_weight ctab =
    List.foldl (add_ct_weight ctab) 0.0;

(*Relevant constants are weighted according to frequency, 
  but irrelevant constants are simply counted. Otherwise, Skolem functions,
  which are rare, would harm a clause's chances of being picked.*)
fun clause_weight ctab gctyps consts_typs =
    let val rel = filter (fn s => uni_mem s gctyps) consts_typs
        val rel_weight = consts_typs_weight ctab rel
    in
	rel_weight / (rel_weight + real (length consts_typs - length rel))
    end;
    
fun relevant_clauses ctab rel_axs [] (addc,tmpc) keep =
      if null addc orelse null tmpc 
      then (addc @ rel_axs @ keep, tmpc)   (*termination!*)
      else relevant_clauses ctab addc tmpc ([],[]) (rel_axs @ keep)
  | relevant_clauses ctab rel_axs ((clstm,(consts_typs,w))::e_axs) (addc,tmpc) keep =
      let fun clause_weight_ax (_,(refconsts_typs,wa)) =
              wa * clause_weight ctab refconsts_typs consts_typs;
          val weight' = List.foldl Real.max w (map clause_weight_ax rel_axs)
	  val e_ax' = (clstm, (consts_typs,weight'))
      in
	if !pass_mark <= weight' 
	then relevant_clauses ctab rel_axs e_axs (e_ax'::addc, tmpc) keep
	else relevant_clauses ctab rel_axs e_axs (addc, e_ax'::tmpc) keep
      end;

fun pair_consts_typs_axiom thy (tm,name) =
    ((tm,name), (consts_typs_of_term thy tm));

(*Unit clauses other than non-trivial equations can be included subject to
  a separate (presumably lower) mark. *)
fun good_unit_clause ((t,_), (_,w)) = 
     !unit_pass_mark <= w andalso
     (case clause_kind t of
	  Unit_neq => true
	| Unit_geq => true
	| Other => false);
	
fun axiom_ord ((_,(_,w1)), (_,(_,w2))) = Real.compare (w2,w1);

fun showconst (c,cttab) = 
      List.app (fn n => Output.debug (Int.toString n ^ " occurrences of " ^ c))
	        (map #2 (CTtab.dest cttab))

fun show_cname (name,k) = name ^ "__" ^ Int.toString k;

fun showax ((_,cname), (_,w)) = 
    Output.debug ("Axiom " ^ show_cname cname ^ " has weight " ^ Real.toString w)
	      
fun relevance_filter_aux thy axioms goals = 
  let val const_tab = List.foldl (count_axiom_consts thy) Symtab.empty axioms
      val goals_consts_typs = get_goal_consts_typs thy goals
      fun relevant [] (ax,r) = (ax,r)
	| relevant ((clstm,consts_typs)::y) (ax,r) =
	    let val weight = clause_weight const_tab goals_consts_typs consts_typs
		val ccc = (clstm, (consts_typs,weight))
	    in
	      if !pass_mark <= weight 
	      then relevant y (ccc::ax, r)
	      else relevant y (ax, ccc::r)
	    end
      val (rel_clauses,nrel_clauses) =
	  relevant (map (pair_consts_typs_axiom thy) axioms) ([],[]) 
      val (ax,r) = relevant_clauses const_tab rel_clauses nrel_clauses ([],[]) []
      val max_filtered = floor (!reduction_factor * real (length ax))
      val ax' = Library.take(max_filtered, Library.sort axiom_ord ax)
  in
      if !Output.show_debug_msgs then
	   (List.app showconst (Symtab.dest const_tab);
	    List.app showax ax)
      else ();
      if !add_unit then (filter good_unit_clause r) @ ax'
      else ax'
  end;

fun relevance_filter thy axioms goals =
  map #1 (relevance_filter_aux thy axioms goals);
    

end;