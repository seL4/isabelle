(* ID: $Id$ 
   Author: Jia Meng, NICTA

FOL clauses translated from HOL formulae.  Combinators are used to represent lambda terms.
*)

structure ResHolClause =

struct

(* theorems for combinators and function extensionality *)
val ext = thm "HOL.ext";
val comb_I = thm "ATP_Linkup.COMBI_def";
val comb_K = thm "ATP_Linkup.COMBK_def";
val comb_B = thm "ATP_Linkup.COMBB_def";
val comb_C = thm "ATP_Linkup.COMBC_def";
val comb_S = thm "ATP_Linkup.COMBS_def";
val comb_B' = thm "ATP_Linkup.COMBB'_def";
val comb_C' = thm "ATP_Linkup.COMBC'_def";
val comb_S' = thm "ATP_Linkup.COMBS'_def";
val fequal_imp_equal = thm "ATP_Linkup.fequal_imp_equal";
val equal_imp_fequal = thm "ATP_Linkup.equal_imp_fequal";

(*A flag to set if we use the Turner optimizations. Currently FALSE, as the 5 standard
  combinators appear to work best.*)
val use_Turner = ref false;

val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun init thy = (const_typargs := Sign.const_typargs thy);

(**********************************************************************)
(* convert a Term.term with lambdas into a Term.term with combinators *) 
(**********************************************************************)

fun is_free (Bound(a)) n = (a = n)
  | is_free (Abs(x,_,b)) n = (is_free b (n+1))
  | is_free (P $ Q) n = ((is_free P n) orelse (is_free Q n))
  | is_free _ _ = false;


(*******************************************)
fun mk_compact_comb (tm as (Const("ATP_Linkup.COMBB",_)$p) $ (Const("ATP_Linkup.COMBB",_)$q$r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ = Term.type_of1(bnds,tm)
	  val typ_B' = [tp_p,tp_q,tp_r] ---> typ
      in
	  Const("ATP_Linkup.COMBB'",typ_B') $ p $ q $ r
      end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBC",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ = Term.type_of1(bnds,tm)
	  val typ_C' = [tp_p,tp_q,tp_r] ---> typ
      in
	  Const("ATP_Linkup.COMBC'",typ_C') $ p $ q $ r
      end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBS",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) bnds =
      let val tp_p = Term.type_of1(bnds,p)
	  val tp_q = Term.type_of1(bnds,q)
	  val tp_r = Term.type_of1(bnds,r)
	  val typ = Term.type_of1(bnds,tm)
	  val typ_S' = [tp_p,tp_q,tp_r] ---> typ
      in
	  Const("ATP_Linkup.COMBS'",typ_S') $ p $ q $ r
      end
  | mk_compact_comb tm _ = tm;

fun compact_comb t bnds = 
  if !use_Turner then mk_compact_comb t bnds else t;

fun lam2comb (Abs(x,tp,Bound 0)) _ = Const("ATP_Linkup.COMBI",tp-->tp) 
  | lam2comb (Abs(x,tp,Bound n)) bnds = 
      let val tb = List.nth(bnds,n-1)
      in
	  Const("ATP_Linkup.COMBK", [tb,tp] ---> tb) $ Bound (n-1)
      end
  | lam2comb (Abs(x,t1,Const(c,t2))) _ = Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Const(c,t2) 
  | lam2comb (Abs(x,t1,Free(v,t2))) _ = Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Free(v,t2)
  | lam2comb (Abs(x,t1,Var(ind,t2))) _ = Const("ATP_Linkup.COMBK", [t2,t1] ---> t2) $ Var(ind,t2)
  | lam2comb (t as (Abs(x,t1,P$(Bound 0)))) bnds =
      if is_free P 0 then 
	  let val tI = [t1] ---> t1
	      val P' = lam2comb (Abs(x,t1,P)) bnds
	      val tp' = Term.type_of1(bnds,P')
	      val tr = Term.type_of1(t1::bnds,P)
	      val tS = [tp',tI] ---> tr
	  in
	      compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ 
	                     Const("ATP_Linkup.COMBI",tI)) bnds
	  end
      else incr_boundvars ~1 P
  | lam2comb (t as (Abs(x,t1,P$Q))) bnds =
      let val nfreeP = not(is_free P 0)
	  and nfreeQ = not(is_free Q 0)
	  val tpq = Term.type_of1(t1::bnds, P$Q) 
      in
	  if nfreeP andalso nfreeQ 
	  then 
	    let val tK = [tpq,t1] ---> tpq
		val PQ' = incr_boundvars ~1 (P $ Q)
	    in 
		Const("ATP_Linkup.COMBK",tK) $ PQ'
	    end
	  else if nfreeP then 
	    let val Q' = lam2comb (Abs(x,t1,Q)) bnds
		val P' = incr_boundvars ~1 P
		val tp = Term.type_of1(bnds,P')
		val tq' = Term.type_of1(bnds, Q')
		val tB = [tp,tq',t1] ---> tpq
	    in
		compact_comb (Const("ATP_Linkup.COMBB",tB) $ P' $ Q') bnds 
	    end
	  else if nfreeQ then 
	    let val P' = lam2comb (Abs(x,t1,P)) bnds
		val Q' = incr_boundvars ~1 Q
		val tq = Term.type_of1(bnds,Q')
		val tp' = Term.type_of1(bnds, P')
		val tC = [tp',tq,t1] ---> tpq
	    in
		compact_comb (Const("ATP_Linkup.COMBC",tC) $ P' $ Q') bnds
	    end
          else
	    let val P' = lam2comb (Abs(x,t1,P)) bnds
		val Q' = lam2comb (Abs(x,t1,Q)) bnds 
		val tp' = Term.type_of1(bnds,P')
		val tq' = Term.type_of1(bnds,Q')
		val tS = [tp',tq',t1] ---> tpq
	    in
		compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ Q') bnds
	    end
      end
  | lam2comb (t as (Abs(x,t1,_))) _ = raise ResClause.CLAUSE("HOL CLAUSE",t);

(*********************)

fun to_comb (Abs(x,tp,b)) bnds =
      lam2comb (Abs(x, tp, to_comb b (tp::bnds))) bnds 
  | to_comb (P $ Q) bnds = (to_comb P bnds) $ (to_comb Q bnds)
  | to_comb t _ = t;


(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

datatype type_level = T_FULL | T_PARTIAL | T_CONST | T_NONE;

val typ_level = ref T_CONST;

fun full_types () = (typ_level:=T_FULL);
fun partial_types () = (typ_level:=T_PARTIAL);
fun const_types_only () = (typ_level:=T_CONST);
fun no_types () = (typ_level:=T_NONE);

fun find_typ_level () = !typ_level;

type axiom_name = string;
type polarity = bool;
type clause_id = int;

datatype combterm = CombConst of string * ResClause.fol_type * ResClause.fol_type list
		  | CombFree of string * ResClause.fol_type
		  | CombVar of string * ResClause.fol_type
		  | CombApp of combterm * combterm * ResClause.fol_type
		  
datatype literal = Literal of polarity * combterm;

datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    th: thm,
		    kind: ResClause.kind,
		    literals: literal list,
		    ctypes_sorts: (ResClause.typ_var * Term.sort) list, 
                    ctvar_type_literals: ResClause.type_literal list, 
                    ctfree_type_literals: ResClause.type_literal list};


(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

fun isFalse (Literal(pol, CombConst(c,_,_))) =
      (pol andalso c = "c_False") orelse
      (not pol andalso c = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol, CombConst(c,_,_))) =
      (pol andalso c = "c_True") orelse
      (not pol andalso c = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  

fun type_of (Type (a, Ts)) =
      let val (folTypes,ts) = types_of Ts
	  val t = ResClause.make_fixed_type_const a
      in
	  (ResClause.mk_fol_type("Comp",t,folTypes), ts)
      end
  | type_of (tp as (TFree(a,s))) =
      let val t = ResClause.make_fixed_type_var a
      in
	  (ResClause.mk_fol_type("Fixed",t,[]), [ResClause.mk_typ_var_sort tp])
      end
  | type_of (tp as (TVar(v,s))) =
      let val t = ResClause.make_schematic_type_var v
      in
	  (ResClause.mk_fol_type("Var",t,[]), [ResClause.mk_typ_var_sort tp])
      end
and types_of Ts =
      let val foltyps_ts = map type_of Ts
	  val (folTyps,ts) = ListPair.unzip foltyps_ts
      in
	  (folTyps, ResClause.union_all ts)
      end;

(* same as above, but no gathering of sort information *)
fun simp_type_of (Type (a, Ts)) = 
      let val typs = map simp_type_of Ts
	  val t = ResClause.make_fixed_type_const a
      in
	  ResClause.mk_fol_type("Comp",t,typs)
      end
  | simp_type_of (TFree (a,s)) = ResClause.mk_fol_type("Fixed",ResClause.make_fixed_type_var a,[])
  | simp_type_of (TVar (v,s)) = ResClause.mk_fol_type("Var",ResClause.make_schematic_type_var v,[]);


fun const_type_of (c,t) =
    let val (tp,ts) = type_of t
	val tvars = !const_typargs(c,t)
    in
	(tp, ts, map simp_type_of tvars)
    end;

(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of (Const(c,t)) =
      let val (tp,ts,tvar_list) = const_type_of (c,t)
	  val c' = CombConst(ResClause.make_fixed_const c,tp,tvar_list)
      in
	  (c',ts)
      end
  | combterm_of (Free(v,t)) =
      let val (tp,ts) = type_of t
	  val v' = if ResClause.isMeta v then CombVar(ResClause.make_schematic_var(v,0),tp)
		   else CombFree(ResClause.make_fixed_var v,tp)
      in
	  (v',ts)
      end
  | combterm_of (Var(v,t)) =
      let val (tp,ts) = type_of t
	  val v' = CombVar(ResClause.make_schematic_var v,tp)
      in
	  (v',ts)
      end
  | combterm_of (t as (P $ Q)) =
      let val (P',tsP) = combterm_of P
	  val (Q',tsQ) = combterm_of Q
	  val tp = Term.type_of t
	  val t' = CombApp(P',Q', simp_type_of tp)
      in
	  (t',tsP union tsQ)
      end;

fun predicate_of ((Const("Not",_) $ P), polarity) = predicate_of (P, not polarity)
  | predicate_of (t,polarity) = (combterm_of t, polarity);

fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 args (Const("op |",_) $ P $ Q) = 
      literals_of_term1 (literals_of_term1 args P) Q
  | literals_of_term1 (lits,ts) P =
      let val ((pred,ts'),pol) = predicate_of (P,true)
      in
	  (Literal(pol,pred)::lits, ts union ts')
      end;

fun literals_of_term P = literals_of_term1 ([],[]) P;

(* making axiom and conjecture clauses *)
fun make_clause(clause_id,axiom_name,kind,th) =
    let val (lits,ctypes_sorts) = literals_of_term (to_comb (prop_of th) [])
	val (ctvar_lits,ctfree_lits) = ResClause.add_typs_aux ctypes_sorts
    in
	if forall isFalse lits
	then error "Problem too trivial for resolution (empty clause)"
	else
	    Clause {clause_id = clause_id, axiom_name = axiom_name, th = th, kind = kind,
		    literals = lits, ctypes_sorts = ctypes_sorts, 
		    ctvar_type_literals = ctvar_lits,
		    ctfree_type_literals = ctfree_lits}
    end;


fun add_axiom_clause ((th,(name,id)), pairs) =
  let val cls = make_clause(id, name, ResClause.Axiom, th)
  in
      if isTaut cls then pairs else (name,cls)::pairs
  end;

val make_axiom_clauses = foldl add_axiom_clause [];

fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (th::ths) =
      make_clause(n,"conjecture", ResClause.Conjecture, th) ::
      make_conjecture_clauses_aux (n+1) ths;

val make_conjecture_clauses = make_conjecture_clauses_aux 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
(**********************************************************************)

val type_wrapper = "typeinfo";

fun wrap_type (c,tp) = case !typ_level of
	T_FULL => type_wrapper ^ ResClause.paren_pack [c, ResClause.string_of_fol_type tp]
      | _ => c;
    

val bool_tp = ResClause.make_fixed_type_const "bool";

val app_str = "hAPP";

val bool_str = "hBOOL";

fun type_of_combterm (CombConst(c,tp,_)) = tp
  | type_of_combterm (CombFree(v,tp)) = tp
  | type_of_combterm (CombVar(v,tp)) = tp
  | type_of_combterm (CombApp(t1,t2,tp)) = tp;

fun string_of_combterm1 (CombConst(c,tp,_)) = 
      let val c' = if c = "equal" then "c_fequal" else c
      in  wrap_type (c',tp)  end
  | string_of_combterm1 (CombFree(v,tp)) = wrap_type (v,tp)
  | string_of_combterm1 (CombVar(v,tp)) = wrap_type (v,tp)
  | string_of_combterm1 (CombApp(t1,t2,tp)) =
      let val s1 = string_of_combterm1 t1
	  val s2 = string_of_combterm1 t2
      in
	  case !typ_level of
	      T_FULL => type_wrapper ^ 
	                ResClause.paren_pack 
	                  [app_str ^ ResClause.paren_pack [s1,s2], 
	                   ResClause.string_of_fol_type tp]
	    | T_PARTIAL => app_str ^ ResClause.paren_pack 
	                     [s1,s2, ResClause.string_of_fol_type (type_of_combterm t1)]
	    | T_NONE => app_str ^ ResClause.paren_pack [s1,s2]
	    | T_CONST => raise ERROR "string_of_combterm1"
      end;

fun string_of_combterm2 (CombConst(c,tp,tvars)) = 
      let val tvars' = map ResClause.string_of_fol_type tvars
	  val c' = if c = "equal" then "c_fequal" else c
      in
	  c' ^ ResClause.paren_pack tvars'
      end
  | string_of_combterm2 (CombFree(v,tp)) = v
  | string_of_combterm2 (CombVar(v,tp)) = v
  | string_of_combterm2 (CombApp(t1,t2,_)) =
      app_str ^ ResClause.paren_pack [string_of_combterm2 t1, string_of_combterm2 t2];

fun string_of_combterm t = 
    case !typ_level of T_CONST => string_of_combterm2 t
		           | _ => string_of_combterm1 t;
		           
fun string_of_predicate (CombApp(CombApp(CombConst("equal",_,_),t1,_),t2,_)) =
      ("equal" ^ ResClause.paren_pack [string_of_combterm t1, string_of_combterm t2])
  | string_of_predicate t = 
      bool_str ^ ResClause.paren_pack [string_of_combterm t]

fun string_of_clausename (cls_id,ax_name) = 
    ResClause.clause_prefix ^ ResClause.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


(*** tptp format ***)

fun tptp_of_equality pol (t1,t2) =
  let val eqop = if pol then " = " else " != "
  in  string_of_combterm t1 ^ eqop ^ string_of_combterm t2  end;

fun tptp_literal (Literal(pol, CombApp(CombApp(CombConst("equal",_,_),t1,_),t2,_))) = 
      tptp_of_equality pol (t1,t2)
  | tptp_literal (Literal(pol,pred)) = 
      ResClause.tptp_sign pol (string_of_predicate pred);
 
fun tptp_type_lits (Clause cls) = 
    let val lits = map tptp_literal (#literals cls)
	val ctvar_lits_strs =
	    case !typ_level of T_NONE => []
	      | _ => map ResClause.tptp_of_typeLit (#ctvar_type_literals cls)
	val ctfree_lits = 
	    case !typ_level of T_NONE => []
	      | _ => map ResClause.tptp_of_typeLit (#ctfree_type_literals cls)
    in
	(ctvar_lits_strs @ lits, ctfree_lits)
    end; 
    
    
fun clause2tptp (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
    let val (lits,ctfree_lits) = tptp_type_lits cls
	val cls_str = ResClause.gen_tptp_cls(clause_id,axiom_name,kind,lits)
    in
	(cls_str,ctfree_lits)
    end;


(*** dfg format ***)

fun dfg_literal (Literal(pol,pred)) = ResClause.dfg_sign pol (string_of_predicate pred);

fun dfg_clause_aux (Clause{literals, ctypes_sorts, ...}) = 
  let val lits = map dfg_literal literals
      val (tvar_lits,tfree_lits) = ResClause.add_typs_aux ctypes_sorts
      val tvar_lits_strs = 
	  case !typ_level of T_NONE => [] 
	      | _ => map ResClause.dfg_of_typeLit tvar_lits
      val tfree_lits =
          case !typ_level of T_NONE => []
	      | _ => map ResClause.dfg_of_typeLit tfree_lits 
  in
      (tvar_lits_strs @ lits, tfree_lits)
  end; 

fun get_uvars (CombConst(_,_,_)) vars = vars
  | get_uvars (CombFree(_,_)) vars = vars
  | get_uvars (CombVar(v,tp)) vars = (v::vars)
  | get_uvars (CombApp(P,Q,tp)) vars = get_uvars P (get_uvars Q vars);

fun get_uvars_l (Literal(_,c)) = get_uvars c [];

fun dfg_vars (Clause {literals,...}) = ResClause.union_all (map get_uvars_l literals);
 
fun clause2dfg (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
        val vars = dfg_vars cls
        val tvars = ResClause.get_tvar_strs ctypes_sorts
	val knd = ResClause.name_of_kind kind
	val lits_str = commas lits
	val cls_str = ResClause.gen_dfg_cls(clause_id, axiom_name, knd, lits_str, tvars@vars) 
    in (cls_str, tfree_lits) end;


fun init_funcs_tab funcs = 
    let val funcs1 = case !typ_level of T_PARTIAL => Symtab.update ("hAPP",3) funcs
				      | _ => Symtab.update ("hAPP",2) funcs
    in
	Symtab.update ("typeinfo",2) funcs1
    end;


fun add_funcs (CombConst(c,_,tvars),funcs) =
      if c = "equal" then foldl ResClause.add_foltype_funcs funcs tvars
      else
	(case !typ_level of
	     T_CONST => foldl ResClause.add_foltype_funcs (Symtab.update(c,length tvars) funcs) tvars
           | _ => foldl ResClause.add_foltype_funcs (Symtab.update(c,0) funcs) tvars)
  | add_funcs (CombFree(v,ctp),funcs) = ResClause.add_foltype_funcs (ctp,Symtab.update (v,0) funcs) 
  | add_funcs (CombVar(_,ctp),funcs) = ResClause.add_foltype_funcs (ctp,funcs)
  | add_funcs (CombApp(P,Q,_),funcs) = add_funcs(P,add_funcs (Q,funcs));

fun add_literal_funcs (Literal(_,c), funcs) = add_funcs (c,funcs);

fun add_clause_funcs (Clause {literals, ...}, funcs) =
    foldl add_literal_funcs funcs literals
    handle Symtab.DUP a => raise ERROR ("function " ^ a ^ " has multiple arities")

fun funcs_of_clauses clauses arity_clauses =
    Symtab.dest (foldl ResClause.add_arityClause_funcs 
                       (foldl add_clause_funcs (init_funcs_tab Symtab.empty) clauses)
                       arity_clauses)

fun add_clause_preds (Clause {ctypes_sorts, ...}, preds) =
  foldl ResClause.add_type_sort_preds preds ctypes_sorts
  handle Symtab.DUP a => raise ERROR ("predicate " ^ a ^ " has multiple arities")

(*Higher-order clauses have only the predicates hBOOL and type classes.*)
fun preds_of_clauses clauses clsrel_clauses arity_clauses = 
    Symtab.dest
	(foldl ResClause.add_classrelClause_preds 
	       (foldl ResClause.add_arityClause_preds
		      (Symtab.update ("hBOOL",1) 
		        (foldl add_clause_preds Symtab.empty clauses))
		      arity_clauses)
	       clsrel_clauses)



(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)


val init_counters =
    Symtab.make [("c_COMBI", 0), ("c_COMBK", 0),
		 ("c_COMBB", 0), ("c_COMBC", 0),
		 ("c_COMBS", 0), ("c_COMBB_e", 0),
		 ("c_COMBC_e", 0), ("c_COMBS_e", 0)];
                
fun count_combterm (CombConst(c,tp,_), ct) = 
     (case Symtab.lookup ct c of NONE => ct  (*no counter*)
                               | SOME n => Symtab.update (c,n+1) ct)
  | count_combterm (CombFree(v,tp), ct) = ct
  | count_combterm (CombVar(v,tp), ct) = ct
  | count_combterm (CombApp(t1,t2,tp), ct) = count_combterm(t1, count_combterm(t2, ct));

fun count_literal (Literal(_,t), ct) = count_combterm(t,ct);

fun count_clause (Clause{literals,...}, ct) = foldl count_literal ct literals;

fun count_user_clause user_lemmas (Clause{axiom_name,literals,...}, ct) = 
  if axiom_name mem_string user_lemmas then foldl count_literal ct literals
  else ct;

val cnf_helper_thms = ResAxioms.cnf_rules_pairs o (map ResAxioms.pairname)

fun get_helper_clauses ct =
    let fun needed c = valOf (Symtab.lookup ct c) > 0
        val IK = if needed "c_COMBI" orelse needed "c_COMBK" 
                 then (Output.debug "Include combinator I K"; cnf_helper_thms [comb_I,comb_K]) 
                 else []
	val BC = if needed "c_COMBB" orelse needed "c_COMBC" 
	         then (Output.debug "Include combinator B C"; cnf_helper_thms [comb_B,comb_C]) 
	         else []
	val S = if needed "c_COMBS" 
	        then (Output.debug "Include combinator S"; cnf_helper_thms [comb_S]) 
	        else []
	val B'C' = if needed "c_COMBB_e" orelse needed "c_COMBC_e" 
	           then (Output.debug "Include combinator B' C'"; cnf_helper_thms [comb_B', comb_C']) 
	           else []
	val S' = if needed "c_COMBS_e" 
	         then (Output.debug "Include combinator S'"; cnf_helper_thms [comb_S']) 
	         else []
	val other = cnf_helper_thms [ext,fequal_imp_equal,equal_imp_fequal]
    in
	make_axiom_clauses (other @ IK @ BC @ S @ B'C' @ S')
    end

(* tptp format *)
						  
(* write TPTP format to a single file *)
fun tptp_write_file thms filename (axclauses,classrel_clauses,arity_clauses) user_lemmas =
    let val conjectures = make_conjecture_clauses thms
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses)
	val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp conjectures)
	val tfree_clss = map ResClause.tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
	val out = TextIO.openOut filename
	val ct = foldl (count_user_clause user_lemmas) 
	            (foldl count_clause init_counters conjectures)
	            axclauses'
	val helper_clauses = map #2 (get_helper_clauses ct)
    in
	List.app (curry TextIO.output out o #1 o clause2tptp) axclauses';
	ResClause.writeln_strs out tfree_clss;
	ResClause.writeln_strs out tptp_clss;
	List.app (curry TextIO.output out o ResClause.tptp_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o ResClause.tptp_arity_clause) arity_clauses;
	List.app (curry TextIO.output out o #1 o clause2tptp) helper_clauses;
	TextIO.closeOut out;
	clnames
    end;



(* dfg format *)

fun dfg_write_file  thms filename (axclauses,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug ("Preparing to write the DFG file " ^ filename) 
	val conjectures = make_conjecture_clauses thms
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses)
	val (dfg_clss,tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
	and probname = Path.implode (Path.base (Path.explode filename))
	val axstrs = map (#1 o clause2dfg) axclauses'
	val tfree_clss = map ResClause.dfg_tfree_clause (ResClause.union_all tfree_litss)
	val out = TextIO.openOut filename
	val ct = foldl (count_user_clause user_lemmas) 
	            (foldl count_clause init_counters conjectures)
	            axclauses'
	val helper_clauses = map #2 (get_helper_clauses ct)
	val helper_clauses_strs = map (#1 o clause2dfg) helper_clauses
	val funcs = funcs_of_clauses (helper_clauses @ conjectures @ axclauses') arity_clauses
	and preds = preds_of_clauses axclauses' classrel_clauses arity_clauses
    in
	TextIO.output (out, ResClause.string_of_start probname); 
	TextIO.output (out, ResClause.string_of_descrip probname); 
	TextIO.output (out, ResClause.string_of_symbols (ResClause.string_of_funcs funcs) (ResClause.string_of_preds preds)); 
	TextIO.output (out, "list_of_clauses(axioms,cnf).\n");
	ResClause.writeln_strs out axstrs;
	List.app (curry TextIO.output out o ResClause.dfg_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o ResClause.dfg_arity_clause) arity_clauses;
	ResClause.writeln_strs out helper_clauses_strs;
	TextIO.output (out, "end_of_list.\n\nlist_of_clauses(conjectures,cnf).\n");
	ResClause.writeln_strs out tfree_clss;
	ResClause.writeln_strs out dfg_clss;
	TextIO.output (out, "end_of_list.\n\n");
	(*VarWeight=3 helps the HO problems, probably by counteracting the presence of hAPP*)
	TextIO.output (out, "list_of_settings(SPASS).\n{*\nset_flag(VarWeight,3).\n*}\nend_of_list.\n\n");
	TextIO.output (out, "end_problem.\n");
	TextIO.closeOut out;
	clnames
    end;

end
