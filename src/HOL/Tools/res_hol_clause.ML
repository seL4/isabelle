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

(*FIXME: these refs should probaby replaced by code to count the combinators in the 
  translated form of the term.*)
val combI_count = ref 0;
val combK_count = ref 0;
val combB_count = ref 0;
val combC_count = ref 0;
val combS_count = ref 0;

val combB'_count = ref 0;
val combC'_count = ref 0;
val combS'_count = ref 0; 


fun increI count_comb =  if count_comb then combI_count := !combI_count + 1 else ();
fun increK count_comb =  if count_comb then combK_count := !combK_count + 1 else ();
fun increB count_comb =  if count_comb then combB_count := !combB_count + 1 else ();
fun increC count_comb =  if count_comb then combC_count := !combC_count + 1 else ();
fun increS count_comb =  if count_comb then combS_count := !combS_count + 1 else (); 
fun increB' count_comb =  if count_comb then combB'_count := !combB'_count + 1 else (); 
fun increC' count_comb =  if count_comb then combC'_count := !combC'_count + 1 else ();
fun increS' count_comb =  if count_comb then combS'_count := !combS'_count + 1 else (); 


exception DECRE_COMB of string;
fun decreB count_comb n = 
  if count_comb then 
    if !combB_count >= n then combB_count := !combB_count - n else raise DECRE_COMB "COMBB"
  else ();

fun decreC count_comb n =
  if count_comb then 
    if !combC_count >= n then combC_count := !combC_count - n else raise DECRE_COMB "COMBC"
  else ();

fun decreS count_comb n = 
  if count_comb then 
    if !combS_count >= n then combS_count := !combS_count - n else raise DECRE_COMB "COMBS"
  else ();

val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun init thy = (combI_count:=0; combK_count:=0;combB_count:=0;combC_count:=0;combS_count:=0;combB'_count:=0;combC'_count:=0;combS'_count:=0;
                const_typargs := Sign.const_typargs thy);

(**********************************************************************)
(* convert a Term.term with lambdas into a Term.term with combinators *) 
(**********************************************************************)

fun is_free (Bound(a)) n = (a = n)
  | is_free (Abs(x,_,b)) n = (is_free b (n+1))
  | is_free (P $ Q) n = ((is_free P n) orelse (is_free Q n))
  | is_free _ _ = false;


(*******************************************)
fun mk_compact_comb (tm as (Const("ATP_Linkup.COMBB",_)$p) $ (Const("ATP_Linkup.COMBB",_)$q$r)) Bnds count_comb =
    let val tp_p = Term.type_of1(Bnds,p)
	val tp_q = Term.type_of1(Bnds,q)
	val tp_r = Term.type_of1(Bnds,r)
	val typ = Term.type_of1(Bnds,tm)
	val typ_B' = [tp_p,tp_q,tp_r] ---> typ
	val _ = increB' count_comb
	val _ = decreB count_comb 2
    in
	Const("ATP_Linkup.COMBB'",typ_B') $ p $ q $ r
    end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBC",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) Bnds count_comb =
    let val tp_p = Term.type_of1(Bnds,p)
	val tp_q = Term.type_of1(Bnds,q)
	val tp_r = Term.type_of1(Bnds,r)
	val typ = Term.type_of1(Bnds,tm)
	val typ_C' = [tp_p,tp_q,tp_r] ---> typ
	val _ = increC' count_comb
	val _ = decreC count_comb 1
	val _ = decreB count_comb 1
    in
	Const("ATP_Linkup.COMBC'",typ_C') $ p $ q $ r
    end
  | mk_compact_comb (tm as (Const("ATP_Linkup.COMBS",_) $ (Const("ATP_Linkup.COMBB",_)$p$q) $ r)) Bnds count_comb =
    let val tp_p = Term.type_of1(Bnds,p)
	val tp_q = Term.type_of1(Bnds,q)
	val tp_r = Term.type_of1(Bnds,r)
	val typ = Term.type_of1(Bnds,tm)
	val typ_S' = [tp_p,tp_q,tp_r] ---> typ
	val _ = increS' count_comb
	val _ = decreS count_comb 1
	val _ = decreB count_comb 1
    in
	Const("ATP_Linkup.COMBS'",typ_S') $ p $ q $ r
    end
  | mk_compact_comb tm _ _ = tm;

fun compact_comb t Bnds count_comb = 
  if !use_Turner then mk_compact_comb t Bnds count_comb else t;

fun lam2comb (Abs(x,tp,Bound 0)) _ count_comb = 
      let val _ = increI count_comb
      in 
	  Const("ATP_Linkup.COMBI",tp-->tp) 
      end
  | lam2comb (Abs(x,tp,Bound n)) Bnds count_comb = 
      let val tb = List.nth(Bnds,n-1)
	  val _ = increK count_comb 
      in
	  Const("ATP_Linkup.COMBK", [tb,tp] ---> tb) $ (Bound (n-1))
      end
  | lam2comb (Abs(x,t1,Const(c,t2))) _ count_comb = 
      let val _ = increK count_comb 
      in 
	  Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Const(c,t2) 
      end
  | lam2comb (Abs(x,t1,Free(v,t2))) _ count_comb =
      let val _ = increK count_comb
      in
	  Const("ATP_Linkup.COMBK",[t2,t1] ---> t2) $ Free(v,t2)
      end
  | lam2comb (Abs(x,t1,Var(ind,t2))) _ count_comb =
      let val _ = increK count_comb 
      in
	  Const("ATP_Linkup.COMBK", [t2,t1] ---> t2) $ Var(ind,t2)
      end
  | lam2comb (t as (Abs(x,t1,P$(Bound 0)))) Bnds count_comb =
      let val tr = Term.type_of1(t1::Bnds,P)
      in
	  if not(is_free P 0) then (incr_boundvars ~1 P)
	  else 
	  let val tI = [t1] ---> t1
	      val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
	      val tp' = Term.type_of1(Bnds,P')
	      val tS = [tp',tI] ---> tr
	      val _ = increI count_comb
	      val _ = increS count_comb
	  in
	      compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ 
	                     Const("ATP_Linkup.COMBI",tI)) Bnds count_comb
	  end
      end	    
  | lam2comb (t as (Abs(x,t1,P$Q))) Bnds count_comb =
      let val nfreeP = not(is_free P 0)
	  and nfreeQ = not(is_free Q 0)
	  val tpq = Term.type_of1(t1::Bnds, P$Q) 
      in
	  if nfreeP andalso nfreeQ 
	  then 
	    let val tK = [tpq,t1] ---> tpq
		val PQ' = incr_boundvars ~1(P $ Q)
		val _ = increK count_comb
	    in 
		Const("ATP_Linkup.COMBK",tK) $ PQ'
	    end
	  else if nfreeP then 
	    let val Q' = lam2comb (Abs(x,t1,Q)) Bnds count_comb
		val P' = incr_boundvars ~1 P
		val tp = Term.type_of1(Bnds,P')
		val tq' = Term.type_of1(Bnds, Q')
		val tB = [tp,tq',t1] ---> tpq
		val _ = increB count_comb
	    in
		compact_comb (Const("ATP_Linkup.COMBB",tB) $ P' $ Q') Bnds count_comb 
	    end
	  else if nfreeQ then 
	    let val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
		val Q' = incr_boundvars ~1 Q
		val tq = Term.type_of1(Bnds,Q')
		val tp' = Term.type_of1(Bnds, P')
		val tC = [tp',tq,t1] ---> tpq
		val _ = increC count_comb
	    in
		compact_comb (Const("ATP_Linkup.COMBC",tC) $ P' $ Q') Bnds count_comb
	    end
          else
	    let val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
		val Q' = lam2comb (Abs(x,t1,Q)) Bnds count_comb 
		val tp' = Term.type_of1(Bnds,P')
		val tq' = Term.type_of1(Bnds,Q')
		val tS = [tp',tq',t1] ---> tpq
		val _ = increS count_comb
	    in
		compact_comb (Const("ATP_Linkup.COMBS",tS) $ P' $ Q') Bnds count_comb
	    end
      end
  | lam2comb (t as (Abs(x,t1,_))) _ _ = raise ResClause.CLAUSE("HOL CLAUSE",t);

(*********************)

fun to_comb (Abs(x,tp,b)) Bnds count_comb =
    let val b' = to_comb b (tp::Bnds) count_comb
    in lam2comb (Abs(x,tp,b')) Bnds count_comb end
  | to_comb (P $ Q) Bnds count_comb = ((to_comb P Bnds count_comb) $ (to_comb Q Bnds count_comb))
  | to_comb t _ _ = t;
 
   
fun comb_of t count_comb = to_comb t [] count_comb;
 
(* print a term containing combinators, used for debugging *)
exception TERM_COMB of term;

fun string_of_term (Const(c,t)) = c
  | string_of_term (Free(v,t)) = v
  | string_of_term (Var((x,n),t)) = x ^ "_" ^ (string_of_int n)
  | string_of_term (P $ Q) =
      "(" ^ string_of_term P ^ " " ^ string_of_term Q ^ ")" 
  | string_of_term t =  raise TERM_COMB (t);



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
datatype kind = Axiom | Conjecture;

fun name_of_kind Axiom = "axiom"
  | name_of_kind Conjecture = "conjecture";

type polarity = bool;
type indexname = Term.indexname;
type clause_id = int;
type csort = Term.sort;
type ctyp = ResClause.fol_type;

val string_of_ctyp = ResClause.string_of_fol_type;

type ctyp_var = ResClause.typ_var;

type ctype_literal = ResClause.type_literal;


datatype combterm = CombConst of string * ctyp * ctyp list
		  | CombFree of string * ctyp
		  | CombVar of string * ctyp
		  | CombApp of combterm * combterm * ctyp
		  | Bool of combterm;
		  
datatype literal = Literal of polarity * combterm;

datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    th: thm,
		    kind: kind,
		    literals: literal list,
		    ctypes_sorts: (ctyp_var * csort) list, 
                    ctvar_type_literals: ctype_literal list, 
                    ctfree_type_literals: ctype_literal list};


fun string_of_kind (Clause cls) = name_of_kind (#kind cls);
fun get_axiomName (Clause cls) = #axiom_name cls;
fun get_clause_id (Clause cls) = #clause_id cls;

fun get_literals (c as Clause(cls)) = #literals cls;


(*********************************************************************)
(* convert a clause with type Term.term to a clause with type clause *)
(*********************************************************************)

fun isFalse (Literal(pol,Bool(CombConst(c,_,_)))) =
      (pol andalso c = "c_False") orelse
      (not pol andalso c = "c_True")
  | isFalse _ = false;


fun isTrue (Literal (pol,Bool(CombConst(c,_,_)))) =
      (pol andalso c = "c_True") orelse
      (not pol andalso c = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  

fun type_of (Type (a, Ts)) =
    let val (folTypes,ts) = types_of Ts
	val t = ResClause.make_fixed_type_const a
    in
	(ResClause.mk_fol_type("Comp",t,folTypes),ts)
    end
  | type_of (tp as (TFree(a,s))) =
    let val t = ResClause.make_fixed_type_var a
    in
	(ResClause.mk_fol_type("Fixed",t,[]),[ResClause.mk_typ_var_sort tp])
    end
  | type_of (tp as (TVar(v,s))) =
    let val t = ResClause.make_schematic_type_var v
    in
	(ResClause.mk_fol_type("Var",t,[]),[ResClause.mk_typ_var_sort tp])
    end

and types_of Ts =
    let val foltyps_ts = map type_of Ts
	val (folTyps,ts) = ListPair.unzip foltyps_ts
    in
	(folTyps,ResClause.union_all ts)
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
	val tvars' = map simp_type_of tvars
    in
	(tp,ts,tvars')
    end;


fun is_bool_type (Type("bool",[])) = true
  | is_bool_type _ = false;


(* convert a Term.term (with combinators) into a combterm, also accummulate sort info *)
fun combterm_of (Const(c,t)) =
    let val (tp,ts,tvar_list) = const_type_of (c,t)
	val is_bool = is_bool_type t
	val c' = CombConst(ResClause.make_fixed_const c,tp,tvar_list)
	val c'' = if is_bool then Bool(c') else c'
    in
	(c'',ts)
    end
  | combterm_of (Free(v,t)) =
    let val (tp,ts) = type_of t
	val is_bool = is_bool_type t
	val v' = if ResClause.isMeta v then CombVar(ResClause.make_schematic_var(v,0),tp)
		 else CombFree(ResClause.make_fixed_var v,tp)
	val v'' = if is_bool then Bool(v') else v'
    in
	(v'',ts)
    end
  | combterm_of (Var(v,t)) =
    let val (tp,ts) = type_of t
	val is_bool = is_bool_type t
	val v' = CombVar(ResClause.make_schematic_var v,tp)
	val v'' = if is_bool then Bool(v') else v'
    in
	(v'',ts)
    end
  | combterm_of (t as (P $ Q)) =
    let val (P',tsP) = combterm_of P
	val (Q',tsQ) = combterm_of Q
	val tp = Term.type_of t
	val tp' = simp_type_of tp
	val is_bool = is_bool_type tp
	val t' = CombApp(P',Q',tp')
	val t'' = if is_bool then Bool(t') else t'
    in
	(t'',tsP union tsQ)
    end;

fun predicate_of ((Const("Not",_) $ P), polarity) =
    predicate_of (P, not polarity)
  | predicate_of (term,polarity) = (combterm_of term,polarity);


fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 args (Const("op |",_) $ P $ Q) = 
    let val args' = literals_of_term1 args P
    in
	literals_of_term1 args' Q
    end
  | literals_of_term1 (lits,ts) P =
    let val ((pred,ts'),pol) = predicate_of (P,true)
	val lits' = Literal(pol,pred)::lits
    in
	(lits',ts union ts')
    end;


fun literals_of_term P = literals_of_term1 ([],[]) P;

fun occurs a (CombVar(b,_)) = a = b
  | occurs a (CombApp(t1,t2,_)) = (occurs a t1) orelse (occurs a t2)
  | occurs _ _ = false

fun too_general_terms (CombVar(v,_), t) = not (occurs v t)
  | too_general_terms _ = false;

fun too_general_equality (Literal(true,(Bool(CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))))) =
      too_general_terms (t1,t2) orelse too_general_terms (t2,t1)
  | too_general_equality _ = false;

(* forbid the literal hBOOL(V) *)
fun too_general_bool (Literal(_,Bool(CombVar _))) = true
  | too_general_bool _ = false;

(* making axiom and conjecture clauses *)
exception MAKE_CLAUSE
fun make_clause(clause_id,axiom_name,kind,thm,is_user) =
    let val term = prop_of thm
	val term' = comb_of term is_user
	val (lits,ctypes_sorts) = literals_of_term term'
	val (ctvar_lits,ctfree_lits) = ResClause.add_typs_aux ctypes_sorts
    in
	if forall isFalse lits
	then error "Problem too trivial for resolution (empty clause)"
	else if (!typ_level <> T_FULL) andalso kind=Axiom andalso 
	        (forall too_general_equality lits orelse exists too_general_bool lits)
	    then (Output.debug ("Omitting " ^ axiom_name ^ ": clause is too prolific"); 
	          raise MAKE_CLAUSE) 
	else
	    Clause {clause_id = clause_id, axiom_name = axiom_name, th = thm, kind = kind,
		    literals = lits, ctypes_sorts = ctypes_sorts, 
		    ctvar_type_literals = ctvar_lits,
		    ctfree_type_literals = ctfree_lits}
    end;


fun make_axiom_clause thm (ax_name,cls_id,is_user) = 
      make_clause(cls_id,ax_name,Axiom,thm,is_user);
 
fun make_axiom_clauses [] user_lemmas = []
  | make_axiom_clauses ((thm,(name,id))::thms) user_lemmas =
    let val is_user = name mem user_lemmas
	val cls = SOME (make_axiom_clause thm (name,id,is_user)) 
	          handle MAKE_CLAUSE => NONE
	val clss = make_axiom_clauses thms user_lemmas
    in
	case cls of NONE => clss
		  | SOME(cls') => if isTaut cls' then clss 
		                  else (name,cls')::clss
    end;


fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (th::ths) =
      make_clause(n,"conjecture",Conjecture,th,true) ::
      make_conjecture_clauses_aux (n+1) ths;

val make_conjecture_clauses = make_conjecture_clauses_aux 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
(**********************************************************************)

val type_wrapper = "typeinfo";

fun wrap_type (c,t) = 
    case !typ_level of T_FULL => type_wrapper ^ ResClause.paren_pack [c,t]
		     | _ => c;
    

val bool_tp = ResClause.make_fixed_type_const "bool";

val app_str = "hAPP";

val bool_str = "hBOOL";

exception STRING_OF_COMBTERM of int;

(* convert literals of clauses into strings *)
fun string_of_combterm1_aux _ (CombConst(c,tp,_)) = 
    let val tp' = string_of_ctyp tp
	val c' = if c = "equal" then "c_fequal" else c
    in
	(wrap_type (c',tp'),tp')
    end
  | string_of_combterm1_aux _ (CombFree(v,tp)) = 
    let val tp' = string_of_ctyp tp
    in
	(wrap_type (v,tp'),tp')
    end
  | string_of_combterm1_aux _ (CombVar(v,tp)) = 
    let val tp' = string_of_ctyp tp
    in
	(wrap_type (v,tp'),tp')
    end
  | string_of_combterm1_aux is_pred (CombApp(t1,t2,tp)) =
    let val (s1,tp1) = string_of_combterm1_aux is_pred t1
	val (s2,tp2) = string_of_combterm1_aux is_pred t2
	val tp' = ResClause.string_of_fol_type tp
	val r =	case !typ_level of
	            T_FULL => type_wrapper ^ ResClause.paren_pack [(app_str ^ ResClause.paren_pack [s1,s2]),tp']
		  | T_PARTIAL => app_str ^ ResClause.paren_pack [s1,s2,tp1]
		  | T_NONE => app_str ^ ResClause.paren_pack [s1,s2]
		  | T_CONST => raise STRING_OF_COMBTERM 1 (*should not happen, if happened may be a bug*)
    in	(r,tp')   end
  | string_of_combterm1_aux is_pred (Bool(CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))) =
    if is_pred then 
	let val (s1,_) = string_of_combterm1_aux false t1
	    val (s2,_) = string_of_combterm1_aux false t2
	in
	    ("equal" ^ ResClause.paren_pack [s1,s2], bool_tp)
	end
    else
	let val (t,_) = string_of_combterm1_aux false (CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))
	in
	    (t,bool_tp)
	end
  | string_of_combterm1_aux is_pred (Bool(t)) = 
    let val (t',_) = string_of_combterm1_aux false t
	val r = if is_pred then bool_str ^ ResClause.paren_pack [t']
		else t'
    in
	(r,bool_tp)
    end;

fun string_of_combterm1 is_pred term = fst (string_of_combterm1_aux is_pred term);

fun string_of_combterm2 _ (CombConst(c,tp,tvars)) = 
    let val tvars' = map string_of_ctyp tvars
	val c' = if c = "equal" then "c_fequal" else c
    in
	c' ^ ResClause.paren_pack tvars'
    end
  | string_of_combterm2 _ (CombFree(v,tp)) = v
  | string_of_combterm2 _ (CombVar(v,tp)) = v
  | string_of_combterm2 is_pred (CombApp(t1,t2,tp)) =
    let val s1 = string_of_combterm2 is_pred t1
	val s2 = string_of_combterm2 is_pred t2
    in
	app_str ^ ResClause.paren_pack [s1,s2]
    end
  | string_of_combterm2 is_pred (Bool(CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))) =
    if is_pred then 
	let val s1 = string_of_combterm2 false t1
	    val s2 = string_of_combterm2 false t2
	in
	    ("equal" ^ ResClause.paren_pack [s1,s2])
	end
    else
	string_of_combterm2 false (CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))
 
  | string_of_combterm2 is_pred (Bool(t)) = 
    let val t' = string_of_combterm2 false t
    in
	if is_pred then bool_str ^ ResClause.paren_pack [t']
	else t'
    end;

fun string_of_combterm is_pred term = 
    case !typ_level of T_CONST => string_of_combterm2 is_pred term
		     | _ => string_of_combterm1 is_pred term;

fun string_of_clausename (cls_id,ax_name) = 
    ResClause.clause_prefix ^ ResClause.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


(* tptp format *)

fun tptp_literal (Literal(pol,pred)) =
    let val pred_string = string_of_combterm true pred
	val pol_str = if pol then "++" else "--"
    in
	pol_str ^ pred_string
    end;

 
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
    
    
fun clause2tptp cls =
    let val (lits,ctfree_lits) = tptp_type_lits cls
	val cls_id = get_clause_id cls
	val ax_name = get_axiomName cls
	val knd = string_of_kind cls
	val lits_str = ResClause.bracket_pack lits
	val cls_str = ResClause.gen_tptp_cls(cls_id,ax_name,knd,lits_str)
    in
	(cls_str,ctfree_lits)
    end;


(* dfg format *)
fun dfg_literal (Literal(pol,pred)) = ResClause.dfg_sign pol (string_of_combterm true pred);

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
  | get_uvars (CombApp(P,Q,tp)) vars = get_uvars P (get_uvars Q vars)
  | get_uvars (Bool(c)) vars = get_uvars c vars;


fun get_uvars_l (Literal(_,c)) = get_uvars c [];

fun dfg_vars (Clause {literals,...}) = ResClause.union_all (map get_uvars_l literals);
 
fun clause2dfg (cls as Clause{axiom_name,clause_id,kind,ctypes_sorts,...}) =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
        val vars = dfg_vars cls
        val tvars = ResClause.get_tvar_strs ctypes_sorts
	val knd = name_of_kind kind
	val lits_str = commas lits
	val cls_str = ResClause.gen_dfg_cls(clause_id, axiom_name, knd, lits_str, tvars@vars) 
    in (cls_str, tfree_lits) end;


fun init_funcs_tab funcs = 
    let val tp = !typ_level
	val funcs1 = case tp of T_PARTIAL => Symtab.update ("hAPP",3) funcs
				      | _ => Symtab.update ("hAPP",2) funcs
	val funcs2 = case tp of T_FULL => Symtab.update ("typeinfo",2) funcs1
				      | _ => funcs1
    in
	funcs2
    end;


fun add_funcs (CombConst(c,_,tvars),funcs) =
    if c = "equal" then foldl ResClause.add_foltype_funcs funcs tvars
    else
	(case !typ_level of T_CONST => foldl ResClause.add_foltype_funcs (Symtab.update(c,length tvars) funcs) tvars
			  | _ => foldl ResClause.add_foltype_funcs (Symtab.update(c,0) funcs) tvars)
  | add_funcs (CombFree(v,ctp),funcs) = ResClause.add_foltype_funcs (ctp,Symtab.update (v,0) funcs) 
  | add_funcs (CombVar(_,ctp),funcs) = ResClause.add_foltype_funcs (ctp,funcs)
  | add_funcs (CombApp(P,Q,_),funcs) = add_funcs(P,add_funcs (Q,funcs))
  | add_funcs (Bool(t),funcs) = add_funcs (t,funcs);


fun add_literal_funcs (Literal(_,c), funcs) = add_funcs (c,funcs);

fun add_clause_funcs (Clause {literals, ...}, funcs) =
    foldl add_literal_funcs funcs literals
    handle Symtab.DUP a => raise ERROR ("function " ^ a ^ " has multiple arities")

fun funcs_of_clauses clauses arity_clauses =
    Symtab.dest (foldl ResClause.add_arityClause_funcs 
                       (foldl add_clause_funcs (init_funcs_tab Symtab.empty) clauses)
                       arity_clauses)

fun preds_of clsrel_clauses arity_clauses = 
    Symtab.dest
	(foldl ResClause.add_classrelClause_preds 
	       (foldl ResClause.add_arityClause_preds
		      (Symtab.update ("hBOOL",1) Symtab.empty)
		      arity_clauses)
	       clsrel_clauses)


(**********************************************************************)
(* write clauses to files                                             *)
(**********************************************************************)

val cnf_helper_thms = ResAxioms.cnf_rules_pairs o (map ResAxioms.pairname)

(*Simulate the result of conversion to CNF*)
fun pretend_cnf s = (thm s, (s,0));

(*These theorems allow the proof of P=Q from P-->Q and Q-->P, so they are necessary for
  completeness. Unfortunately, they are very prolific, causing greatly increased runtimes.
  They also lead to many unsound proofs. Thus it is well that the "exists too_general_bool"
  test deletes them except with the full-typed translation.*)
val iff_thms = [pretend_cnf "ATP_Linkup.iff_positive", 
                pretend_cnf "ATP_Linkup.iff_negative"];

fun get_helper_clauses () =
    let val IK = if !combI_count > 0 orelse !combK_count > 0 
                 then (Output.debug "Include combinator I K"; cnf_helper_thms [comb_I,comb_K]) 
                 else []
	val BC = if !combB_count > 0 orelse !combC_count > 0 
	         then (Output.debug "Include combinator B C"; cnf_helper_thms [comb_B,comb_C]) 
	         else []
	val S = if !combS_count > 0 
	        then (Output.debug "Include combinator S"; cnf_helper_thms [comb_S]) 
	        else []
	val B'C' = if !combB'_count > 0 orelse !combC'_count > 0 
	           then (Output.debug "Include combinator B' C'"; cnf_helper_thms [comb_B', comb_C']) 
	           else []
	val S' = if !combS'_count > 0 
	         then (Output.debug "Include combinator S'"; cnf_helper_thms [comb_S']) 
	         else []
	val other = cnf_helper_thms [ext,fequal_imp_equal,equal_imp_fequal]
    in
	make_axiom_clauses (iff_thms @ other @ IK @ BC @ S @ B'C' @ S') []
    end


(* tptp format *)
						  
(* write TPTP format to a single file *)
(* when "get_helper_clauses" is called, "include_combS" and "include_min_comb" should have correct values already *)
fun tptp_write_file thms filename (axclauses,classrel_clauses,arity_clauses) user_lemmas=
    let val clss = make_conjecture_clauses thms
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses user_lemmas)
	val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp clss)
	val tfree_clss = map ResClause.tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
	val out = TextIO.openOut filename
	val helper_clauses = (#2 o ListPair.unzip o get_helper_clauses) ()
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
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses user_lemmas)
	val (dfg_clss,tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
	and probname = Path.pack (Path.base (Path.unpack filename))
	val (axstrs,_) =  ListPair.unzip (map clause2dfg axclauses')
	val tfree_clss = map ResClause.dfg_tfree_clause (ResClause.union_all tfree_litss)
	val out = TextIO.openOut filename
	val helper_clauses = (#2 o ListPair.unzip o get_helper_clauses) ()
	val helper_clauses_strs = (#1 o ListPair.unzip o (map clause2dfg)) helper_clauses
	val funcs = funcs_of_clauses (helper_clauses @ conjectures @ axclauses') arity_clauses
	and preds = preds_of classrel_clauses arity_clauses
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
