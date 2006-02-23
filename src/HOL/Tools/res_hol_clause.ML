(* ID: $Id$ 
   Author: Jia Meng, NICTA

FOL clauses translated from HOL formulae.  Combinators are used to represent lambda terms.

*)

structure ResHolClause =

struct


val include_combS = ref false;
val include_min_comb = ref false;

val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun init thy = (include_combS:=false;include_min_comb:=false;const_typargs := Sign.const_typargs thy);

(**********************************************************************)
(* convert a Term.term with lambdas into a Term.term with combinators *) 
(**********************************************************************)

fun is_free (Bound(a)) n = (a = n)
  | is_free (Abs(x,_,b)) n = (is_free b (n+1))
  | is_free (P $ Q) n = ((is_free P n) orelse (is_free Q n))
  | is_free _ _ = false;


exception LAM2COMB of term;

exception BND of term;

fun decre_bndVar (Bound n) = Bound (n-1)
  | decre_bndVar (P $ Q) = (decre_bndVar P) $ (decre_bndVar Q)
  | decre_bndVar t =
    case t of Const(_,_) => t
	    | Free(_,_) => t
	    | Var(_,_) => t
	    | Abs(_,_,_) => raise BND(t); (*should not occur*)


(*******************************************)
fun lam2comb (Abs(x,tp,Bound 0)) _ = 
    let val tpI = Type("fun",[tp,tp])
    in 
	include_min_comb:=true;
	Const("COMBI",tpI) 
    end
  | lam2comb (Abs(x,tp,Bound n)) Bnds = 
    let val (Bound n') = decre_bndVar (Bound n)
	val tb = List.nth(Bnds,n')
	val tK = Type("fun",[tb,Type("fun",[tp,tb])])
    in
	include_min_comb:=true;
	Const("COMBK",tK) $ (Bound n')
    end
  | lam2comb (Abs(x,t1,Const(c,t2))) _ = 
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
    in 
	include_min_comb:=true;
	Const("COMBK",tK) $ Const(c,t2) 
    end
  | lam2comb (Abs(x,t1,Free(v,t2))) _ =
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
    in
	include_min_comb:=true;
	Const("COMBK",tK) $ Free(v,t2)
    end
  | lam2comb (Abs(x,t1,Var(ind,t2))) _=
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
    in
	include_min_comb:=true;
	Const("COMBK",tK) $ Var(ind,t2)
    end
  | lam2comb (t as (Abs(x,t1,P$(Bound 0)))) Bnds =
    let val nfreeP = not(is_free P 0)
	val tr = Term.type_of1(t1::Bnds,P)
    in
	if nfreeP then (decre_bndVar P)
	else (
	      let val tI = Type("fun",[t1,t1])
		  val P' = lam2comb (Abs(x,t1,P)) Bnds
		  val tp' = Term.type_of1(Bnds,P')
		  val tS = Type("fun",[tp',Type("fun",[tI,tr])])
	      in
		  include_min_comb:=true;
		  include_combS:=true;
		  Const("COMBS",tS) $ P' $ Const("COMBI",tI)
	      end)
    end
	    
  | lam2comb (t as (Abs(x,t1,P$Q))) Bnds =
    let val (nfreeP,nfreeQ) = (not(is_free P 0),not(is_free Q 0))
	val tpq = Term.type_of1(t1::Bnds, P$Q) 
    in
	if(nfreeP andalso nfreeQ) then (
	    let val tK = Type("fun",[tpq,Type("fun",[t1,tpq])])
		val PQ' = decre_bndVar(P $ Q)
	    in 
		include_min_comb:=true;
		Const("COMBK",tK) $ PQ'
	    end)
	else (
	      if nfreeP then (
			       let val Q' = lam2comb (Abs(x,t1,Q)) Bnds
				   val P' = decre_bndVar P
				   val tp = Term.type_of1(Bnds,P')
				   val tq' = Term.type_of1(Bnds, Q')
				   val tB = Type("fun",[tp,Type("fun",[tq',Type("fun",[t1,tpq])])])
			       in
				   include_min_comb:=true;
				   Const("COMBB",tB) $ P' $ Q' 
			       end)
	      else (
		    if nfreeQ then (
				    let val P' = lam2comb (Abs(x,t1,P)) Bnds
					val Q' = decre_bndVar Q
					val tq = Term.type_of1(Bnds,Q')
					val tp' = Term.type_of1(Bnds, P')
					val tC = Type("fun",[tp',Type("fun",[tq,Type("fun",[t1,tpq])])])
				    in
					include_min_comb:=true;
					Const("COMBC",tC) $ P' $ Q'
				    end)
		    else(
			 let val P' = lam2comb (Abs(x,t1,P)) Bnds
			     val Q' = lam2comb (Abs(x,t1,Q)) Bnds
			     val tp' = Term.type_of1(Bnds,P')
			     val tq' = Term.type_of1(Bnds,Q')
			     val tS = Type("fun",[tp',Type("fun",[tq',Type("fun",[t1,tpq])])])
			 in
			     include_min_comb:=true;
			     include_combS:=true;
			     Const("COMBS",tS) $ P' $ Q'
			 end)))
    end
  | lam2comb (t as (Abs(x,t1,_))) _ = raise LAM2COMB (t);

	     

(*********************)

fun to_comb (Abs(x,tp,b)) Bnds =
    let val b' = to_comb b (tp::Bnds)
    in lam2comb (Abs(x,tp,b')) Bnds end
  | to_comb (P $ Q) Bnds = ((to_comb P Bnds) $ (to_comb Q Bnds))
  | to_comb t _ = t;
 
    
fun comb_of t = to_comb t [];


(* print a term containing combinators, used for debugging *)
exception TERM_COMB of term;

fun string_of_term (Const(c,t)) = c
  | string_of_term (Free(v,t)) = v
  | string_of_term (Var((x,n),t)) =
    let val xn = x ^ "_" ^ (string_of_int n)
    in xn end
  | string_of_term (P $ Q) =
    let val P' = string_of_term P
	val Q' = string_of_term Q
    in
	"(" ^ P' ^ " " ^ Q' ^ ")" end
  | string_of_term t =  raise TERM_COMB (t);



(******************************************************)
(* data types for typed combinator expressions        *)
(******************************************************)

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
		  | Bool of combterm
		  | Equal of combterm * combterm;
datatype literal = Literal of polarity * combterm;



datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    kind: kind,
		    literals: literal list,
		    ctypes_sorts: (ctyp_var * csort) list, 
                    ctvar_type_literals: ctype_literal list, 
                    ctfree_type_literals: ctype_literal list};



fun string_of_kind (Clause cls) = name_of_kind (#kind cls);
fun get_axiomName (Clause cls) = #axiom_name cls;
fun get_clause_id (Clause cls) = #clause_id cls;

fun get_literals (c as Clause(cls)) = #literals cls;



exception TERM_ORD of string

fun term_ord (CombVar(_,_),CombVar(_,_)) = EQUAL
  | term_ord (CombVar(_,_),_) = LESS
  | term_ord (CombFree(_,_),CombVar(_,_)) = GREATER
  | term_ord (CombFree(f1,tp1),CombFree(f2,tp2)) = 
    let val ord1 = string_ord(f1,f2)
    in
	case ord1 of EQUAL => ResClause.types_ord ([tp1],[tp2])
		   | _ => ord1
    end
  | term_ord (CombFree(_,_),_) = LESS
  | term_ord (CombConst(_,_,_),CombVar(_,_)) = GREATER
  | term_ord (CombConst(_,_,_),CombFree(_,_)) = GREATER
  | term_ord (CombConst(c1,tp1,_),CombConst(c2,tp2,_)) = 
    let val ord1 = string_ord (c1,c2)
    in
	case ord1 of EQUAL => ResClause.types_ord ([tp1],[tp2])
		   | _ => ord1
    end
  | term_ord (CombConst(_,_,_),_) = LESS
  | term_ord (CombApp(_,_,_),Bool(_)) = raise TERM_ORD("bool")
  | term_ord (CombApp(_,_,_),Equal(_,_)) = LESS
  | term_ord (CombApp(f1,arg1,tp1),CombApp(f2,arg2,tp2)) =
    let val ord1 = term_ord (f1,f2)
	val ord2 = case ord1 of EQUAL => term_ord (arg1,arg2)
			      | _ => ord1
    in
	case ord2 of EQUAL => ResClause.types_ord ([tp1],[tp2])
		   | _ => ord2
    end
  | term_ord (CombApp(_,_,_),_) = GREATER
  | term_ord (Bool(_),_) = raise TERM_ORD("bool")
  | term_ord (Equal(t1,t2),Equal(t3,t4)) = ResClause.list_ord term_ord ([t1,t2],[t3,t4])
  | term_ord (Equal(_,_),_) = GREATER;

fun predicate_ord (Equal(_,_),Bool(_)) = LESS
  | predicate_ord (Equal(t1,t2),Equal(t3,t4)) = 
    ResClause.list_ord term_ord ([t1,t2],[t3,t4])
  | predicate_ord (Bool(_),Equal(_,_)) = GREATER
  | predicate_ord (Bool(t1),Bool(t2)) = term_ord (t1,t2)


fun literal_ord (Literal(false,_),Literal(true,_)) = LESS
  | literal_ord (Literal(true,_),Literal(false,_)) = GREATER
  | literal_ord (Literal(_,pred1),Literal(_,pred2)) = predicate_ord(pred1,pred2);

fun sort_lits lits = sort literal_ord lits;

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



fun make_clause(clause_id,axiom_name,kind,literals,ctypes_sorts,ctvar_type_literals,ctfree_type_literals) =
    if forall isFalse literals
    then error "Problem too trivial for resolution (empty clause)"
    else
	Clause {clause_id = clause_id, axiom_name = axiom_name, kind = kind,
		literals = literals, ctypes_sorts = ctypes_sorts, 
		ctvar_type_literals = ctvar_type_literals,
		ctfree_type_literals = ctfree_type_literals};

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

fun comb_typ ("COMBI",t) = 
    let val t' = domain_type t
    in
	[simp_type_of t']
    end
  | comb_typ ("COMBK",t) = 
    let val a = domain_type t
	val b = domain_type (range_type t)
    in
	map simp_type_of [a,b]
    end
  | comb_typ ("COMBS",t) = 
    let val t' = domain_type t
	val a = domain_type t'
	val b = domain_type (range_type t')
	val c = range_type (range_type t')
    in 
	map simp_type_of [a,b,c]
    end
  | comb_typ ("COMBB",t) = 
    let val ab = domain_type t
	val ca = domain_type (range_type t)
	val a = domain_type ab
	val b = range_type ab
	val c = domain_type ca
    in
	map simp_type_of [a,b,c]
    end
  | comb_typ ("COMBC",t) =
    let val t1 = domain_type t
	val a = domain_type t1
	val b = domain_type (range_type t1)
	val c = range_type (range_type t1)
    in
	map simp_type_of [a,b,c]
    end;

fun const_type_of ("COMBI",t) = 
    let val (tp,ts) = type_of t
	val I_var = comb_typ ("COMBI",t)
    in
	(tp,ts,I_var)
    end
  | const_type_of ("COMBK",t) =
    let val (tp,ts) = type_of t
	val K_var = comb_typ ("COMBK",t)
    in
	(tp,ts,K_var)
    end
  | const_type_of ("COMBS",t) =
    let val (tp,ts) = type_of t
	val S_var = comb_typ ("COMBS",t)
    in
	(tp,ts,S_var)
    end
  | const_type_of ("COMBB",t) =
    let val (tp,ts) = type_of t
	val B_var = comb_typ ("COMBB",t)
    in
	(tp,ts,B_var)
    end
  | const_type_of ("COMBC",t) =
    let val (tp,ts) = type_of t
	val C_var = comb_typ ("COMBC",t)
    in
	(tp,ts,C_var)
    end
  | const_type_of (c,t) =
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
  | combterm_of (Const("op =",T) $ P $ Q) = (*FIXME: allow equal between bools?*)
    let val (P',tsP) = combterm_of P        
	val (Q',tsQ) = combterm_of Q
    in
	(Equal(P',Q'),tsP union tsQ)
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


(* making axiom and conjecture clauses *)
fun make_axiom_clause term (ax_name,cls_id) =
    let val term' = comb_of term
	val (lits,ctypes_sorts) = literals_of_term term'
	val lits' = sort_lits lits
	val (ctvar_lits,ctfree_lits) = ResClause.add_typs_aux ctypes_sorts
    in
	make_clause(cls_id,ax_name,Axiom,
		    lits',ctypes_sorts,ctvar_lits,ctfree_lits)
    end;


fun make_conjecture_clause n t =
    let val t' = comb_of t
	val (lits,ctypes_sorts) = literals_of_term t'
	val (ctvar_lits,ctfree_lits) = ResClause.add_typs_aux ctypes_sorts
    in
	make_clause(n,"conjecture",Conjecture,lits,ctypes_sorts,ctvar_lits,ctfree_lits)
    end;



fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (t::ts) =
    make_conjecture_clause n t :: make_conjecture_clauses_aux (n+1) ts;

val make_conjecture_clauses = make_conjecture_clauses_aux 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(**********************************************************************)

val type_wrapper = "typeinfo";

datatype type_level = T_FULL | T_PARTIAL | T_CONST | T_NONE;

val typ_level = ref T_FULL;

fun full_types () = (typ_level:=T_FULL);
fun partial_types () = (typ_level:=T_PARTIAL);
fun const_types_only () = (typ_level:=T_CONST);
fun no_types () = (typ_level:=T_NONE);


fun find_typ_level () = !typ_level;

fun wrap_type (c,t) = 
    case !typ_level of T_FULL => type_wrapper ^ (ResClause.paren_pack [c,t])
		     | _ => c;
    

val bool_tp = ResClause.make_fixed_type_const "bool";

val app_str = "hAPP";

val bool_str = "hBOOL";

exception STRING_OF_COMBTERM of int;

(* convert literals of clauses into strings *)
fun string_of_combterm1_aux _ (CombConst(c,tp,_)) = 
    let val tp' = string_of_ctyp tp
    in
	(wrap_type (c,tp'),tp')
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
	val r =	case !typ_level of T_FULL => type_wrapper ^  (ResClause.paren_pack [(app_str ^ (ResClause.paren_pack [s1,s2])),tp'])
				 | T_PARTIAL => app_str ^ (ResClause.paren_pack [s1,s2,tp1])
				 | T_NONE => app_str ^ (ResClause.paren_pack [s1,s2])
				 | T_CONST => raise STRING_OF_COMBTERM (1) (*should not happen, if happened may be a bug*)
    in	(r,tp')

    end
  | string_of_combterm1_aux is_pred (Bool(t)) = 
    let val (t',_) = string_of_combterm1_aux false t
	val r = if is_pred then bool_str ^ (ResClause.paren_pack [t'])
		else t'
    in
	(r,bool_tp)
    end
  | string_of_combterm1_aux _ (Equal(t1,t2)) =
    let val (s1,_) = string_of_combterm1_aux false t1
	val (s2,_) = string_of_combterm1_aux false t2
    in
	("equal" ^ (ResClause.paren_pack [s1,s2]),bool_tp) 
    end;

fun string_of_combterm1 is_pred term = fst (string_of_combterm1_aux is_pred term);

fun string_of_combterm2 _ (CombConst(c,tp,tvars)) = 
    let val tvars' = map string_of_ctyp tvars
    in
	c ^ (ResClause.paren_pack tvars')
    end
  | string_of_combterm2 _ (CombFree(v,tp)) = v
  | string_of_combterm2 _ (CombVar(v,tp)) = v
  | string_of_combterm2 is_pred (CombApp(t1,t2,tp)) =
    let val s1 = string_of_combterm2 is_pred t1
	val s2 = string_of_combterm2 is_pred t2
    in
	app_str ^ (ResClause.paren_pack [s1,s2])
    end
  | string_of_combterm2 is_pred (Bool(t)) = 
    let val t' = string_of_combterm2 false t
    in
	if is_pred then bool_str ^ (ResClause.paren_pack [t'])
	else t'
    end
  | string_of_combterm2 _ (Equal(t1,t2)) =
    let val s1 = string_of_combterm2 false t1
	val s2 = string_of_combterm2 false t2
    in
	("equal" ^ (ResClause.paren_pack [s1,s2])) 
    end;



fun string_of_combterm is_pred term = 
    case !typ_level of T_CONST => string_of_combterm2 is_pred term
		     | _ => string_of_combterm1 is_pred term;


fun string_of_clausename (cls_id,ax_name) = 
    ResClause.clause_prefix ^ ResClause.ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);


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
			     | _ => (map ResClause.tptp_of_typeLit (#ctvar_type_literals cls)) 
	val ctfree_lits = 
	    case !typ_level of T_NONE => []
			     | _ => (map ResClause.tptp_of_typeLit (#ctfree_type_literals cls)) 
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



(**********************************************************************)
(* clause equalities and hashing functions                            *)
(**********************************************************************)


fun combterm_eq (CombConst(c1,tp1,tps1),CombConst(c2,tp2,tps2)) vtvars =
    let val (eq1,vtvars1) = if c1 = c2 then ResClause.types_eq (tps1,tps2) vtvars
			    else (false,vtvars)
    in
	(eq1,vtvars1)
    end
  | combterm_eq (CombConst(_,_,_),_) vtvars = (false,vtvars)
  | combterm_eq (CombFree(a1,tp1),CombFree(a2,tp2)) vtvars = 
    if a1 = a2 then ResClause.types_eq ([tp1],[tp2]) vtvars
    else (false,vtvars)
  | combterm_eq (CombFree(_,_),_) vtvars = (false,vtvars)
  | combterm_eq (CombVar(v1,tp1),CombVar(v2,tp2)) (vars,tvars) = 
    (case ResClause.check_var_pairs(v1,v2) vars of 0 => ResClause.types_eq ([tp1],[tp2]) ((v1,v2)::vars,tvars)
						 | 1 => ResClause.types_eq ([tp1],[tp2]) (vars,tvars)
						 | 2 => (false,(vars,tvars)))
  | combterm_eq (CombVar(_,_),_) vtvars = (false,vtvars)
  | combterm_eq (CombApp(f1,arg1,tp1),CombApp(f2,arg2,tp2)) vtvars =
    let val (eq1,vtvars1) = combterm_eq (f1,f2) vtvars
	val (eq2,vtvars2) = if eq1 then combterm_eq (arg1,arg2) vtvars1
			    else (eq1,vtvars1)
    in
	if eq2 then ResClause.types_eq ([tp1],[tp2]) vtvars2
	else (eq2,vtvars2)
    end
  | combterm_eq (CombApp(_,_,_),_) vtvars = (false,vtvars)
  | combterm_eq (Bool(t1),Bool(t2)) vtvars = combterm_eq (t1,t2) vtvars
  | combterm_eq (Bool(_),_) vtvars = (false,vtvars)
  | combterm_eq (Equal(t1,t2),Equal(t3,t4)) vtvars =
    let val (eq1,vtvars1) = combterm_eq (t1,t3) vtvars
    in
	if eq1 then combterm_eq (t2,t4) vtvars1
	else (eq1,vtvars1)
    end
  | combterm_eq (Equal(t1,t2),_) vtvars = (false,vtvars);

fun lit_eq (Literal(pol1,pred1),Literal(pol2,pred2)) vtvars =
    if (pol1 = pol2) then combterm_eq (pred1,pred2) vtvars
    else (false,vtvars);

fun lits_eq ([],[]) vtvars = (true,vtvars)
  | lits_eq (l1::ls1,l2::ls2) vtvars = 
    let val (eq1,vtvars1) = lit_eq (l1,l2) vtvars
    in
	if eq1 then lits_eq (ls1,ls2) vtvars1
	else (false,vtvars1)
    end;

fun clause_eq (cls1,cls2) =
    let val lits1 = get_literals cls1
	val lits2 = get_literals cls2
    in
	length lits1 = length lits2 andalso #1 (lits_eq (lits1,lits2) ([],[]))
    end;

val xor_words = List.foldl Word.xorb 0w0;

fun hash_combterm (CombVar(_,_),w) = w
  | hash_combterm (CombFree(f,_),w) = Polyhash.hashw_string(f,w)
  | hash_combterm (CombConst(c,tp,tps),w) = Polyhash.hashw_string(c,w)
  | hash_combterm (CombApp(f,arg,tp),w) = hash_combterm (arg, hash_combterm (f,w))
  | hash_combterm (Bool(t),w) = hash_combterm (t,w)
  | hash_combterm (Equal(t1,t2),w) = 
    List.foldl hash_combterm (Polyhash.hashw_string ("equal",w)) [t1,t2]

fun hash_literal (Literal(true,pred)) = hash_combterm(pred,0w0)
  | hash_literal (Literal(false,pred)) = Word.notb(hash_combterm(pred,0w0));

fun hash_clause clause = xor_words (map hash_literal (get_literals clause));

end