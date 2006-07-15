(* ID: $Id$ 
   Author: Jia Meng, NICTA

FOL clauses translated from HOL formulae.  Combinators are used to represent lambda terms.

*)

structure ResHolClause =

struct


val include_combS = ref false;
val include_min_comb = ref false;

fun in_min_comb count_comb = if count_comb then include_min_comb:=true else ();
 
fun in_combS count_comb = if count_comb then include_combS:=true else (); 

val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun init thy = (include_combS:=false; include_min_comb:=false;
                const_typargs := Sign.const_typargs thy);

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
fun lam2comb (Abs(x,tp,Bound 0)) _ count_comb = 
    let val tpI = Type("fun",[tp,tp])
	val _ = in_min_comb count_comb
    in 
	Const("COMBI",tpI) 
    end
  | lam2comb (Abs(x,tp,Bound n)) Bnds count_comb = 
    let val (Bound n') = decre_bndVar (Bound n)
	val tb = List.nth(Bnds,n')
	val tK = Type("fun",[tb,Type("fun",[tp,tb])])
	val _ = in_min_comb count_comb 
    in
	Const("COMBK",tK) $ (Bound n')
    end
  | lam2comb (Abs(x,t1,Const(c,t2))) _ count_comb = 
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
	val _ = in_min_comb count_comb 
    in 
	Const("COMBK",tK) $ Const(c,t2) 
    end
  | lam2comb (Abs(x,t1,Free(v,t2))) _ count_comb =
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
	val _ = in_min_comb count_comb
    in
	Const("COMBK",tK) $ Free(v,t2)
    end
  | lam2comb (Abs(x,t1,Var(ind,t2))) _ count_comb =
    let val tK = Type("fun",[t2,Type("fun",[t1,t2])])
	val _ = in_min_comb count_comb 
    in
	Const("COMBK",tK) $ Var(ind,t2)
    end
  | lam2comb (t as (Abs(x,t1,P$(Bound 0)))) Bnds count_comb =
    let val nfreeP = not(is_free P 0)
	val tr = Term.type_of1(t1::Bnds,P)
    in
	if nfreeP then (decre_bndVar P)
	else (
	      let val tI = Type("fun",[t1,t1])
		  val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
		  val tp' = Term.type_of1(Bnds,P')
		  val tS = Type("fun",[tp',Type("fun",[tI,tr])])
		  val _ = in_min_comb count_comb
		  val _ = in_combS count_comb
	      in
		  Const("COMBS",tS) $ P' $ Const("COMBI",tI)
	      end)
    end
	    
  | lam2comb (t as (Abs(x,t1,P$Q))) Bnds count_comb =
    let val (nfreeP,nfreeQ) = (not(is_free P 0),not(is_free Q 0))
	val tpq = Term.type_of1(t1::Bnds, P$Q) 
    in
	if(nfreeP andalso nfreeQ) then (
	    let val tK = Type("fun",[tpq,Type("fun",[t1,tpq])])
		val PQ' = decre_bndVar(P $ Q)
		val _ = in_min_comb count_comb
	    in 
		Const("COMBK",tK) $ PQ'
	    end)
	else (
	      if nfreeP then (
			       let val Q' = lam2comb (Abs(x,t1,Q)) Bnds count_comb
				   val P' = decre_bndVar P
				   val tp = Term.type_of1(Bnds,P')
				   val tq' = Term.type_of1(Bnds, Q')
				   val tB = Type("fun",[tp,Type("fun",[tq',Type("fun",[t1,tpq])])])
				   val _ = in_min_comb count_comb
			       in
				   Const("COMBB",tB) $ P' $ Q' 
			       end)
	      else (
		    if nfreeQ then (
				    let val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
					val Q' = decre_bndVar Q
					val tq = Term.type_of1(Bnds,Q')
					val tp' = Term.type_of1(Bnds, P')
					val tC = Type("fun",[tp',Type("fun",[tq,Type("fun",[t1,tpq])])])
					val _ = in_min_comb count_comb
				    in
					Const("COMBC",tC) $ P' $ Q'
				    end)
		    else(
			 let val P' = lam2comb (Abs(x,t1,P)) Bnds count_comb
			     val Q' = lam2comb (Abs(x,t1,Q)) Bnds count_comb 
			     val tp' = Term.type_of1(Bnds,P')
			     val tq' = Term.type_of1(Bnds,Q')
			     val tS = Type("fun",[tp',Type("fun",[tq',Type("fun",[t1,tpq])])])
			     val _ = in_min_comb count_comb
			     val _ = in_combS count_comb
			 in
			     Const("COMBS",tS) $ P' $ Q'
			 end)))
    end
  | lam2comb (t as (Abs(x,t1,_))) _ _ = raise LAM2COMB (t);

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

(* forbid a clause that contains hBOOL(V) *)
fun too_general [] = false
  | too_general (lit::lits) = 
    case lit of Literal(_,Bool(CombVar(_,_))) => true
	      | _ => too_general lits;


(* making axiom and conjecture clauses *)
exception TOO_GENERAL
fun make_clause(clause_id,axiom_name,kind,thm,is_user) =
    let val term = prop_of thm
	val term' = comb_of term is_user
	val (lits,ctypes_sorts) = literals_of_term term'
	val (ctvar_lits,ctfree_lits) = ResClause.add_typs_aux ctypes_sorts
    in
	if forall isFalse lits
	then error "Problem too trivial for resolution (empty clause)"
	else if too_general lits then raise TOO_GENERAL
	else
	    Clause {clause_id = clause_id, axiom_name = axiom_name, th = thm, kind = kind,
		    literals = lits, ctypes_sorts = ctypes_sorts, 
		    ctvar_type_literals = ctvar_lits,
		    ctfree_type_literals = ctfree_lits}
    end;


fun make_axiom_clause thm (ax_name,cls_id,is_user) = make_clause(cls_id,ax_name,Axiom,thm,is_user);
 
fun make_axiom_clauses [] user_lemmas = []
  | make_axiom_clauses ((thm,(name,id))::thms) user_lemmas =
    let val is_user = name mem user_lemmas
	val cls = SOME (make_axiom_clause thm (name,id,is_user)) handle TOO_GENERAL => NONE
	val clss = make_axiom_clauses thms user_lemmas
    in
	case cls of NONE => clss
		  | SOME(cls') => if isTaut cls' then clss else (name,cls')::clss
    end;


fun make_conjecture_clause n thm = make_clause(n,"conjecture",Conjecture,thm,true);
 

fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (t::ts) =
    make_conjecture_clause n t :: make_conjecture_clauses_aux (n+1) ts;

val make_conjecture_clauses = make_conjecture_clauses_aux 0;


(**********************************************************************)
(* convert clause into ATP specific formats:                          *)
(* TPTP used by Vampire and E                                         *)
(* DFG used by SPASS                                                  *)
(**********************************************************************)

val type_wrapper = "typeinfo";

datatype type_level = T_FULL | T_PARTIAL | T_CONST | T_NONE;

val typ_level = ref T_CONST;

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
	val c' = if c = "equal" then "fequal" else c
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
	val r =	case !typ_level of T_FULL => type_wrapper ^  (ResClause.paren_pack [(app_str ^ (ResClause.paren_pack [s1,s2])),tp'])
				 | T_PARTIAL => app_str ^ (ResClause.paren_pack [s1,s2,tp1])
				 | T_NONE => app_str ^ (ResClause.paren_pack [s1,s2])
				 | T_CONST => raise STRING_OF_COMBTERM (1) (*should not happen, if happened may be a bug*)
    in	(r,tp')

    end
  | string_of_combterm1_aux is_pred (Bool(CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))) =
    if is_pred then 
	let val (s1,_) = string_of_combterm1_aux false t1
	    val (s2,_) = string_of_combterm1_aux false t2
	in
	    ("equal" ^ (ResClause.paren_pack [s1,s2]),bool_tp)
	end
    else
	let val (t,_) = string_of_combterm1_aux false (CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))
	in
	    (t,bool_tp)
	end
  | string_of_combterm1_aux is_pred (Bool(t)) = 
    let val (t',_) = string_of_combterm1_aux false t
	val r = if is_pred then bool_str ^ (ResClause.paren_pack [t'])
		else t'
    in
	(r,bool_tp)
    end;

fun string_of_combterm1 is_pred term = fst (string_of_combterm1_aux is_pred term);

fun string_of_combterm2 _ (CombConst(c,tp,tvars)) = 
    let val tvars' = map string_of_ctyp tvars
	val c' = if c = "equal" then "fequal" else c
    in
	c' ^ (ResClause.paren_pack tvars')
    end
  | string_of_combterm2 _ (CombFree(v,tp)) = v
  | string_of_combterm2 _ (CombVar(v,tp)) = v
  | string_of_combterm2 is_pred (CombApp(t1,t2,tp)) =
    let val s1 = string_of_combterm2 is_pred t1
	val s2 = string_of_combterm2 is_pred t2
    in
	app_str ^ (ResClause.paren_pack [s1,s2])
    end
  | string_of_combterm2 is_pred (Bool(CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))) =
    if is_pred then 
	let val s1 = string_of_combterm2 false t1
	    val s2 = string_of_combterm2 false t2
	in
	    ("equal" ^ (ResClause.paren_pack [s1,s2]))
	end
    else
	string_of_combterm2 false (CombApp(CombApp(CombConst("equal",tp,tps),t1,tp1),t2,tp2))
 
  | string_of_combterm2 is_pred (Bool(t)) = 
    let val t' = string_of_combterm2 false t
    in
	if is_pred then bool_str ^ (ResClause.paren_pack [t'])
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


fun init_combs (comb,funcs) =
    case !typ_level of T_CONST => 
		       (case comb of "c_COMBK" => Symtab.update (comb,2) funcs
				   | "c_COMBS" => Symtab.update (comb,3) funcs
				   | "c_COMBI" => Symtab.update (comb,1) funcs
				   | "c_COMBB" => Symtab.update (comb,3) funcs
				   | "c_COMBC" => Symtab.update (comb,3) funcs
				   | _ => funcs)
		     | _ => Symtab.update (comb,0) funcs;

fun init_funcs_tab funcs = 
    let val tp = !typ_level
	val funcs0 = foldl init_combs funcs ["c_COMBK","c_COMBS","c_COMBI","c_COMBB","c_COMBC"]
	val funcs1 = case tp of T_PARTIAL => Symtab.update ("hAPP",3) funcs0
				      | _ => Symtab.update ("hAPP",2) funcs0
	val funcs2 = case tp of T_FULL => Symtab.update ("typeinfo",2) funcs1
				      | _ => funcs1
    in
	case tp of T_CONST => Symtab.update ("fequal",1) (Symtab.update ("hEXTENT",2) funcs2)
			 | _ => Symtab.update ("fequal",0) (Symtab.update ("hEXTENT",0) funcs2)
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

(* tptp format *)

fun read_in fs = map (File.read o File.unpack_platform_path) fs; 

fun get_helper_clauses_tptp () =
  let val tlevel = case !typ_level of 
		       T_FULL => (Output.debug "Fully-typed HOL"; 
				  "~~/src/HOL/Tools/atp-inputs/full_")
		     | T_PARTIAL => (Output.debug "Partially-typed HOL"; 
				     "~~/src/HOL/Tools/atp-inputs/par_")
		     | T_CONST => (Output.debug "Const-only-typed HOL"; 
				   "~~/src/HOL/Tools/atp-inputs/const_")
		     | T_NONE => (Output.debug "Untyped HOL"; 
				  "~~/src/HOL/Tools/atp-inputs/u_")
      val helpers = if !include_combS 
                    then (Output.debug "Include combinator S"; 
                          ["helper1.tptp","comb_inclS.tptp"]) 
                    else if !include_min_comb 
                    then (Output.debug "Include min combinators"; 
                          ["helper1.tptp","comb_noS.tptp"])
		    else (Output.debug "No combinator is used"; ["helper1.tptp"])
      val t_helpers = map (curry (op ^) tlevel) helpers
  in
      read_in t_helpers
  end;
	
						  
(* write TPTP format to a single file *)
(* when "get_helper_clauses" is called, "include_combS" and "include_min_comb" should have correct values already *)
fun tptp_write_file thms filename (axclauses,classrel_clauses,arity_clauses) user_lemmas=
    let val clss = make_conjecture_clauses thms
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses user_lemmas)
	val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp clss)
	val tfree_clss = map ResClause.tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
	val out = TextIO.openOut filename
	val helper_clauses = get_helper_clauses_tptp ()
    in
	List.app (curry TextIO.output out o #1 o clause2tptp) axclauses';
	ResClause.writeln_strs out tfree_clss;
	ResClause.writeln_strs out tptp_clss;
	List.app (curry TextIO.output out o ResClause.tptp_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o ResClause.tptp_arity_clause) arity_clauses;
	List.app (curry TextIO.output out) helper_clauses;
	TextIO.closeOut out;
	clnames
    end;


(* dfg format *)
fun get_helper_clauses_dfg () = 
 let val tlevel = case !typ_level of 
                      T_FULL => (Output.debug "Fully-typed HOL"; 
                                 "~~/src/HOL/Tools/atp-inputs/full_")
		    | T_PARTIAL => (Output.debug "Partially-typed HOL"; 
		                    "~~/src/HOL/Tools/atp-inputs/par_")
		    | T_CONST => (Output.debug "Const-only-typed HOL"; 
		                  "~~/src/HOL/Tools/atp-inputs/const_")
		    | T_NONE => (Output.debug "Untyped HOL"; 
		                 "~~/src/HOL/Tools/atp-inputs/u_")
     val helpers = if !include_combS 
                   then (Output.debug "Include combinator S"; 
                         ["helper1.dfg","comb_inclS.dfg"]) else
		   if !include_min_comb 
		   then (Output.debug "Include min combinators"; 
		         ["helper1.dfg","comb_noS.dfg"])
		   else (Output.debug "No combinator is used"; ["helper1.dfg"])
     val t_helpers = map (curry (op ^) tlevel) helpers
 in
     read_in t_helpers
 end;


fun dfg_write_file  thms filename (axclauses,classrel_clauses,arity_clauses) user_lemmas =
    let val _ = Output.debug ("Preparing to write the DFG file " ^ filename) 
	val conjectures = make_conjecture_clauses thms
        val (clnames,axclauses') = ListPair.unzip (make_axiom_clauses axclauses user_lemmas)
	val (dfg_clss,tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
	val clss = conjectures @ axclauses'
	val funcs = funcs_of_clauses clss arity_clauses
	and preds = preds_of classrel_clauses arity_clauses
	and probname = Path.pack (Path.base (Path.unpack filename))
	val (axstrs,_) =  ListPair.unzip (map clause2dfg axclauses')
	val tfree_clss = map ResClause.dfg_tfree_clause (ResClause.union_all tfree_litss)
	val out = TextIO.openOut filename
	val helper_clauses = get_helper_clauses_dfg ()
    in
	TextIO.output (out, ResClause.string_of_start probname); 
	TextIO.output (out, ResClause.string_of_descrip probname); 
	TextIO.output (out, ResClause.string_of_symbols (ResClause.string_of_funcs funcs) (ResClause.string_of_preds preds)); 
	TextIO.output (out, "list_of_clauses(axioms,cnf).\n");
	ResClause.writeln_strs out axstrs;
	List.app (curry TextIO.output out o ResClause.dfg_classrelClause) classrel_clauses;
	List.app (curry TextIO.output out o ResClause.dfg_arity_clause) arity_clauses;
	ResClause.writeln_strs out helper_clauses;
	TextIO.output (out, "end_of_list.\n\nlist_of_clauses(conjectures,cnf).\n");
	ResClause.writeln_strs out tfree_clss;
	ResClause.writeln_strs out dfg_clss;
	TextIO.output (out, "end_of_list.\n\nend_problem.\n");
	TextIO.closeOut out;
	clnames
    end;

end