(*  Author: Jia Meng, Cambridge University Computer Laboratory

    ID: $Id$
    Copyright 2004 University of Cambridge

ML data structure for storing/printing FOL clauses and arity clauses.
Typed equality is treated differently.
*)

(* works for writeoutclasimp on typed *)
signature RES_CLAUSE =
  sig
  val keep_types : bool ref
  val special_equal : bool ref
  val tagged : bool ref

  exception ARCLAUSE of string
  exception CLAUSE of string * term
  type arityClause 
  type classrelClause
  type clause
  val init : theory -> unit
  val make_axiom_clause : Term.term -> string * int -> clause
  val make_conjecture_clauses : term list -> clause list
  val get_axiomName : clause ->  string
  val isTaut : clause -> bool
  val num_of_clauses : clause -> int

  val clause2dfg : clause -> string * string list
  val clauses2dfg : clause list -> string -> clause list -> clause list ->
	   (string * int) list -> (string * int) list -> string
  val tfree_dfg_clause : string -> string

  val arity_clause_thy: theory -> arityClause list 
  val classrel_clauses_thy: theory -> classrelClause list 

  val tptp_arity_clause : arityClause -> string
  val tptp_classrelClause : classrelClause -> string
  val tptp_clause : clause -> string list
  val clause2tptp : clause -> string * string list
  val tfree_clause : string -> string
  val schematic_var_prefix : string
  val fixed_var_prefix : string
  val tvar_prefix : string
  val tfree_prefix : string
  val clause_prefix : string 
  val arclause_prefix : string
  val const_prefix : string
  val tconst_prefix : string 
  val class_prefix : string 

  val union_all : ''a list list -> ''a list
  val ascii_of : String.string -> String.string
  val paren_pack : string list -> string
  val bracket_pack : string list -> string
  val make_schematic_var : String.string * int -> string
  val make_fixed_var : String.string -> string
  val make_schematic_type_var : string * int -> string
  val make_fixed_type_var : string -> string
  val make_fixed_const : String.string -> string		
  val make_fixed_type_const : String.string -> string   
  val make_type_class : String.string -> string
  val isMeta : String.string -> bool
  
  type typ_var
  val mk_typ_var_sort : Term.typ -> typ_var * sort
  type type_literal
  val add_typs_aux2 : (typ_var * string list) list -> type_literal list * type_literal list
  val gen_tptp_cls : int * string * string * string -> string
  val gen_tptp_type_cls : int * string * string * string * int -> string
  val tptp_of_typeLit : type_literal -> string

  end;

structure ResClause: RES_CLAUSE =
struct

(* Added for typed equality *)
val special_equal = ref false; (* by default,equality does not carry type information *)
val eq_typ_wrapper = "typeinfo"; (* default string *)


val schematic_var_prefix = "V_";
val fixed_var_prefix = "v_";

val tvar_prefix = "T_";
val tfree_prefix = "t_";

val clause_prefix = "cls_"; 
val arclause_prefix = "clsarity_" 
val clrelclause_prefix = "clsrel_";

val const_prefix = "c_";
val tconst_prefix = "tc_"; 

val class_prefix = "class_"; 


fun union_all xss = foldl (op union) [] xss;

 
(*Provide readable names for the more common symbolic functions*)
val const_trans_table =
      Symtab.make [("op =", "equal"),
	  	   ("op <=", "lessequals"),
		   ("op <", "less"),
		   ("op &", "and"),
		   ("op |", "or"),
		   ("op +", "plus"),
		   ("op -", "minus"),
		   ("op *", "times"),
		   ("op -->", "implies"),
		   ("{}", "emptyset"),
		   ("op :", "in"),
		   ("op Un", "union"),
		   ("op Int", "inter"),
		   ("List.op @", "append")];

val type_const_trans_table =
      Symtab.make [("*", "t_prod"),
	  	   ("+", "t_sum"),
		   ("~=>", "t_map")];

(*Escaping of special characters.
  Alphanumeric characters are left unchanged.
  The character _ goes to __
  Characters in the range ASCII space to / go to _A to _P, respectively.
  Other printing characters go to _NNN where NNN is the decimal ASCII code.*)
local

val A_minus_space = Char.ord #"A" - Char.ord #" ";

fun ascii_of_c c =
  if Char.isAlphaNum c then String.str c
  else if c = #"_" then "__"
  else if #" " <= c andalso c <= #"/" 
       then "_" ^ String.str (Char.chr (Char.ord c + A_minus_space))
  else if Char.isPrint c then ("_" ^ Int.toString (Char.ord c))
  else ""

in

val ascii_of = String.translate ascii_of_c;

end;

(* convert a list of strings into one single string; surrounded by brackets *)
fun paren_pack [] = ""   (*empty argument list*)
  | paren_pack strings = "(" ^ commas strings ^ ")";

fun bracket_pack strings = "[" ^ commas strings ^ "]";


(*Remove the initial ' character from a type variable, if it is present*)
fun trim_type_var s =
  if s <> "" andalso String.sub(s,0) = #"'" then String.extract(s,1,NONE)
  else error ("trim_type: Malformed type variable encountered: " ^ s);

fun ascii_of_indexname (v,0) = ascii_of v
  | ascii_of_indexname (v,i) = ascii_of v ^ "_" ^ Int.toString i;

fun make_schematic_var v = schematic_var_prefix ^ (ascii_of_indexname v);
fun make_fixed_var x = fixed_var_prefix ^ (ascii_of x);

fun make_schematic_type_var (x,i) = 
      tvar_prefix ^ (ascii_of_indexname (trim_type_var x,i));
fun make_fixed_type_var x = tfree_prefix ^ (ascii_of (trim_type_var x));

fun make_fixed_const c =
    case Symtab.lookup const_trans_table c of
        SOME c' => c'
      | NONE =>  const_prefix ^ ascii_of c;

fun make_fixed_type_const c = 
    case Symtab.lookup type_const_trans_table c of
        SOME c' => c'
      | NONE =>  tconst_prefix ^ ascii_of c;

fun make_type_class clas = class_prefix ^ ascii_of clas;



(***** definitions and functions for FOL clauses, prepared for conversion into TPTP format or SPASS format. *****)

val keep_types = ref true;

datatype kind = Axiom | Hypothesis | Conjecture;
fun name_of_kind Axiom = "axiom"
  | name_of_kind Hypothesis = "hypothesis"
  | name_of_kind Conjecture = "conjecture";

type clause_id = int;
type axiom_name = string;


type polarity = bool;

type indexname = Term.indexname;


(* "tag" is used for vampire specific syntax  *)
type tag = bool; 


(**** Isabelle FOL clauses ****)

val tagged = ref false;

type pred_name = string;
type sort = Term.sort;



datatype typ_var = FOLTVar of indexname | FOLTFree of string;

datatype fol_type = AtomV of string
		  | AtomF of string
		  | Comp of string * fol_type list;

fun string_of_fol_type (AtomV x) = x
  | string_of_fol_type (AtomF x) = x
  | string_of_fol_type (Comp(tcon,tps)) = 
    let val tstrs = map string_of_fol_type tps
    in
	tcon ^ (paren_pack tstrs)
    end;


datatype type_literal = LTVar of string | LTFree of string;

datatype folTerm = UVar of string * fol_type
                 | Fun of string * fol_type list * folTerm list;
datatype predicate = Predicate of pred_name * fol_type list * folTerm list;

datatype literal = Literal of polarity * predicate * tag;

fun mk_typ_var_sort (TFree(a,s)) = (FOLTFree a,s)
  | mk_typ_var_sort (TVar(v,s)) = (FOLTVar v,s);



(* ML datatype used to repsent one single clause: disjunction of literals. *)
datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    kind: kind,
		    literals: literal list,
		    types_sorts: (typ_var * sort) list, 
                    tvar_type_literals: type_literal list, 
                    tfree_type_literals: type_literal list ,
                    tvars: string list,
                    predicates: (string*int) list,
                    functions: (string*int) list};


exception CLAUSE of string * term;

fun get_literals (c as Clause(cls)) = #literals cls;

fun components_of_literal (Literal (pol,pred,tag)) = ((pol,pred),tag);

fun predicate_name (Predicate(predname,_,_)) = predname;


(*** make clauses ***)

fun isFalse (Literal (pol,Predicate(a,_,[]),_)) =
      (pol andalso a = "c_False") orelse
      (not pol andalso a = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol,Predicate(a,_,[]),_)) =
      (pol andalso a = "c_True") orelse
      (not pol andalso a = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  

fun make_clause (clause_id,axiom_name,kind,literals,
                 types_sorts,tvar_type_literals,
                 tfree_type_literals,tvars, predicates, functions) =
  if forall isFalse literals 
  then error "Problem too trivial for resolution (empty clause)"
  else
     Clause {clause_id = clause_id, axiom_name = axiom_name, kind = kind, 
             literals = literals, types_sorts = types_sorts,
             tvar_type_literals = tvar_type_literals,
             tfree_type_literals = tfree_type_literals,
             tvars = tvars, predicates = predicates, 
             functions = functions};


(** Some Clause destructor functions **)

fun string_of_kind (Clause cls) = name_of_kind (#kind cls);

fun get_axiomName (Clause cls) = #axiom_name cls;

fun get_clause_id (Clause cls) = #clause_id cls;

fun funcs_of_cls (Clause cls) = #functions cls;

fun preds_of_cls (Clause cls) = #predicates cls;


(*Declarations of the current theory--to allow suppressing types.*)
val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun num_typargs(s,T) = if !keep_types then length (!const_typargs (s,T)) else 0;

(*Initialize the type suppression mechanism with the current theory before
    producing any clauses!*)
fun init thy = (const_typargs := Sign.const_typargs thy);
    

(*Flatten a type to a fol_type while accumulating sort constraints on the TFrees and
  TVars it contains.*)    
fun type_of (Type (a, Ts)) = 
      let val (folTyps, (ts, funcs)) = types_of Ts 
	  val t = make_fixed_type_const a
      in    
	  (Comp(t,folTyps), (ts, (t, length Ts)::funcs))
      end
  | type_of (TFree (a,s)) = 
      let val t = make_fixed_type_var a
      in (AtomF(t), ([((FOLTFree a),s)], [(t,0)])) end
  | type_of (TVar (v, s)) = (AtomV(make_schematic_type_var v), ([((FOLTVar v),s)], []))
and types_of Ts =
      let val foltyps_ts = map type_of Ts 
	  val (folTyps,ts_funcs) = ListPair.unzip foltyps_ts
	  val (ts, funcslist) = ListPair.unzip ts_funcs
      in    
	  (folTyps, (union_all ts, union_all funcslist))
      end;


fun const_types_of (c,T) = types_of (!const_typargs (c,T));

(* Any variables created via the METAHYPS tactical should be treated as
   universal vars, although it is represented as "Free(...)" by Isabelle *)
val isMeta = String.isPrefix "METAHYP1_"

fun pred_name_type (Const(c,T)) = 
      let val (contys,(folTyps,funcs)) = const_types_of (c,T)
      in (make_fixed_const c, (contys,folTyps), funcs) end
  | pred_name_type (Free(x,T))  = 
      if isMeta x then raise CLAUSE("Predicate Not First Order 1", Free(x,T)) 
      else (make_fixed_var x, ([],[]), [])
  | pred_name_type (v as Var _) = raise CLAUSE("Predicate Not First Order 2", v)
  | pred_name_type t        = raise CLAUSE("Predicate input unexpected", t);


(* For typed equality *)
(* here "arg_typ" is the type of "="'s argument's type, not the type of the equality *)
(* Find type of equality arg *)
fun eq_arg_type (Type("fun",[T,_])) = 
    let val (folT,_) = type_of T;
    in  folT  end;

fun fun_name_type (Const("op =",T)) args =   (*FIXME: Is this special treatment of = needed??*)
      let val t = make_fixed_const "op ="
      in (t, ([eq_arg_type T], []), [(t,2)]) end
  | fun_name_type (Const(c,T)) args = 
      let val t = make_fixed_const c
	  val (contys, (folTyps,funcs)) = const_types_of (c,T)
	  val arity = num_typargs(c,T) + length args
      in
	  (t, (contys,folTyps), ((t,arity)::funcs))
      end
 | fun_name_type (Free(x,T)) args  = 
      let val t = make_fixed_var x
      in  (t, ([],[]), [(t, length args)]) end
  | fun_name_type f args = raise CLAUSE("Function Not First Order 1", f);


fun term_of (Var(ind_nm,T)) = 
      let val (folType,(ts,funcs)) = type_of T
      in
	  (UVar(make_schematic_var ind_nm, folType), (ts, funcs))
      end
  | term_of (Free(x,T)) = 
      let val (folType, (ts,funcs)) = type_of T
      in
	  if isMeta x then (UVar(make_schematic_var(x,0),folType),
			    (ts, ((make_schematic_var(x,0)),0)::funcs))
	  else
	      (Fun(make_fixed_var x, [folType], []), 
	       (ts, ((make_fixed_var x),0)::funcs))
      end
  | term_of (Const(c,T)) =  (* impossible to be equality *)
      let val (contys, (folTyps,funcs)) = const_types_of (c,T)
      in
	  (Fun(make_fixed_const c, contys, []),
	   (folTyps, ((make_fixed_const c),0)::funcs))
      end    
  | term_of app = 
      let val (f,args) = strip_comb app
          val _ = case f of Const(_,_) => ()
			  | Free(s,_)  => 
			      if isMeta s 
			      then raise CLAUSE("Function Not First Order 2", f)
			      else ()
			  | _ => raise CLAUSE("Function Not First Order 3", f);
	  val (funName,(contys,ts1),funcs) = fun_name_type f args
	  val (args',(ts2,funcs')) = terms_of args
      in
	  (Fun(funName,contys,args'), 
	   (union_all (ts1::ts2), 
	    union_all(funcs::funcs')))
      end
  | term_of t = raise CLAUSE("Function Not First Order 4", t)
and terms_of ts =  
      let val (args, ts_funcs) = ListPair.unzip (map term_of ts)
      in
	  (args, ListPair.unzip ts_funcs)
      end


fun pred_of (Const("op =", typ), args) =
      let val arg_typ = eq_arg_type typ 
	  val (args',(ts,funcs)) = terms_of args
	  val equal_name = make_fixed_const "op ="
      in
	  (Predicate(equal_name,[arg_typ],args'),
	   union_all ts, 
	   [((make_fixed_var equal_name), 2)], 
	   union_all funcs)
      end
  | pred_of (pred,args) = 
      let val (predName,(predType,ts1), pfuncs) = pred_name_type pred
	  val (args',(ts2,ffuncs)) = terms_of args
	  val ts3 = union_all (ts1::ts2)
	  val ffuncs' = union_all ffuncs
	  val newfuncs = pfuncs union ffuncs'
	  val arity = 
	    case pred of
		Const (c,T) => num_typargs(c,T) + length args
	      | _ => length args
      in
	  (Predicate(predName,predType,args'), ts3, 
	   [(predName, arity)], newfuncs)
      end;


(*Treatment of literals, possibly negated or tagged*)
fun predicate_of ((Const("Not",_) $ P), polarity, tag) =
      predicate_of (P, not polarity, tag)
  | predicate_of ((Const("HOL.tag",_) $ P), polarity, tag) =
      predicate_of (P, polarity, true)
  | predicate_of (term,polarity,tag) =
        (pred_of (strip_comb term), polarity, tag);

fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 (args as (lits, ts, preds, funcs)) (Const("op |",_) $ P $ Q) = 
      let val (lits', ts', preds', funcs') = literals_of_term1 args P
      in
	  literals_of_term1 (lits', ts', preds' union preds, funcs' union funcs) Q
      end
  | literals_of_term1 (lits, ts, preds, funcs) P =
      let val ((pred, ts', preds', funcs'), pol, tag) = predicate_of (P,true,false)
	  val lits' = Literal(pol,pred,tag) :: lits
      in
	  (lits', ts union ts', preds' union preds, funcs' union funcs)
      end;


val literals_of_term = literals_of_term1 ([],[],[],[]);



fun list_ord _ ([],[]) = EQUAL
  | list_ord _ ([],_) = LESS
  | list_ord _ (_,[]) = GREATER
  | list_ord ord (x::xs, y::ys) =
    let val xy_ord = ord(x,y)
    in
	case xy_ord of EQUAL => list_ord ord (xs,ys)
		     | _ => xy_ord
    end;

fun type_ord (AtomV(_),AtomV(_)) = EQUAL
  | type_ord (AtomV(_),_) = LESS
  | type_ord (AtomF(_),AtomV(_)) = GREATER
  | type_ord (AtomF(f1),AtomF(f2)) = string_ord (f1,f2)
  | type_ord (AtomF(_),_) = LESS
  | type_ord (Comp(_,_),AtomV(_)) = GREATER
  | type_ord (Comp(_,_),AtomF(_)) = GREATER
  | type_ord (Comp(con1,args1),Comp(con2,args2)) = 
    let val con_ord = string_ord(con1,con2)
    in
	case con_ord of EQUAL => types_ord (args1,args2)
		      | _ => con_ord
    end
and

types_ord ([],[]) = EQUAL
  | types_ord (tps1,tps2) = list_ord type_ord (tps1,tps2);


fun term_ord (UVar(_,_),UVar(_,_)) = EQUAL
  | term_ord (UVar(_,_),_) = LESS
  | term_ord (Fun(_,_,_),UVar(_)) = GREATER
  | term_ord (Fun(f1,tps1,tms1),Fun(f2,tps2,tms2)) = 
    let val fn_ord = string_ord (f1,f2)
    in
	case fn_ord of EQUAL => 
		       let val tms_ord = terms_ord (tms1,tms2)
		       in
			   case tms_ord of EQUAL => types_ord (tps1,tps2)
					 | _ => tms_ord
		       end
		     | _ => fn_ord
    end

and

terms_ord ([],[]) = EQUAL
  | terms_ord (tms1,tms2) = list_ord term_ord (tms1,tms2);



fun predicate_ord (Predicate(predname1,ftyps1,ftms1),Predicate(predname2,ftyps2,ftms2)) = 
    let val predname_ord = string_ord (predname1,predname2)
    in
	case predname_ord of EQUAL => 
			     let val ftms_ord = terms_ord(ftms1,ftms2)
			     in
				 case ftms_ord of EQUAL => types_ord(ftyps1,ftyps2)
						| _ => ftms_ord
			     end
			   | _ => predname_ord
    end;

fun literal_ord (Literal(false,_,_),Literal(true,_,_)) = LESS
  | literal_ord (Literal(true,_,_),Literal(false,_,_)) = GREATER
  | literal_ord (Literal(_,pred1,_),Literal(_,pred2,_)) = predicate_ord(pred1,pred2);

fun sort_lits lits = sort literal_ord lits;



(* FIX: not sure what to do with these funcs *)

(*Make literals for sorted type variables*) 
fun sorts_on_typs (_, [])   = ([]) 
  | sorts_on_typs (v, "HOL.type" :: s) =
      sorts_on_typs (v,s)   (*Ignore sort "type"*)
  | sorts_on_typs ((FOLTVar indx), (s::ss)) =
      LTVar((make_type_class s) ^ 
        "(" ^ (make_schematic_type_var indx) ^ ")") :: 
      (sorts_on_typs ((FOLTVar indx), ss))
  | sorts_on_typs ((FOLTFree x), (s::ss)) =
      LTFree((make_type_class s) ^ "(" ^ (make_fixed_type_var x) ^ ")") :: 
      (sorts_on_typs ((FOLTFree x), ss));


(*UGLY: seems to be parsing the "show sorts" output, removing anything that
  starts with a left parenthesis.*)
fun remove_type str = hd (String.fields (fn c => c = #"(") str);

fun pred_of_sort (LTVar x) = ((remove_type x),1)
|   pred_of_sort (LTFree x) = ((remove_type x),1)




(*Given a list of sorted type variables, return two separate lists.
  The first is for TVars, the second for TFrees.*)
fun add_typs_aux [] preds  = ([],[], preds)
  | add_typs_aux ((FOLTVar indx,s)::tss) preds = 
      let val vs = sorts_on_typs (FOLTVar indx, s)
          val preds' = (map pred_of_sort vs)@preds
	  val (vss,fss, preds'') = add_typs_aux tss preds'
      in
	  (vs union vss, fss, preds'')
      end
  | add_typs_aux ((FOLTFree x,s)::tss) preds  =
      let val fs = sorts_on_typs (FOLTFree x, s)
          val preds' = (map pred_of_sort fs)@preds
	  val (vss,fss, preds'') = add_typs_aux tss preds'
      in
	  (vss, fs union fss, preds'')
      end;

fun add_typs_aux2 [] = ([],[])
  | add_typs_aux2 ((FOLTVar indx,s)::tss) =
    let val vs = sorts_on_typs (FOLTVar indx,s)
	val (vss,fss) = add_typs_aux2 tss
    in
	(vs union vss,fss)
    end
  | add_typs_aux2 ((FOLTFree x,s)::tss) =
    let val fs = sorts_on_typs (FOLTFree x,s)
	val (vss,fss) = add_typs_aux2 tss
    in
	(vss,fs union fss)
    end;


fun add_typs (Clause cls) preds  = add_typs_aux (#types_sorts cls) preds 


(** make axiom clauses, hypothesis clauses and conjecture clauses. **)

fun get_tvar_strs [] = []
  | get_tvar_strs ((FOLTVar indx,s)::tss) = 
      let val vstr = make_schematic_type_var indx
      in
	  vstr ins (get_tvar_strs tss)
      end
  | get_tvar_strs((FOLTFree x,s)::tss) = distinct (get_tvar_strs tss)

(* FIX add preds and funcs to add typs aux here *)

fun make_axiom_clause_thm thm (ax_name,cls_id) =
    let val (lits,types_sorts, preds, funcs) = literals_of_term (prop_of thm)
	val lits' = sort_lits lits
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds 
        val tvars = get_tvar_strs types_sorts
    in 
	make_clause(cls_id,ax_name,Axiom,
	            lits',types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;


(* check if a clause is FOL first*)
fun make_conjecture_clause n t =
    let val _ = check_is_fol_term t
	    handle TERM("check_is_fol_term",_) => raise CLAUSE("Goal is not FOL",t)
	val (lits,types_sorts, preds, funcs) = literals_of_term t
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds 
        val tvars = get_tvar_strs types_sorts
    in
	make_clause(n,"conjecture",Conjecture,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;
    
fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (t::ts) =
      make_conjecture_clause n t :: make_conjecture_clauses_aux (n+1) ts

val make_conjecture_clauses = make_conjecture_clauses_aux 0


(*before converting an axiom clause to "clause" format, check if it is FOL*)
fun make_axiom_clause term (ax_name,cls_id) =
    let val _ = check_is_fol_term term 
	    handle TERM("check_is_fol_term",_) => raise CLAUSE("Axiom is not FOL", term) 
	val (lits,types_sorts, preds,funcs) = literals_of_term term
	val lits' = sort_lits lits
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds
        val tvars = get_tvar_strs types_sorts	
    in 
	make_clause(cls_id,ax_name,Axiom,
	            lits',types_sorts,tvar_lits,tfree_lits,
	            tvars, preds,funcs)
    end;



 
(**** Isabelle arities ****)

exception ARCLAUSE of string;
 

type class = string; 
type tcons = string; 


datatype arLit = TConsLit of bool * (class * tcons * string list) | TVarLit of bool * (class * string);
 
datatype arityClause =  
	 ArityClause of {clause_id: clause_id,
	  	         axiom_name: axiom_name,
			 kind: kind,
			 conclLit: arLit,
			 premLits: arLit list};


fun get_TVars 0 = []
  | get_TVars n = ("T_" ^ (Int.toString n)) :: get_TVars (n-1);



fun pack_sort(_,[])  = raise ARCLAUSE("Empty Sort Found") 
  | pack_sort(tvar, [cls]) = [(make_type_class cls, tvar)] 
  | pack_sort(tvar, cls::srt) =  (make_type_class cls,tvar) :: (pack_sort(tvar, srt));
    
    
fun make_TVarLit (b,(cls,str)) = TVarLit(b,(cls,str));
fun make_TConsLit (b,(cls,tcons,tvars)) = TConsLit(b,(make_type_class cls,make_fixed_type_const tcons,tvars));

fun make_axiom_arity_clause (tcons,n,(res,args)) =
   let val nargs = length args
       val tvars = get_TVars nargs
       val tvars_srts = ListPair.zip (tvars,args)
       val tvars_srts' = union_all(map pack_sort tvars_srts)
       val false_tvars_srts' = map (pair false) tvars_srts'
   in
      ArityClause {clause_id = n, kind = Axiom, 
                   axiom_name = tcons,
                   conclLit = make_TConsLit(true,(res,tcons,tvars)), 
                   premLits = map make_TVarLit false_tvars_srts'}
   end;
    
(*The number of clauses generated from cls, including type clauses*)
fun num_of_clauses (Clause cls) =
    let val num_tfree_lits = 
	      if !keep_types then length (#tfree_type_literals cls)
	      else 0
    in 	1 + num_tfree_lits  end;


(**** Isabelle class relations ****)


datatype classrelClause = 
	 ClassrelClause of {clause_id: clause_id,
			    subclass: class,
			    superclass: class option};


fun make_axiom_classrelClause n subclass superclass =
  ClassrelClause {clause_id = n,
                  subclass = subclass, superclass = superclass};


fun classrelClauses_of_aux n sub [] = []
  | classrelClauses_of_aux n sub (sup::sups) =
      make_axiom_classrelClause n sub (SOME sup) :: classrelClauses_of_aux (n+1) sub sups;


fun classrelClauses_of (sub,sups) = 
    case sups of [] => [make_axiom_classrelClause 0 sub NONE]
	       | _ => classrelClauses_of_aux 0 sub sups;


(***** Isabelle arities *****)


fun arity_clause _ (tcons, []) = []
  | arity_clause n (tcons, ar::ars) =
      make_axiom_arity_clause (tcons,n,ar) :: 
      arity_clause (n+1) (tcons,ars);

fun multi_arity_clause [] = []
  | multi_arity_clause (tcon_ar :: tcons_ars)  =
      arity_clause 0 tcon_ar  @  multi_arity_clause tcons_ars 

fun arity_clause_thy thy =
  let val arities = #arities (Type.rep_tsig (Sign.tsig_of thy))
  in multi_arity_clause (Symtab.dest arities) end;


(* Isabelle classes *)

type classrelClauses = classrelClause list Symtab.table;

val classrel_of = #2 o #classes o Type.rep_tsig o Sign.tsig_of;
fun classrel_clauses_classrel (C: Sorts.classes) = map classrelClauses_of (Graph.dest C);
val classrel_clauses_thy = List.concat o classrel_clauses_classrel o classrel_of;



(****!!!! Changed for typed equality !!!!****)

fun wrap_eq_type typ t = eq_typ_wrapper ^"(" ^ t ^ "," ^ typ ^ ")";

(*Only need to wrap equality's arguments with "typeinfo" if the output clauses are typed 
 and if we specifically ask for types to be included.   *)
fun string_of_equality (typ,terms) =
      let val [tstr1,tstr2] = map string_of_term terms
	  val typ' = string_of_fol_type typ
      in
	  if !keep_types andalso !special_equal 
	  then "equal(" ^ (wrap_eq_type typ' tstr1) ^ "," ^ 
		 	  (wrap_eq_type typ' tstr2) ^ ")"
	  else "equal(" ^ tstr1 ^ "," ^ tstr2 ^ ")"
      end
and string_of_term (UVar(x,_)) = x
  | string_of_term (Fun("equal",[typ],terms)) = string_of_equality(typ,terms)
  | string_of_term (Fun (name,typs,[])) = name (*Overloaded consts like 0 don't get types!*)
  | string_of_term (Fun (name,typs,terms)) = 
      let val terms_as_strings = map string_of_term terms
	  val typs' = if !keep_types then map string_of_fol_type typs else []
      in  name ^ (paren_pack (terms_as_strings @ typs'))  end
  | string_of_term _ = error "string_of_term";      

(* before output the string of the predicate, check if the predicate corresponds to an equality or not. *)
fun string_of_predicate (Predicate("equal",[typ],terms)) = string_of_equality(typ,terms)
  | string_of_predicate (Predicate(name,typs,terms)) = 
      let val terms_as_strings = map string_of_term terms
	  val typs' = if !keep_types then map string_of_fol_type typs else []
      in  name ^ (paren_pack (terms_as_strings @ typs'))  end
  | string_of_predicate _ = error "string_of_predicate";      


fun string_of_clausename (cls_id,ax_name) = 
    clause_prefix ^ ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);
    

(********************************)
(* Code for producing DFG files *)
(********************************)

fun dfg_literal (Literal(pol,pred,tag)) =
    let val pred_string = string_of_predicate pred
    in
	if pol then pred_string else "not(" ^pred_string ^ ")"  
    end;


(* FIX: what does this mean? *)
(*fun dfg_of_typeLit (LTVar x) = "not(" ^ x ^ ")"
  | dfg_of_typeLit (LTFree x) = "(" ^ x ^ ")";*)

fun dfg_of_typeLit (LTVar x) =  x 
  | dfg_of_typeLit (LTFree x) = x ;
 
(*Make the string of universal quantifiers for a clause*)
fun forall_open ([],[]) = ""
  | forall_open (vars,tvars) = "forall([" ^ (commas (tvars@vars))^ "],\n"

fun forall_close ([],[]) = ""
  | forall_close (vars,tvars) = ")"

fun gen_dfg_cls (cls_id,ax_name,knd,lits,tvars,vars) = 
    "clause( %(" ^ knd ^ ")\n" ^ forall_open(vars,tvars) ^ 
    "or(" ^ lits ^ ")" ^ forall_close(vars,tvars) ^ ",\n" ^ 
    string_of_clausename (cls_id,ax_name) ^  ").";

fun gen_dfg_type_cls (cls_id,ax_name,knd,tfree_lit,idx,tvars,vars) = 
    "clause( %(" ^ knd ^ ")\n" ^ forall_open(vars,tvars) ^ 
    "or( " ^ tfree_lit ^ ")" ^ forall_close(vars,tvars) ^ ",\n" ^ 
    string_of_type_clsname (cls_id,ax_name,idx) ^  ").";

fun dfg_clause_aux (Clause cls) = 
  let val lits = map dfg_literal (#literals cls)
      val tvar_lits_strs = 
	  if !keep_types then map dfg_of_typeLit (#tvar_type_literals cls) 
	  else []
      val tfree_lits =
          if !keep_types then map dfg_of_typeLit (#tfree_type_literals cls)
          else []
  in
      (tvar_lits_strs @ lits, tfree_lits)
  end; 


fun dfg_folterms (Literal(pol,pred,tag)) = 
  let val Predicate (predname, _, folterms) = pred
  in  folterms  end

 
fun get_uvars (UVar(a,typ)) = [a] 
|   get_uvars (Fun (_,typ,tlist)) = union_all(map get_uvars tlist)


fun is_uvar (UVar _) = true
|   is_uvar (Fun _) = false;

fun uvar_name (UVar(a,_)) = a
|   uvar_name (Fun (a,_,_)) = raise CLAUSE("Not a variable", Const(a,dummyT));

fun dfg_vars (Clause cls) =
    let val lits = #literals cls
        val folterms = List.concat (map dfg_folterms lits)
    in 
        union_all(map get_uvars folterms)
    end


fun dfg_tvars (Clause cls) =(#tvars cls)


	
(* make this return funcs and preds too? *)
fun string_of_predname (Predicate("equal",_,terms)) = "EQUALITY"
  | string_of_predname (Predicate(name,_,terms)) = name
    
	

fun concat_with sep []  = ""
  | concat_with sep [x] = "(" ^ x ^ ")"
  | concat_with sep (x::xs) = "(" ^ x ^ ")" ^  sep ^ (concat_with sep xs);

fun dfg_pred (Literal(pol,pred,tag)) ax_name = 
    (string_of_predname pred) ^ " " ^ ax_name

fun dfg_clause cls =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
             (*"lits" includes the typing assumptions (TVars)*)
        val vars = dfg_vars cls
        val tvars = dfg_tvars cls
	val knd = string_of_kind cls
	val lits_str = commas lits
	val cls_id = get_clause_id cls
	val axname = get_axiomName cls
	val cls_str = gen_dfg_cls(cls_id,axname,knd,lits_str,tvars, vars) 			
        fun typ_clss k [] = []
          | typ_clss k (tfree :: tfrees) = 
              (gen_dfg_type_cls(cls_id,axname,knd,tfree,k, tvars,vars)) :: 
              (typ_clss (k+1) tfrees)
    in 
	cls_str :: (typ_clss 0 tfree_lits)
    end;

fun string_of_arity (name, num) =  name ^ "," ^ (Int.toString num) 

fun string_of_preds preds = 
  "predicates[" ^ (concat_with ", " (map string_of_arity preds)) ^ "].\n";

fun string_of_funcs funcs =
  "functions[" ^ (concat_with ", " (map string_of_arity funcs)) ^ "].\n" ;


fun string_of_symbols predstr funcstr = 
  "list_of_symbols.\n" ^ predstr  ^ funcstr  ^ "end_of_list.\n\n";


fun string_of_axioms axstr = 
  "list_of_clauses(axioms,cnf).\n" ^ axstr ^ "end_of_list.\n\n";


fun string_of_conjectures conjstr = 
  "list_of_clauses(conjectures,cnf).\n" ^ conjstr ^ "end_of_list.\n\n";

fun string_of_descrip () = 
  "list_of_descriptions.\nname({*[ File     : ],[ Names    :]*}).\nauthor({*[ Source   :]*}).\nstatus(unknown).\ndescription({*[ Refs     :]*}).\nend_of_list.\n\n"


fun string_of_start name = "%------------------------------------------------------------------------------\nbegin_problem(" ^ name ^ ").\n\n";


fun string_of_end () = "end_problem.\n%------------------------------------------------------------------------------";


fun clause2dfg cls =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
            (*"lits" includes the typing assumptions (TVars)*)
	val cls_id = get_clause_id cls
	val ax_name = get_axiomName cls
        val vars = dfg_vars cls
        val tvars = dfg_tvars cls
        val funcs = funcs_of_cls cls
        val preds = preds_of_cls cls
	val knd = string_of_kind cls
	val lits_str = commas lits
	val cls_str = gen_dfg_cls(cls_id,ax_name,knd,lits_str,tvars,vars) 
    in
	(cls_str,tfree_lits) 
    end;



fun tfree_dfg_clause tfree_lit =
  "clause( %(conjecture)\n" ^ "or( " ^ tfree_lit ^ "),\n" ^ "tfree_tcs" ^ ")."


fun gen_dfg_file probname axioms conjectures funcs preds = 
    let val axstrs_tfrees = (map clause2dfg axioms)
	val (axstrs, atfrees) = ListPair.unzip axstrs_tfrees
        val axstr = (space_implode "\n" axstrs) ^ "\n\n"
        val conjstrs_tfrees = (map clause2dfg conjectures)
	val (conjstrs, atfrees) = ListPair.unzip conjstrs_tfrees
        val tfree_clss = map tfree_dfg_clause (union_all atfrees) 
        val conjstr = (space_implode "\n" (tfree_clss@conjstrs)) ^ "\n\n"
        val funcstr = string_of_funcs funcs
        val predstr = string_of_preds preds
    in
       (string_of_start probname) ^ (string_of_descrip ()) ^ 
       (string_of_symbols funcstr predstr) ^  
       (string_of_axioms axstr) ^
       (string_of_conjectures conjstr) ^ (string_of_end ())
    end;
   
fun clauses2dfg [] probname axioms conjectures funcs preds = 
      let val funcs' = (union_all(map funcs_of_cls axioms)) @ funcs
	  val preds' = (union_all(map preds_of_cls axioms)) @ preds
      in
	 gen_dfg_file probname axioms conjectures funcs' preds' 
      end
 | clauses2dfg (cls::clss) probname axioms conjectures funcs preds = 
     let val (lits,tfree_lits) = dfg_clause_aux cls
	       (*"lits" includes the typing assumptions (TVars)*)
	 val cls_id = get_clause_id cls
	 val ax_name = get_axiomName cls
	 val vars = dfg_vars cls
	 val tvars = dfg_tvars cls
	 val funcs' = (funcs_of_cls cls) union funcs
	 val preds' = (preds_of_cls cls) union preds
	 val knd = string_of_kind cls
	 val lits_str = concat_with ", " lits
	 val axioms' = if knd = "axiom" then (cls::axioms) else axioms
	 val conjectures' = 
	     if knd = "conjecture" then (cls::conjectures) else conjectures
     in
	 clauses2dfg clss probname axioms' conjectures' funcs' preds' 
     end;


fun string_of_arClauseID (ArityClause {clause_id,axiom_name,...}) =
    arclause_prefix ^ ascii_of axiom_name ^ "_" ^ Int.toString clause_id;

fun string_of_arKind (ArityClause arcls) = name_of_kind(#kind arcls);

(*FIXME!!! currently is TPTP format!*)
fun dfg_of_arLit (TConsLit(b,(c,t,args))) =
      let val pol = if b then "++" else "--"
	  val arg_strs = paren_pack args
      in 
	  pol ^ c ^ "(" ^ t ^ arg_strs ^ ")"
      end
  | dfg_of_arLit (TVarLit(b,(c,str))) =
      let val pol = if b then "++" else "--"
      in
	  pol ^ c ^ "(" ^ str ^ ")"
      end;
    

fun dfg_of_conclLit (ArityClause arcls) = dfg_of_arLit (#conclLit arcls);
     

fun dfg_of_premLits (ArityClause arcls) = map dfg_of_arLit (#premLits arcls);
		


(*FIXME: would this have variables in a forall? *)

fun dfg_arity_clause arcls = 
  let val arcls_id = string_of_arClauseID arcls
      val concl_lit = dfg_of_conclLit arcls
      val prems_lits = dfg_of_premLits arcls
      val knd = string_of_arKind arcls
      val all_lits = concl_lit :: prems_lits
  in
      "clause( %(" ^ knd ^ ")\n" ^  "or( " ^ (bracket_pack all_lits) ^ ")),\n" ^
       arcls_id ^  ")."
  end;


(********************************)
(* code to produce TPTP files   *)
(********************************)

fun tptp_literal (Literal(pol,pred,tag)) =
    let val pred_string = string_of_predicate pred
	val tagged_pol = 
	      if (tag andalso !tagged) then (if pol then "+++" else "---")
	      else (if pol then "++" else "--")
     in
	tagged_pol ^ pred_string
    end;

fun tptp_of_typeLit (LTVar x) = "--" ^ x
  | tptp_of_typeLit (LTFree x) = "++" ^ x;
 

fun gen_tptp_cls (cls_id,ax_name,knd,lits) = 
    "input_clause(" ^ string_of_clausename (cls_id,ax_name) ^ "," ^ 
    knd ^ "," ^ lits ^ ").";

fun gen_tptp_type_cls (cls_id,ax_name,knd,tfree_lit,idx) = 
    "input_clause(" ^ string_of_type_clsname (cls_id,ax_name,idx) ^ "," ^ 
    knd ^ ",[" ^ tfree_lit ^ "]).";

fun tptp_type_lits (Clause cls) = 
    let val lits = map tptp_literal (#literals cls)
	val tvar_lits_strs =
	      if !keep_types 
	      then (map tptp_of_typeLit (#tvar_type_literals cls)) 
	      else []
	val tfree_lits = 
	      if !keep_types
	      then (map tptp_of_typeLit (#tfree_type_literals cls)) 
	      else []
    in
	(tvar_lits_strs @ lits, tfree_lits)
    end; 

fun tptp_clause cls =
    let val (lits,tfree_lits) = tptp_type_lits cls 
            (*"lits" includes the typing assumptions (TVars)*)
	val cls_id = get_clause_id cls
	val ax_name = get_axiomName cls
	val knd = string_of_kind cls
	val lits_str = bracket_pack lits
	val cls_str = gen_tptp_cls(cls_id,ax_name,knd,lits_str) 			 
	fun typ_clss k [] = []
          | typ_clss k (tfree :: tfrees) = 
              gen_tptp_type_cls(cls_id,ax_name,knd,tfree,k) :: 
              typ_clss (k+1) tfrees
    in 
	cls_str :: (typ_clss 0 tfree_lits)
    end;

fun clause2tptp cls =
    let val (lits,tfree_lits) = tptp_type_lits cls 
            (*"lits" includes the typing assumptions (TVars)*)
	val cls_id = get_clause_id cls
	val ax_name = get_axiomName cls
	val knd = string_of_kind cls
	val lits_str = bracket_pack lits
	val cls_str = gen_tptp_cls(cls_id,ax_name,knd,lits_str) 
    in
	(cls_str,tfree_lits) 
    end;


fun tfree_clause tfree_lit =
    "input_clause(" ^ "tfree_tcs," ^ "conjecture" ^ ",[" ^ tfree_lit ^ "]).";


fun tptp_of_arLit (TConsLit(b,(c,t,args))) =
      let val pol = if b then "++" else "--"
	  val  arg_strs = paren_pack args
      in 
	  pol ^ c ^ "(" ^ t ^ arg_strs ^ ")"
      end
  | tptp_of_arLit (TVarLit(b,(c,str))) =
      let val pol = if b then "++" else "--"
      in
	  pol ^ c ^ "(" ^ str ^ ")"
      end;
    

fun tptp_of_conclLit (ArityClause arcls) = tptp_of_arLit (#conclLit arcls);
     
fun tptp_of_premLits (ArityClause arcls) = map tptp_of_arLit (#premLits arcls);
		
fun tptp_arity_clause arcls = 
    let val arcls_id = string_of_arClauseID arcls
	val concl_lit = tptp_of_conclLit arcls
	val prems_lits = tptp_of_premLits arcls
	val knd = string_of_arKind arcls
	val all_lits = concl_lit :: prems_lits
    in
	"input_clause(" ^ arcls_id ^ "," ^ knd ^ "," ^ 
	(bracket_pack all_lits) ^ ")."
    end;

fun tptp_classrelLits sub sup = 
    let val tvar = "(T)"
    in 
	case sup of NONE => "[++" ^ sub ^ tvar ^ "]"
		  | (SOME supcls) =>  "[--" ^ sub ^ tvar ^ ",++" ^ supcls ^ tvar ^ "]"
    end;


fun tptp_classrelClause (ClassrelClause {clause_id,subclass,superclass,...}) =
    let val relcls_id = clrelclause_prefix ^ ascii_of subclass ^ "_" ^ 
                        Int.toString clause_id
	val lits = tptp_classrelLits (make_type_class subclass) 
	                (Option.map make_type_class superclass)
    in
	"input_clause(" ^ relcls_id ^ ",axiom," ^ lits ^ ")."
    end; 

end;
