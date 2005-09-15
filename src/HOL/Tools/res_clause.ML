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
  val classrelClauses_of : string * string list -> classrelClause list
  type clause
  val init : theory -> unit
  val make_axiom_arity_clause :
     string * (string * string list list) -> arityClause
  val make_axiom_classrelClause :  string * string option -> classrelClause
  val make_axiom_clause : Term.term -> string * int -> clause
  val make_conjecture_clause : Term.term -> clause
  val make_conjecture_clause_thm : Thm.thm -> clause
  val make_hypothesis_clause : Term.term -> clause
  val get_axiomName : clause ->  string
  val isTaut : clause -> bool
  val num_of_clauses : clause -> int

  val dfg_clauses2str : string list -> string
  val clause2dfg : clause -> string * string list
  val clauses2dfg : clause list -> string -> clause list -> clause list ->
	   (string * int) list -> (string * int) list -> string
  val tfree_dfg_clause : string -> string

  val tptp_arity_clause : arityClause -> string
  val tptp_classrelClause : classrelClause -> string
  val tptp_clause : clause -> string list
  val tptp_clauses2str : string list -> string
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
val arclause_prefix = "arcls_" 
val clrelclause_prefix = "relcls_";

val const_prefix = "c_";
val tconst_prefix = "tc_"; 

val class_prefix = "class_"; 


(**** some useful functions ****)
 
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
		   ("op Int", "inter")];

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

(*Remove the initial ' character from a type variable, if it is present*)
fun trim_type_var s =
  if s <> "" andalso String.sub(s,0) = #"'" then String.extract(s,1,NONE)
  else error ("trim_type: Malformed type variable encountered: " ^ s);

fun ascii_of_indexname (v,0) = ascii_of v
  | ascii_of_indexname (v,i) = ascii_of v ^ "_" ^ string_of_int i;

fun make_schematic_var v = schematic_var_prefix ^ (ascii_of_indexname v);
fun make_fixed_var x = fixed_var_prefix ^ (ascii_of x);

(*Type variables contain _H because the character ' translates to that.*)
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


val id_ref = ref 0;

fun generate_id () = 
  let val id = !id_ref
  in id_ref := id + 1; id end;



(**** Isabelle FOL clauses ****)

val tagged = ref false;

type pred_name = string;
type sort = Term.sort;
type fol_type = string;


datatype type_literal = LTVar of string | LTFree of string;


datatype folTerm = UVar of string * fol_type
                 | Fun of string * fol_type * folTerm list;
datatype predicate = Predicate of pred_name * fol_type * folTerm list;

datatype literal = Literal of polarity * predicate * tag;

datatype typ_var = FOLTVar of indexname | FOLTFree of string;


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



(*Definitions of the current theory--to allow suppressing types.*)
val curr_defs = ref Defs.empty;

(*Initialize the type suppression mechanism with the current theory before
    producing any clauses!*)
fun init thy = (curr_defs := Theory.defs_of thy);

fun no_types_needed s = Defs.monomorphic (!curr_defs) s;
    

(*Flatten a type to a string while accumulating sort constraints on the TFress and
  TVars it contains.*)    
fun type_of (Type (a, [])) = 
      let val t = make_fixed_type_const a
      in (t,([],[(t,0)]))  end
  | type_of (Type (a, Ts)) = 
      let val foltyps_ts = map type_of Ts 
	  val (folTyps,ts_funcs) = ListPair.unzip foltyps_ts
	  val (ts, funcslist) = ListPair.unzip ts_funcs
	  val ts' = ResLib.flat_noDup ts
	  val funcs' = ResLib.flat_noDup funcslist
	  val t = make_fixed_type_const a
      in    
	  ((t ^ (ResLib.list_to_string folTyps)),(ts', (t, length Ts)::funcs') )
      end
  | type_of (TFree (a, s)) = 
      let val t = make_fixed_type_var a
      in (t, ([((FOLTFree a),s)],[(t,0)]) ) end
  | type_of (TVar (v, s)) = (make_schematic_type_var v, ([((FOLTVar v),s)], []))


fun maybe_type_of c T =
 if no_types_needed c then ("",([],[])) else type_of T;

(* Any variables created via the METAHYPS tactical should be treated as
   universal vars, although it is represented as "Free(...)" by Isabelle *)
val isMeta = String.isPrefix "METAHYP1_"

fun pred_name_type (Const(c,T)) = 
      let val (typof,(folTyps,funcs)) = maybe_type_of c T
      in (make_fixed_const c, (typof,folTyps), funcs) end
  | pred_name_type (Free(x,T))  = 
      if isMeta x then raise CLAUSE("Predicate Not First Order 1", Free(x,T)) 
      else (make_fixed_var x, ("",[]), [])
  | pred_name_type (v as Var _) = raise CLAUSE("Predicate Not First Order 2", v)
  | pred_name_type t        = raise CLAUSE("Predicate input unexpected", t);


(* For type equality *)
(* here "arg_typ" is the type of "="'s argument's type, not the type of the equality *)
(* Find type of equality arg *)
fun eq_arg_type (Type("fun",[T,_])) = 
    let val (folT,_) = type_of T;
    in  folT  end;

fun fun_name_type (Const(c,T)) args = 
      let val t = make_fixed_const c
	val (typof, (folTyps,funcs)) = maybe_type_of c T
	val arity = if !keep_types andalso not (no_types_needed c)
	            then 1 + length args
	            else length args
      in
	  (t, (typof,folTyps), ((t,arity)::funcs))
      end
 | fun_name_type (Free(x,T)) args  = 
      let val t = make_fixed_var x
      in
	    (t, ("",[]), [(t, length args)])
      end
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
	      (Fun(make_fixed_var x, folType, []), 
	       (ts, ((make_fixed_var x),0)::funcs))
      end
  | term_of (Const(c,T)) =  (* impossible to be equality *)
      let val (folType,(ts,funcs)) = type_of T
      in
	  (Fun(make_fixed_const c, folType, []),
	   (ts, ((make_fixed_const c),0)::funcs))
      end    
  | term_of (app as (t $ a)) = 
      let val (f,args) = strip_comb app
	  fun term_of_aux () = 
	      let val (funName,(funType,ts1),funcs) = fun_name_type f args
		  val (args',ts_funcs) = ListPair.unzip (map term_of args)
		  val (ts2,funcs') = ListPair.unzip ts_funcs
		  val ts3 = ResLib.flat_noDup (ts1::ts2)
		  val funcs'' = ResLib.flat_noDup((funcs::funcs'))
	      in
		  (Fun(funName,funType,args'), (ts3,funcs''))
	      end
	  fun term_of_eq ((Const ("op =", typ)),args) =
	      let val arg_typ = eq_arg_type typ
		  val (args',ts_funcs) = ListPair.unzip (map term_of args)
		  val (ts,funcs) = ListPair.unzip ts_funcs
		  val equal_name = make_fixed_const ("op =")
	      in
		  (Fun(equal_name,arg_typ,args'),
		   (ResLib.flat_noDup ts, 
		    (make_fixed_var equal_name, 2):: ResLib.flat_noDup funcs))
	      end
      in
	 case f of Const ("op =", typ) => term_of_eq (f,args)
		 | Const(_,_) => term_of_aux ()
		 | Free(s,_)  => 
		     if isMeta s 
		     then raise CLAUSE("Function Not First Order 2", f)
		     else term_of_aux()
		 | _ => raise CLAUSE("Function Not First Order 3", f)
      end
  | term_of t = raise CLAUSE("Function Not First Order 4", t); 


fun pred_of (Const("op =", typ), args) =
      let val arg_typ = eq_arg_type typ 
	  val (args',ts_funcs) = ListPair.unzip (map term_of args)
	  val (ts,funcs) = ListPair.unzip ts_funcs
	  val equal_name = make_fixed_const "op ="
      in
	  (Predicate(equal_name,arg_typ,args'),
	   ResLib.flat_noDup ts, 
	   [((make_fixed_var equal_name), 2)], 
	   (ResLib.flat_noDup funcs))
      end
  | pred_of (pred,args) = 
      let val (predName,(predType,ts1), pfuncs) = pred_name_type pred
	  val (args',ts_funcs) = ListPair.unzip (map term_of args)
	  val (ts2,ffuncs) = ListPair.unzip ts_funcs
	  val ts3 = ResLib.flat_noDup (ts1::ts2)
	  val ffuncs' = (ResLib.flat_noDup ffuncs)
	  val newfuncs = distinct (pfuncs@ffuncs')
	  val arity = 
	    case pred of
		Const (c,_) => 
		      if !keep_types andalso not (no_types_needed c)
		      then 1 + length args
		      else length args
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

fun literals_of_term ((Const("Trueprop",_) $ P),lits_ts, preds, funcs) =    
      literals_of_term(P,lits_ts, preds, funcs)
  | literals_of_term ((Const("op |",_) $ P $ Q),(lits,ts), preds,funcs) = 
      let val (lits',ts', preds', funcs') = 
            literals_of_term(P,(lits,ts), preds,funcs)
      in
	  literals_of_term(Q, (lits',ts'), distinct(preds'@preds), 
	                   distinct(funcs'@funcs))
      end
  | literals_of_term (P,(lits,ts), preds, funcs) = 
      let val ((pred,ts', preds', funcs'), pol, tag) = 
              predicate_of (P,true,false)
	  val lits' = Literal(pol,pred,tag) :: lits
	  val ts'' = ResLib.no_rep_app ts ts' 
      in
	  (lits',ts'', distinct(preds'@preds), distinct(funcs'@funcs))
      end;


fun literals_of_thm thm = literals_of_term (prop_of thm, ([],[]), [], []);


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
	  (ResLib.no_rep_app vs vss, fss, preds'')
      end
  | add_typs_aux ((FOLTFree x,s)::tss) preds  =
      let val fs = sorts_on_typs (FOLTFree x, s)
          val preds' = (map pred_of_sort fs)@preds
	  val (vss,fss, preds'') = add_typs_aux tss preds'
      in
	  (vss, ResLib.no_rep_app fs fss,preds'')
      end;

fun add_typs (Clause cls) preds  = add_typs_aux (#types_sorts cls) preds 


(** make axiom clauses, hypothesis clauses and conjecture clauses. **)

fun get_tvar_strs [] = []
  | get_tvar_strs ((FOLTVar indx,s)::tss) = 
      let val vstr = make_schematic_type_var indx
          val vstrs = get_tvar_strs tss
      in
	  (distinct( vstr:: vstrs))
      end
  | get_tvar_strs((FOLTFree x,s)::tss) = distinct (get_tvar_strs tss)

(* FIX add preds and funcs to add typs aux here *)

fun make_axiom_clause_thm thm (ax_name,cls_id) =
    let val (lits,types_sorts, preds, funcs) = literals_of_thm thm
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds 
        val tvars = get_tvar_strs types_sorts
    in 
	make_clause(cls_id,ax_name,Axiom,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;



fun make_conjecture_clause_thm thm =
    let val (lits,types_sorts, preds, funcs) = literals_of_thm thm
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds 
        val tvars = get_tvar_strs types_sorts
    in
	make_clause(cls_id,"",Conjecture,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;


fun make_axiom_clause term (ax_name,cls_id) =
    let val (lits,types_sorts, preds,funcs) = literals_of_term (term,([],[]), [],[])
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds
        val tvars = get_tvar_strs types_sorts	
    in 
	make_clause(cls_id,ax_name,Axiom,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds,funcs)
    end;


fun make_hypothesis_clause term =
    let val (lits,types_sorts, preds, funcs) = literals_of_term (term,([],[]),[],[])
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts  preds 
        val tvars = get_tvar_strs types_sorts
    in
	make_clause(cls_id,"",Hypothesis,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;
 
fun make_conjecture_clause term =
    let val (lits,types_sorts, preds, funcs) = literals_of_term (term,([],[]),[],[])
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits, preds) = add_typs_aux types_sorts preds 
        val tvars = get_tvar_strs types_sorts	
    in
	make_clause(cls_id,"",Conjecture,
	            lits,types_sorts,tvar_lits,tfree_lits,
	            tvars, preds, funcs)
    end;
 

 
(**** Isabelle arities ****)

exception ARCLAUSE of string;
 

type class = string; 
type tcons = string; 


datatype arLit = TConsLit of bool * (class * tcons * string list) | TVarLit of bool * (class * string);
 
datatype arityClause =  
	 ArityClause of {clause_id: clause_id,
			 kind: kind,
			 conclLit: arLit,
			 premLits: arLit list};


fun get_TVars 0 = []
  | get_TVars n = ("T_" ^ (string_of_int n)) :: get_TVars (n-1);



fun pack_sort(_,[])  = raise ARCLAUSE("Empty Sort Found") 
  | pack_sort(tvar, [cls]) = [(make_type_class cls, tvar)] 
  | pack_sort(tvar, cls::srt) =  (make_type_class cls,tvar) :: (pack_sort(tvar, srt));
    
    
fun make_TVarLit (b,(cls,str)) = TVarLit(b,(cls,str));
fun make_TConsLit (b,(cls,tcons,tvars)) = TConsLit(b,(make_type_class cls,make_fixed_type_const tcons,tvars));


fun make_arity_clause (clause_id,kind,conclLit,premLits) =
    ArityClause {clause_id = clause_id, kind = kind, conclLit = conclLit, premLits = premLits};


fun make_axiom_arity_clause (tcons,(res,args)) =
     let val cls_id = generate_id()
	 val nargs = length args
	 val tvars = get_TVars nargs
	 val conclLit = make_TConsLit(true,(res,tcons,tvars))
         val tvars_srts = ListPair.zip (tvars,args)
	 val tvars_srts' = ResLib.flat_noDup(map pack_sort tvars_srts)
         val false_tvars_srts' = ResLib.pair_ins false tvars_srts'
	 val premLits = map make_TVarLit false_tvars_srts'
     in
	 make_arity_clause (cls_id,Axiom,conclLit,premLits)
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

fun make_classrelClause (clause_id,subclass,superclass) =
    ClassrelClause {clause_id = clause_id,subclass = subclass, superclass = superclass};


fun make_axiom_classrelClause (subclass,superclass) =
    let val cls_id = generate_id()
	val sub = make_type_class subclass
	val sup = case superclass of NONE => NONE 
				   | SOME s => SOME (make_type_class s)
    in
	make_classrelClause(cls_id,sub,sup)
    end;



fun classrelClauses_of_aux (sub,[]) = []
  | classrelClauses_of_aux (sub,(sup::sups)) = make_axiom_classrelClause(sub,SOME sup) :: (classrelClauses_of_aux (sub,sups));


fun classrelClauses_of (sub,sups) = 
    case sups of [] => [make_axiom_classrelClause (sub,NONE)]
	       | _ => classrelClauses_of_aux (sub, sups);


(****!!!! Changed for typed equality !!!!****)

fun wrap_eq_type typ t = eq_typ_wrapper ^"(" ^ t ^ "," ^ typ ^ ")";

(* Only need to wrap equality's arguments with "typeinfo" if the output clauses are typed && if we specifically ask for types to be included.   *)
fun string_of_equality (typ,terms) =
      let val [tstr1,tstr2] = map string_of_term terms
      in
	  if !keep_types andalso !special_equal 
	  then "equal(" ^ (wrap_eq_type typ tstr1) ^ "," ^ 
		 	  (wrap_eq_type typ tstr2) ^ ")"
	  else "equal(" ^ tstr1 ^ "," ^ tstr2 ^ ")"
      end
and string_of_term (UVar(x,_)) = x
  | string_of_term (Fun("equal",typ,terms)) = string_of_equality(typ,terms)
  | string_of_term (Fun (name,typ,[])) = name
  | string_of_term (Fun (name,typ,terms)) = 
      let val terms' = map string_of_term terms
      in
	  if !keep_types andalso typ<>"" 
	  then name ^ (ResLib.list_to_string (terms' @ [typ]))
	  else name ^ (ResLib.list_to_string terms')
      end;

(* before output the string of the predicate, check if the predicate corresponds to an equality or not. *)
fun string_of_predicate (Predicate("equal",typ,terms)) = 
      string_of_equality(typ,terms)
  | string_of_predicate (Predicate(name,_,[])) = name 
  | string_of_predicate (Predicate(name,typ,terms)) = 
      let val terms_as_strings = map string_of_term terms
      in
	  if !keep_types andalso typ<>""
	  then name ^ (ResLib.list_to_string  (terms_as_strings @ [typ]))
	  else name ^ (ResLib.list_to_string terms_as_strings) 
      end;


fun string_of_clausename (cls_id,ax_name) = 
    clause_prefix ^ ascii_of ax_name ^ "_" ^ string_of_int cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (string_of_int idx);
    

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
  let val Predicate (predname, foltype, folterms) = pred
  in
      folterms
  end

 
fun get_uvars (UVar(a,typ)) = [a] 
|   get_uvars (Fun (_,typ,tlist)) = ResLib.flat_noDup(map get_uvars tlist)


fun is_uvar (UVar _) = true
|   is_uvar (Fun _) = false;

fun uvar_name (UVar(a,_)) = a
|   uvar_name (Fun (a,_,_)) = raise CLAUSE("Not a variable", Const(a,dummyT));

fun mergelist [] = []
|   mergelist (x::xs ) = x @ mergelist xs

fun dfg_vars (Clause cls) =
    let val lits = #literals cls
        val folterms = mergelist(map dfg_folterms lits)
    in 
        ResLib.flat_noDup(map get_uvars folterms)
    end


fun dfg_tvars (Clause cls) =(#tvars cls)


	
(* make this return funcs and preds too? *)
fun string_of_predname (Predicate("equal",typ,terms)) = "EQUALITY"
  | string_of_predname (Predicate(name,_,[])) = name 
  | string_of_predname (Predicate(name,typ,terms)) = name
    
	
(* make this return funcs and preds too? *)

fun string_of_predicate (Predicate("equal",typ,terms)) =  
      string_of_equality(typ,terms)
  | string_of_predicate (Predicate(name,_,[])) = name 
  | string_of_predicate (Predicate(name,typ,terms)) = 
      let val terms_as_strings = map string_of_term terms
      in
	  if !keep_types andalso typ<>""
	  then name ^ (ResLib.list_to_string  (terms_as_strings @ [typ]))
	  else name ^ (ResLib.list_to_string terms_as_strings) 
      end;


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

fun string_of_arity (name, num) =  name ^ "," ^ (string_of_int num) 

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

val delim = "\n";
val dfg_clauses2str = ResLib.list2str_sep delim; 
     

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
        val axstr = ResLib.list2str_sep delim axstrs
        val conjstrs_tfrees = (map clause2dfg conjectures)
	val (conjstrs, atfrees) = ListPair.unzip conjstrs_tfrees
        val tfree_clss = map tfree_dfg_clause (ResLib.flat_noDup atfrees) 
        val conjstr = ResLib.list2str_sep delim (tfree_clss@conjstrs)
        val funcstr = string_of_funcs funcs
        val predstr = string_of_preds preds
    in
       (string_of_start probname) ^ (string_of_descrip ()) ^ 
       (string_of_symbols funcstr predstr ) ^  
       (string_of_axioms axstr) ^
       (string_of_conjectures conjstr) ^ (string_of_end ())
    end;
   
fun clauses2dfg [] probname axioms conjectures funcs preds = 
      let val funcs' = (ResLib.flat_noDup(map funcs_of_cls axioms)) @ funcs
	  val preds' = (ResLib.flat_noDup(map preds_of_cls axioms)) @ preds
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
	 val funcs' = distinct((funcs_of_cls cls)@funcs)
	 val preds' = distinct((preds_of_cls cls)@preds)
	 val knd = string_of_kind cls
	 val lits_str = concat_with ", " lits
	 val axioms' = if knd = "axiom" then (cls::axioms) else axioms
	 val conjectures' = 
	     if knd = "conjecture" then (cls::conjectures) else conjectures
     in
	 clauses2dfg clss probname axioms' conjectures' funcs' preds' 
     end;


fun string_of_arClauseID (ArityClause arcls) =
    arclause_prefix ^ string_of_int(#clause_id arcls);

fun string_of_arLit (TConsLit(b,(c,t,args))) =
    let val pol = if b then "++" else "--"
	val arg_strs = (case args of [] => "" | _ => ResLib.list_to_string args)
    in 
	pol ^ c ^ "(" ^ t ^ arg_strs ^ ")"
    end
  | string_of_arLit (TVarLit(b,(c,str))) =
    let val pol = if b then "++" else "--"
    in
	pol ^ c ^ "(" ^ str ^ ")"
    end;
    

fun string_of_conclLit (ArityClause arcls) = string_of_arLit (#conclLit arcls);
     

fun strings_of_premLits (ArityClause arcls) = map string_of_arLit (#premLits arcls);
		

fun string_of_arKind (ArityClause arcls) = name_of_kind(#kind arcls);

(*FIX: would this have variables in a forall? *)

fun dfg_arity_clause arcls = 
    let val arcls_id = string_of_arClauseID arcls
	val concl_lit = string_of_conclLit arcls
	val prems_lits = strings_of_premLits arcls
	val knd = string_of_arKind arcls
	val all_lits = concl_lit :: prems_lits
    in

	"clause( %(" ^ knd ^ ")\n" ^  "or( " ^ (ResLib.list_to_string' all_lits) ^ ")),\n" ^
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
	val lits_str = ResLib.list_to_string' lits
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
	val lits_str = ResLib.list_to_string' lits
	val cls_str = gen_tptp_cls(cls_id,ax_name,knd,lits_str) 
    in
	(cls_str,tfree_lits) 
    end;


fun tfree_clause tfree_lit =
    "input_clause(" ^ "tfree_tcs," ^ "conjecture" ^ ",[" ^ tfree_lit ^ "]).";

val delim = "\n";
val tptp_clauses2str = ResLib.list2str_sep delim; 
     

fun string_of_arClauseID (ArityClause arcls) =
  arclause_prefix ^ string_of_int(#clause_id arcls);


fun string_of_arLit (TConsLit(b,(c,t,args))) =
    let val pol = if b then "++" else "--"
	val  arg_strs = (case args of [] => "" | _ => ResLib.list_to_string args)
    in 
	pol ^ c ^ "(" ^ t ^ arg_strs ^ ")"
    end
  | string_of_arLit (TVarLit(b,(c,str))) =
    let val pol = if b then "++" else "--"
    in
	pol ^ c ^ "(" ^ str ^ ")"
    end;
    

fun string_of_conclLit (ArityClause arcls) = string_of_arLit (#conclLit arcls);
     
fun strings_of_premLits (ArityClause arcls) =
 map string_of_arLit (#premLits arcls);
		

fun string_of_arKind (ArityClause arcls) = name_of_kind(#kind arcls);

fun tptp_arity_clause arcls = 
    let val arcls_id = string_of_arClauseID arcls
	val concl_lit = string_of_conclLit arcls
	val prems_lits = strings_of_premLits arcls
	val knd = string_of_arKind arcls
	val all_lits = concl_lit :: prems_lits
    in
	"input_clause(" ^ arcls_id ^ "," ^ knd ^ "," ^ 
	(ResLib.list_to_string' all_lits) ^ ")."
    end;

fun tptp_classrelLits sub sup = 
    let val tvar = "(T)"
    in 
	case sup of NONE => "[++" ^ sub ^ tvar ^ "]"
		  | (SOME supcls) =>  "[--" ^ sub ^ tvar ^ ",++" ^ supcls ^ tvar ^ "]"
    end;


fun tptp_classrelClause (ClassrelClause cls) =
    let val relcls_id = clrelclause_prefix ^ string_of_int(#clause_id cls)
	val sub = #subclass cls
	val sup = #superclass cls
	val lits = tptp_classrelLits sub sup
    in
	"input_clause(" ^ relcls_id ^ ",axiom," ^ lits ^ ")."
    end; 

end;
