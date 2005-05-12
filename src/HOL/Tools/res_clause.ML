(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ML data structure for storing/printing FOL clauses and arity clauses.
Typed equality is treated differently.
*)

signature RES_CLAUSE =
  sig
    exception ARCLAUSE of string
    exception CLAUSE of string
    type arityClause 
    type classrelClause
    val classrelClauses_of :
       string * string list -> classrelClause list
    type clause
    val keep_types : bool ref
    val make_axiom_arity_clause :
       string * (string * string list list) -> arityClause
    val make_axiom_classrelClause :
       string * string option -> classrelClause
    val make_axiom_clause : Term.term -> string * int -> clause
    val make_axiom_clause_thm : Thm.thm -> string * int -> clause
    val make_conjecture_clause : Term.term -> clause
    val make_conjecture_clause_thm : Thm.thm -> clause
    val make_hypothesis_clause : Term.term -> clause
    val make_hypothesis_clause_thm : Thm.thm -> clause
    val special_equal : bool ref
    val tptp_arity_clause : arityClause -> string
    val tptp_classrelClause : classrelClause -> string
    val tptp_clause : clause -> string list
    val tptp_clauses2str : string list -> string
    val typed : unit -> unit
    val untyped : unit -> unit
    val clause2tptp : clause -> string * string list
    val tfree_clause : string -> string
  end;

structure ResClause : RES_CLAUSE =
struct

(* Added for typed equality *)
val special_equal = ref false; (* by default,equality does not carry type information *)
val eq_typ_wrapper = "typeinfo"; (* default string *)


val schematic_var_prefix = "V_";
val fixed_var_prefix = "v_";


val tvar_prefix = "Typ_";
val tfree_prefix = "typ_";


val clause_prefix = "cls_"; 

val arclause_prefix = "arcls_" 

val const_prefix = "const_";
val tconst_prefix = "tconst_"; 

val class_prefix = "clas_"; 



(**** some useful functions ****)
 
val const_trans_table =
      Symtab.make [("op =", "equal"),
	  	   ("op <=", "lessequals"),
		   ("op <", "less"),
		   ("op &", "and"),
		   ("op |", "or"),
		   ("op -->", "implies"),
		   ("op :", "in"),
		   ("op Un", "union"),
		   ("op Int", "inter")];



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


(* another version of above functions that remove chars that may not be allowed by Vampire *)
fun make_schematic_var v = schematic_var_prefix ^ (ascii_of v);
fun make_fixed_var x = fixed_var_prefix ^ (ascii_of x);

fun make_schematic_type_var v = tvar_prefix ^ (ascii_of v);
fun make_fixed_type_var x = tfree_prefix ^ (ascii_of x);

fun make_fixed_const c = const_prefix ^ (ascii_of c);
fun make_fixed_type_const c = tconst_prefix ^ (ascii_of c);

fun make_type_class clas = class_prefix ^ (ascii_of clas);




fun lookup_const c =
    case Symtab.lookup (const_trans_table,c) of
        SOME c' => c'
      | NONE =>  make_fixed_const c;



(***** definitions and functions for FOL clauses, prepared for conversion into TPTP format or SPASS format. *****)

val keep_types = ref true; (* default is true *)
fun untyped () = (keep_types := false);
fun typed () = (keep_types := true);


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



fun string_of_indexname (name,index) = name ^ "_" ^ (string_of_int index);


val id_ref = ref 0;
fun generate_id () = 
     let val id = !id_ref
     in
	 (id_ref:=id + 1; id)
     end;



(**** Isabelle FOL clauses ****)

(* by default it is false *)
val tagged = ref false;

type pred_name = string;
type sort = Term.sort;
type fol_type = string;


datatype type_literal = LTVar of string | LTFree of string;


datatype folTerm = UVar of string * fol_type| Fun of string * fol_type * folTerm list;
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
                    tfree_type_literals: type_literal list };


exception CLAUSE of string;



(*** make clauses ***)


fun make_clause (clause_id,axiom_name,kind,literals,types_sorts,tvar_type_literals,tfree_type_literals) =
     Clause {clause_id = clause_id, axiom_name = axiom_name, kind = kind, literals = literals, types_sorts = types_sorts,tvar_type_literals = tvar_type_literals,tfree_type_literals = tfree_type_literals};



fun type_of (Type (a, [])) = (make_fixed_type_const a,[]) 
  | type_of (Type (a, Ts)) = 
    let val foltyps_ts = map type_of Ts
        val (folTyps,ts) = ListPair.unzip foltyps_ts
        val ts' = ResLib.flat_noDup ts
    in    
        (((make_fixed_type_const a) ^ (ResLib.list_to_string folTyps)),ts') 
    end
  | type_of (TFree (a, s)) = (make_fixed_type_var a, [((FOLTFree a),s)])
  | type_of (TVar (v, s))  = (make_schematic_type_var (string_of_indexname v), [((FOLTVar v),s)]);

(* added: checkMeta: string -> bool *)
(* Any meta vars like ?x should be treated as universal vars,although it is represented as "Free(...)" by Isabelle *)
fun checkMeta s =
    let val chars = explode s
    in
	["M", "E", "T", "A", "H", "Y", "P", "1"] prefix chars
    end;

    
fun pred_name_type (Const(c,T)) = (lookup_const c,type_of T)
  | pred_name_type (Free(x,T))  = 
    let val is_meta = checkMeta x
    in
	if is_meta then (raise CLAUSE("Predicate Not First Order")) else
	(make_fixed_var x,type_of T)
    end
  | pred_name_type (Var(_,_))   = raise CLAUSE("Predicate Not First Order")
  | pred_name_type _          = raise CLAUSE("Predicate input unexpected");


(* For type equality *)
(* here "arg_typ" is the type of "="'s argument's type, not the type of the equality *)
(* Find type of equality arg *)
fun eq_arg_type (Type("fun",[T,_])) = 
    let val (folT,_) = type_of T;
    in
	folT
    end;



fun fun_name_type (Const(c,T)) = (lookup_const c,type_of T)
  | fun_name_type (Free(x,T)) = (make_fixed_var x,type_of T)
  | fun_name_type _ = raise CLAUSE("Function Not First Order");
    


fun term_of (Var(ind_nm,T)) = 
    let val (folType,ts) = type_of T
    in
	(UVar(make_schematic_var(string_of_indexname ind_nm),folType),ts)
    end
  | term_of (Free(x,T)) = 
    let val is_meta = checkMeta x
	val (folType,ts) = type_of T
    in
	if is_meta then (UVar(make_schematic_var x,folType),ts)
	else
            (Fun(make_fixed_var x,folType,[]),ts)
    end
  | term_of (Const(c,T)) =  (* impossible to be equality *)
    let val (folType,ts) = type_of T
     in
        (Fun(lookup_const c,folType,[]),ts)
    end    
  | term_of (app as (t $ a)) = 
    let val (f,args) = strip_comb app
        fun term_of_aux () = 
            let val (funName,(funType,ts1)) = fun_name_type f
                 val (args',ts2) = ListPair.unzip (map term_of args)
                 val ts3 = ResLib.flat_noDup (ts1::ts2)
            in
		(Fun(funName,funType,args'),ts3)
            end
	fun term_of_eq ((Const ("op =", typ)),args) =
	    let val arg_typ = eq_arg_type typ
		val (args',ts) = ListPair.unzip (map term_of args)
		val equal_name = lookup_const ("op =")
	    in
		(Fun(equal_name,arg_typ,args'),ResLib.flat_noDup ts)
	    end
    in
        case f of Const ("op =", typ) => term_of_eq (f,args)
	        | Const(_,_) => term_of_aux ()
                | Free(s,_)  => if (checkMeta s) then (raise CLAUSE("Function Not First Order")) else term_of_aux ()
                | _          => raise CLAUSE("Function Not First Order")
    end
  | term_of _ = raise CLAUSE("Function Not First Order"); 




fun pred_of_eq ((Const ("op =", typ)),args) =
    let val arg_typ = eq_arg_type typ 
	val (args',ts) = ListPair.unzip (map term_of args)
	val equal_name = lookup_const "op ="
    in
	(Predicate(equal_name,arg_typ,args'),ResLib.flat_noDup ts)
    end;


(* changed for non-equality predicate *)
(* The input "pred" cannot be an equality *)
fun pred_of_nonEq (pred,args) = 
    let val (predName,(predType,ts1)) = pred_name_type pred
	val (args',ts2) = ListPair.unzip (map term_of args)
	val ts3 = ResLib.flat_noDup (ts1::ts2)
    in
	(Predicate(predName,predType,args'),ts3)
    end;


(* Changed for typed equality *)
(* First check if the predicate is an equality or not, then call different functions for equality and non-equalities *)
fun predicate_of term =
    let val (pred,args) = strip_comb term
    in
	case pred of (Const ("op =", _)) => pred_of_eq (pred,args)
		   | _ => pred_of_nonEq (pred,args)
    end;


 
fun literals_of_term ((Const("Trueprop",_) $ P),lits_ts) = literals_of_term(P,lits_ts)
  | literals_of_term ((Const("op |",_) $ P $ Q),(lits,ts)) = 
    let val (lits',ts') = literals_of_term(P,(lits,ts))
    in
        literals_of_term(Q,(lits',ts'))
    end
  | literals_of_term ((Const("Not",_) $ P),(lits,ts)) = 
    let val (pred,ts') = predicate_of P
        val lits' = Literal(false,pred,false) :: lits
        val ts'' = ResLib.no_rep_app ts ts'
    in
        (lits',ts'')
    end
  | literals_of_term (P,(lits,ts)) = 
    let val (pred,ts') = predicate_of P
        val lits' = Literal(true,pred,false) :: lits
        val ts'' = ResLib.no_rep_app ts ts' 
    in
        (lits',ts'')
    end;
     

fun literals_of_thm thm = literals_of_term (prop_of thm, ([],[]));
    
 
fun sorts_on_typs (_, []) = []
  | sorts_on_typs ((FOLTVar(indx)), [s]) = [LTVar((make_type_class s) ^ "(" ^ (make_schematic_type_var(string_of_indexname indx)) ^ ")")]
  | sorts_on_typs ((FOLTVar(indx)), (s::ss))=  LTVar((make_type_class s) ^ "(" ^ (make_schematic_type_var(string_of_indexname indx)) ^ ")") :: (sorts_on_typs ((FOLTVar(indx)), ss))
  | sorts_on_typs ((FOLTFree(x)), [s]) = [LTFree((make_type_class s) ^ "(" ^ (make_fixed_type_var(x)) ^ ")")]
  | sorts_on_typs ((FOLTFree(x)), (s::ss)) = LTFree((make_type_class s) ^ "(" ^ (make_fixed_type_var(x)) ^ ")") :: (sorts_on_typs ((FOLTFree(x)), ss));


fun add_typs_aux [] = ([],[])
  | add_typs_aux ((FOLTVar(indx),s)::tss) = 
    let val vs = sorts_on_typs (FOLTVar(indx),s)
        val (vss,fss) = add_typs_aux tss
    in
        (ResLib.no_rep_app vs vss,fss)
    end
  | add_typs_aux ((FOLTFree(x),s)::tss) =
    let val fs = sorts_on_typs (FOLTFree(x),s)
        val (vss,fss) = add_typs_aux tss
    in
        (vss,ResLib.no_rep_app fs fss)
    end;


fun add_typs (Clause cls) = 
    let val ts = #types_sorts cls
    in
	add_typs_aux ts
    end;    




(** make axiom clauses, hypothesis clauses and conjecture clauses. **)

local 
    fun replace_dot "." = "_"
      | replace_dot c = c;

in

fun proper_ax_name ax_name = 
    let val chars = explode ax_name
    in
	implode (map replace_dot chars)
    end;
end;

fun make_axiom_clause_thm thm (name,number)=
    let val (lits,types_sorts) = literals_of_thm thm
	val cls_id = number
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
	val ax_name = proper_ax_name name
    in 
	make_clause(cls_id,ax_name,Axiom,lits,types_sorts,tvar_lits,tfree_lits)
    end;
   
fun make_hypothesis_clause_thm thm =
    let val (lits,types_sorts) = literals_of_thm thm
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
    in
	make_clause(cls_id,"",Hypothesis,lits,types_sorts,tvar_lits,tfree_lits)
    end;


fun make_conjecture_clause_thm thm =
    let val (lits,types_sorts) = literals_of_thm thm
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
    in
	make_clause(cls_id,"",Conjecture,lits,types_sorts,tvar_lits,tfree_lits)
    end;


fun make_axiom_clause term (name,number)=
    let val (lits,types_sorts) = literals_of_term (term,([],[]))
	val cls_id = number
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
	val ax_name = proper_ax_name name
    in 
	make_clause(cls_id,ax_name,Axiom,lits,types_sorts,tvar_lits,tfree_lits)
    end;


fun make_hypothesis_clause term =
    let val (lits,types_sorts) = literals_of_term (term,([],[]))
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
    in
	make_clause(cls_id,"",Hypothesis,lits,types_sorts,tvar_lits,tfree_lits)
    end;
    
 
fun make_conjecture_clause term =
    let val (lits,types_sorts) = literals_of_term (term,([],[]))
	val cls_id = generate_id()
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
    in
	make_clause(cls_id,"",Conjecture,lits,types_sorts,tvar_lits,tfree_lits)
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



(***** convert clauses to tptp format *****)


fun string_of_clauseID (Clause cls) = clause_prefix ^ (string_of_int (#clause_id cls));


fun string_of_kind (Clause cls) = name_of_kind (#kind cls);

fun string_of_axiomName (Clause cls) = #axiom_name cls;

(****!!!! Changed for typed equality !!!!****)
fun wrap_eq_type typ t = eq_typ_wrapper ^"(" ^ t ^ "," ^ typ ^ ")";


(****!!!! Changed for typed equality !!!!****)
(* Only need to wrap equality's arguments with "typeinfo" if the output clauses are typed && if we specifically ask for types to be included.   *)
fun string_of_equality (typ,terms) =
    let val [tstr1,tstr2] = map string_of_term terms
    in
	if ((!keep_types) andalso (!special_equal)) then 
	    "equal(" ^ (wrap_eq_type typ tstr1) ^ "," ^ (wrap_eq_type typ tstr2) ^ ")"
	else
	    "equal(" ^ tstr1 ^ "," ^ tstr2 ^ ")"
    end


and
    string_of_term (UVar(x,_)) = x
  | string_of_term (Fun("equal",typ,terms)) = string_of_equality(typ,terms)
  | string_of_term (Fun (name,typ,[])) = name
  | string_of_term (Fun (name,typ,terms)) = 
    let val terms' = map string_of_term terms
    in
        if (!keep_types) then name ^ (ResLib.list_to_string (typ :: terms'))
        else name ^ (ResLib.list_to_string terms')
    end;



(* Changed for typed equality *)
(* before output the string of the predicate, check if the predicate corresponds to an equality or not. *)
fun string_of_predicate (Predicate("equal",typ,terms)) = string_of_equality(typ,terms)
  | string_of_predicate (Predicate(name,_,[])) = name 
  | string_of_predicate (Predicate(name,typ,terms)) = 
    let val terms_as_strings = map string_of_term terms
    in
        if (!keep_types) then name ^ (ResLib.list_to_string  (typ :: terms_as_strings))
        else name ^ (ResLib.list_to_string terms_as_strings) 
    end;

    


fun tptp_literal (Literal(pol,pred,tag)) =
    let val pred_string = string_of_predicate pred
	val tagged_pol = if (tag andalso !tagged) then (if pol then "+++" else "---")
                         else (if pol then "++" else "--")
     in
	tagged_pol ^ pred_string
    end;



fun tptp_of_typeLit (LTVar x) = "--" ^ x
  | tptp_of_typeLit (LTFree x) = "++" ^ x;
 

fun gen_tptp_cls (cls_id,ax_name,knd,lits) = 
    let val ax_str = (if ax_name = "" then "" else ("_" ^ ax_name))
    in
	"input_clause(" ^ cls_id ^ ax_str ^ "," ^ knd ^ "," ^ lits ^ ")."
    end;


fun gen_tptp_type_cls (cls_id,knd,tfree_lit,idx) = "input_clause(" ^ cls_id ^ "_tcs" ^ (string_of_int idx) ^ "," ^ knd ^ ",[" ^ tfree_lit ^ "]).";


fun tptp_clause_aux (Clause cls) = 
    let val lits = map tptp_literal (#literals cls)
	val tvar_lits_strs = if (!keep_types) then (map tptp_of_typeLit (#tvar_type_literals cls)) else []
	val tfree_lits = if (!keep_types) then (map tptp_of_typeLit (#tfree_type_literals cls)) else []
    in
	(tvar_lits_strs @ lits,tfree_lits)
    end; 


fun tptp_clause cls =
    let val (lits,tfree_lits) = tptp_clause_aux cls (*"lits" includes the typing assumptions (TVars)*)
	val cls_id = string_of_clauseID cls
	val ax_name = string_of_axiomName cls
	val knd = string_of_kind cls
	val lits_str = ResLib.list_to_string' lits
	val cls_str = gen_tptp_cls(cls_id,ax_name,knd,lits_str) 			fun typ_clss k [] = []
          | typ_clss k (tfree :: tfrees) = 
            (gen_tptp_type_cls(cls_id,knd,tfree,k)) ::  (typ_clss (k+1) tfrees)
    in 
	cls_str :: (typ_clss 0 tfree_lits)
    end;


fun clause2tptp cls =
    let val (lits,tfree_lits) = tptp_clause_aux cls (*"lits" includes the typing assumptions (TVars)*)
	val cls_id = string_of_clauseID cls
	val ax_name = string_of_axiomName cls
	val knd = string_of_kind cls
	val lits_str = ResLib.list_to_string' lits
	val cls_str = gen_tptp_cls(cls_id,ax_name,knd,lits_str) 
    in
	(cls_str,tfree_lits) 
    end;


fun tfree_clause tfree_lit = "input_clause(" ^ "tfree_tcs," ^ "conjecture" ^ ",[" ^ tfree_lit ^ "]).";

val delim = "\n";
val tptp_clauses2str = ResLib.list2str_sep delim; 
     

fun string_of_arClauseID (ArityClause arcls) = arclause_prefix ^ string_of_int(#clause_id arcls);


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
     

fun strings_of_premLits (ArityClause arcls) = map string_of_arLit (#premLits arcls);
		

fun string_of_arKind (ArityClause arcls) = name_of_kind(#kind arcls);

fun tptp_arity_clause arcls = 
    let val arcls_id = string_of_arClauseID arcls
	val concl_lit = string_of_conclLit arcls
	val prems_lits = strings_of_premLits arcls
	val knd = string_of_arKind arcls
	val all_lits = concl_lit :: prems_lits
    in
	"input_clause(" ^ arcls_id ^ "," ^ knd ^ "," ^ (ResLib.list_to_string' all_lits) ^ ")."
	
    end;


val clrelclause_prefix = "relcls_";


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
