(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ML data structure for storing/printing FOL clauses and arity clauses.
Typed equality is treated differently.
*)

signature RES_CLAUSE =
  sig
  exception CLAUSE of string * term
  type clause and arityClause and classrelClause
  type fol_type
  type typ_var
  type type_literal
  val add_typs_aux : (typ_var * string list) list -> type_literal list * type_literal list
  val arity_clause_thy: theory -> arityClause list 
  val ascii_of : string -> string
  val bracket_pack : string list -> string
  val check_var_pairs: ''a * ''b -> (''a * ''b) list -> int
  val classrel_clauses_thy: theory -> classrelClause list 
  val clause_eq : clause * clause -> bool
  val clause_prefix : string 
  val clause2tptp : clause -> string * string list
  val const_prefix : string
  val dfg_write_file: thm list -> string -> (clause list * classrelClause list * arityClause list) -> unit
  val fixed_var_prefix : string
  val gen_tptp_cls : int * string * string * string -> string
  val gen_tptp_type_cls : int * string * string * string * int -> string
  val get_axiomName : clause ->  string
  val hash_clause : clause -> int
  val init : theory -> unit
  val isMeta : string -> bool
  val isTaut : clause -> bool
  val keep_types : bool ref
  val list_ord : ('a * 'b -> order) -> 'a list * 'b list -> order
  val make_axiom_clause : Term.term -> string * int -> clause option
  val make_conjecture_clauses : term list -> clause list
  val make_fixed_const : string -> string		
  val make_fixed_type_const : string -> string   
  val make_fixed_type_var : string -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_schematic_var : string * int -> string
  val make_type_class : string -> string
  val mk_fol_type: string * string * fol_type list -> fol_type
  val mk_typ_var_sort : Term.typ -> typ_var * sort
  val paren_pack : string list -> string
  val schematic_var_prefix : string
  val special_equal : bool ref
  val string_of_fol_type : fol_type -> string
  val tconst_prefix : string 
  val tfree_prefix : string
  val tptp_arity_clause : arityClause -> string
  val tptp_classrelClause : classrelClause -> string
  val tptp_of_typeLit : type_literal -> string
  val tptp_tfree_clause : string -> string
  val tptp_write_file: thm list -> string -> (clause list * classrelClause list * arityClause list) -> unit
  val tvar_prefix : string
  val types_eq: fol_type list * fol_type list -> (string*string) list * (string*string) list -> bool * ((string*string) list * (string*string) list)
  val types_ord : fol_type list * fol_type list -> order
  val union_all : ''a list list -> ''a list
  val writeln_strs: TextIO.outstream -> TextIO.vector list -> unit
  end;

structure ResClause : RES_CLAUSE =
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
		   ("Divides.op div", "div"),
		   ("HOL.divide", "divide"),
		   ("op -->", "implies"),
		   ("{}", "emptyset"),
		   ("op :", "in"),
		   ("op Un", "union"),
		   ("op Int", "inter"),
		   ("List.op @", "append")];

val type_const_trans_table =
      Symtab.make [("*", "prod"),
	  	   ("+", "sum"),
		   ("~=>", "map")];

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

fun lookup_const c =
    case Symtab.lookup const_trans_table c of
        SOME c' => c'
      | NONE => ascii_of c;

fun lookup_type_const c = 
    case Symtab.lookup type_const_trans_table c of
        SOME c' => c'
      | NONE => ascii_of c;

fun make_fixed_const "op =" = "equal"   (*MUST BE "equal" because it's built-in to ATPs*)
  | make_fixed_const c      = const_prefix ^ lookup_const c;

fun make_fixed_type_const c = tconst_prefix ^ lookup_type_const c;

fun make_type_class clas = class_prefix ^ ascii_of clas;


(***** definitions and functions for FOL clauses, for conversion to TPTP or DFG format. *****)

val keep_types = ref true;

datatype kind = Axiom | Hypothesis | Conjecture;
fun name_of_kind Axiom = "axiom"
  | name_of_kind Hypothesis = "hypothesis"
  | name_of_kind Conjecture = "conjecture";

type clause_id = int;
type axiom_name = string;


type polarity = bool;

(* "tag" is used for vampire specific syntax FIXME REMOVE *)
type tag = bool; 


(**** Isabelle FOL clauses ****)

val tagged = ref false;

type pred_name = string;

datatype typ_var = FOLTVar of indexname | FOLTFree of string;

(*FIXME: give the constructors more sensible names*)
datatype fol_type = AtomV of string
		  | AtomF of string
		  | Comp of string * fol_type list;

fun string_of_fol_type (AtomV x) = x
  | string_of_fol_type (AtomF x) = x
  | string_of_fol_type (Comp(tcon,tps)) = 
      tcon ^ (paren_pack (map string_of_fol_type tps));
      
fun mk_fol_type ("Var",x,_) = AtomV(x)
  | mk_fol_type ("Fixed",x,_) = AtomF(x)
  | mk_fol_type ("Comp",con,args) = Comp(con,args)


(*First string is the type class; the second is a TVar or TFfree*)
datatype type_literal = LTVar of string * string | LTFree of string * string;

datatype fol_term = UVar of string * fol_type
                 | Fun of string * fol_type list * fol_term list;
datatype predicate = Predicate of pred_name * fol_type list * fol_term list;

datatype literal = Literal of polarity * predicate * tag;

fun mk_typ_var_sort (TFree(a,s)) = (FOLTFree a,s)
  | mk_typ_var_sort (TVar(v,s)) = (FOLTVar v,s);


(*A clause has first-order literals and other, type-related literals*)
datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    kind: kind,
		    literals: literal list,
		    types_sorts: (typ_var * sort) list};

fun get_axiomName (Clause cls) = #axiom_name cls;

exception CLAUSE of string * term;

fun isFalse (Literal (pol,Predicate(pname,_,[]),_)) =
      (pol andalso pname = "c_False") orelse
      (not pol andalso pname = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol,Predicate(pname,_,[]),_)) =
      (pol andalso pname = "c_True") orelse
      (not pol andalso pname = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  

fun make_clause (clause_id, axiom_name, kind, literals, types_sorts) =
  if forall isFalse literals 
  then error "Problem too trivial for resolution (empty clause)"
  else
     Clause {clause_id = clause_id, axiom_name = axiom_name, kind = kind, 
             literals = literals, types_sorts = types_sorts};


(*Declarations of the current theory--to allow suppressing types.*)
val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun num_typargs(s,T) = if !keep_types then length (!const_typargs (s,T)) else 0;

(*Initialize the type suppression mechanism with the current theory before
    producing any clauses!*)
fun init thy = (const_typargs := Sign.const_typargs thy);
    

(*Flatten a type to a fol_type while accumulating sort constraints on the TFrees and
  TVars it contains.*)    
fun type_of (Type (a, Ts)) = 
      let val (folTyps, ts) = types_of Ts 
	  val t = make_fixed_type_const a
      in (Comp(t,folTyps), ts) end
  | type_of (TFree (a,s)) = (AtomF(make_fixed_type_var a), [(FOLTFree a, s)]) 
  | type_of (TVar (v, s)) = (AtomV(make_schematic_type_var v), [(FOLTVar v, s)])
and types_of Ts =
      let val (folTyps,ts) = ListPair.unzip (map type_of Ts)
      in (folTyps, union_all ts) end;


fun const_types_of (c,T) = types_of (!const_typargs (c,T));

(* Any variables created via the METAHYPS tactical should be treated as
   universal vars, although it is represented as "Free(...)" by Isabelle *)
val isMeta = String.isPrefix "METAHYP1_"

fun pred_name_type (Const(c,T)) = (make_fixed_const c, const_types_of (c,T))
  | pred_name_type (Free(x,T))  = 
      if isMeta x then raise CLAUSE("Predicate Not First Order 1", Free(x,T)) 
      else (make_fixed_var x, ([],[]))
  | pred_name_type (v as Var _) = raise CLAUSE("Predicate Not First Order 2", v)
  | pred_name_type t        = raise CLAUSE("Predicate input unexpected", t);


(* For typed equality *)
(* here "arg_typ" is the type of "="'s argument's type, not the type of the equality *)
(* Find type of equality arg *)
fun eq_arg_type (Type("fun",[T,_])) = 
    let val (folT,_) = type_of T;
    in  folT  end;

fun fun_name_type (Const(c,T)) args = (make_fixed_const c, const_types_of (c,T))
  | fun_name_type (Free(x,T)) args  = 
       if isMeta x then raise CLAUSE("Function Not First Order", Free(x,T))
       else (make_fixed_var x, ([],[]))
  | fun_name_type f args = raise CLAUSE("Function Not First Order 1", f);

(*Convert a term to a fol_term while accumulating sort constraints on the TFrees and
  TVars it contains.*)    
fun term_of (Var(ind_nm,T)) = 
      let val (folType,ts) = type_of T
      in (UVar(make_schematic_var ind_nm, folType), ts) end
  | term_of (Free(x,T)) = 
      let val (folType, ts) = type_of T
      in
	  if isMeta x then (UVar(make_schematic_var(x,0),folType), ts)
	  else (Fun(make_fixed_var x, [folType], []), ts)
      end
  | term_of app = 
      let val (f,args) = strip_comb app
	  val (funName,(contys,ts1)) = fun_name_type f args
	  val (args',ts2) = terms_of args
      in
	  (Fun(funName,contys,args'), union_all (ts1::ts2))
      end
and terms_of ts = ListPair.unzip (map term_of ts)

(*Create a predicate value, again accumulating sort constraints.*)    
fun pred_of (Const("op =", typ), args) =
      let val arg_typ = eq_arg_type typ 
	  val (args',ts) = terms_of args
	  val equal_name = make_fixed_const "op ="
      in
	  (Predicate(equal_name,[arg_typ],args'),
	   union_all ts)
      end
  | pred_of (pred,args) = 
      let val (pname, (predType,ts1)) = pred_name_type pred
	  val (args',ts2) = terms_of args
      in
	  (Predicate(pname,predType,args'), union_all (ts1::ts2))
      end;

(*Treatment of literals, possibly negated or tagged*)
fun predicate_of ((Const("Not",_) $ P), polarity, tag) =
      predicate_of (P, not polarity, tag)
  | predicate_of ((Const("HOL.tag",_) $ P), polarity, tag) =
      predicate_of (P, polarity, true)
  | predicate_of (term,polarity,tag) =
        (pred_of (strip_comb term), polarity, tag);

fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 args (Const("op |",_) $ P $ Q) = 
      literals_of_term1 (literals_of_term1 args P) Q
  | literals_of_term1 (lits, ts) P =
      let val ((pred, ts'), polarity, tag) = predicate_of (P,true,false)
	  val lits' = Literal(polarity,pred,tag) :: lits
      in
	  (lits', ts union ts')
      end;

val literals_of_term = literals_of_term1 ([],[]);


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


fun term_ord (UVar _, UVar _) = EQUAL
  | term_ord (UVar _, _) = LESS
  | term_ord (Fun _, UVar _) = GREATER
  | term_ord (Fun(f1,tps1,tms1),Fun(f2,tps2,tms2)) = 
     (case string_ord (f1,f2) of
         EQUAL => 
	   (case terms_ord (tms1,tms2) of EQUAL => types_ord (tps1,tps2)
	      | tms_ord => tms_ord)
       | fn_ord => fn_ord)

and
      terms_ord ([],[]) = EQUAL
    | terms_ord (tms1,tms2) = list_ord term_ord (tms1,tms2);



fun predicate_ord (Predicate(pname1,ftyps1,ftms1),Predicate(pname2,ftyps2,ftms2)) = 
  case string_ord (pname1,pname2) of
       EQUAL => (case terms_ord(ftms1,ftms2) of EQUAL => types_ord(ftyps1,ftyps2)
				              | ftms_ord => ftms_ord)
     | pname_ord => pname_ord
			   

fun literal_ord (Literal(false,_,_),Literal(true,_,_)) = LESS
  | literal_ord (Literal(true,_,_),Literal(false,_,_)) = GREATER
  | literal_ord (Literal(_,pred1,_),Literal(_,pred2,_)) = predicate_ord(pred1,pred2);

fun sort_lits lits = sort literal_ord lits;


(********** clause equivalence ******************)

fun check_var_pairs (x,y) [] = 0 
  | check_var_pairs (x,y) ((u,v)::w) =
    if (x,y) = (u,v) then 1 
    else
	if (x = u) orelse (y = v) then 2 (*conflict*)
	else check_var_pairs (x,y) w;

fun type_eq (AtomV(v1),AtomV(v2)) (vars,tvars) =
    (case check_var_pairs (v1,v2) tvars of 0 => (true,(vars,(v1,v2)::tvars))
					 | 1 => (true,(vars,tvars))
					 | 2 => (false,(vars,tvars)))
  | type_eq (AtomV(_),_) vtvars = (false,vtvars)
  | type_eq (AtomF(f1),AtomF(f2)) vtvars = (f1=f2,vtvars)
  | type_eq (AtomF(_),_) vtvars = (false,vtvars)
  | type_eq (Comp(con1,args1),Comp(con2,args2)) vtvars =
      let val (eq1,vtvars1) = 
	      if con1 = con2 then types_eq (args1,args2) vtvars
	      else (false,vtvars)
      in
	  (eq1,vtvars1)
      end
  | type_eq (Comp(_,_),_) vtvars = (false,vtvars)

and

    types_eq ([],[]) vtvars = (true,vtvars)
  | types_eq (tp1::tps1,tp2::tps2) vtvars =
      let val (eq1,vtvars1) = type_eq (tp1,tp2) vtvars
	  val (eq2,vtvars2) = if eq1 then types_eq (tps1,tps2) vtvars1
			      else (eq1,vtvars1)
      in
	  (eq2,vtvars2)
      end;


fun term_eq (UVar(v1,tp1),UVar(v2,tp2)) (vars,tvars) =
    (case check_var_pairs (v1,v2) vars of 0 => type_eq (tp1,tp2) (((v1,v2)::vars),tvars)
					| 1 => type_eq (tp1,tp2) (vars,tvars)
					| 2 => (false,(vars,tvars)))
  | term_eq (UVar _,_) vtvars = (false,vtvars)
  | term_eq (Fun(f1,tps1,tms1),Fun(f2,tps2,tms2)) vtvars =
      let val (eq1,vtvars1) = 
	      if f1 = f2 then terms_eq (tms1,tms2) vtvars
	      else (false,vtvars)
	  val (eq2,vtvars2) =
	      if eq1 then types_eq (tps1,tps2) vtvars1
	      else (eq1,vtvars1)
      in
	  (eq2,vtvars2)
      end
  | term_eq (Fun(_,_,_),_) vtvars = (false,vtvars)

and

    terms_eq ([],[]) vtvars = (true,vtvars)
  | terms_eq (tm1::tms1,tm2::tms2) vtvars =
      let val (eq1,vtvars1) = term_eq (tm1,tm2) vtvars
	  val (eq2,vtvars2) = if eq1 then terms_eq (tms1,tms2) vtvars1
				     else (eq1,vtvars1)
      in
	  (eq2,vtvars2)
      end;
					     

fun pred_eq (Predicate(pname1,tps1,tms1),Predicate(pname2,tps2,tms2)) vtvars =
    let val (eq1,vtvars1) = 
	    if (pname1 = pname2) then terms_eq (tms1,tms2) vtvars
	    else (false,vtvars)
	val (eq2,vtvars2) = 
	    if eq1 then types_eq (tps1,tps2) vtvars1
	    else (eq1,vtvars1)
    in
	(eq2,vtvars2)
    end;
					      

fun lit_eq (Literal(pol1,pred1,_),Literal(pol2,pred2,_)) vtvars =
    if (pol1 = pol2) then pred_eq (pred1,pred2) vtvars
    else (false,vtvars);

(*must have the same number of literals*)
fun lits_eq ([],[]) vtvars = (true,vtvars)
  | lits_eq (l1::ls1,l2::ls2) vtvars = 
    let val (eq1,vtvars1) = lit_eq (l1,l2) vtvars
    in
	if eq1 then lits_eq (ls1,ls2) vtvars1
	else (false,vtvars1)
    end;


(*Equality of two clauses up to variable renaming*)
fun clause_eq (Clause{literals=lits1,...}, Clause{literals=lits2,...}) =
  length lits1 = length lits2 andalso #1 (lits_eq (lits1,lits2) ([],[]));


(*** Hash function for clauses ***)

val xor_words = List.foldl Word.xorb 0w0;

fun hashw_term (UVar _, w) = w
  | hashw_term (Fun(f,tps,args), w) = 
      List.foldl hashw_term (Polyhash.hashw_string (f,w)) args;
  
fun hashw_pred (Predicate(pn,_,args), w) = 
    List.foldl hashw_term (Polyhash.hashw_string (pn,w)) args;
    
fun hash1_literal (Literal(true,pred,_)) = hashw_pred (pred, 0w0)
  | hash1_literal (Literal(false,pred,_)) = Word.notb (hashw_pred (pred, 0w0));
  
fun hash_clause (Clause{literals,...}) =
  Word.toIntX (xor_words (map hash1_literal literals));


(*Make literals for sorted type variables.  FIXME: can it use map?*) 
fun sorts_on_typs (_, [])   = ([]) 
  | sorts_on_typs (v, "HOL.type" :: s) =
      sorts_on_typs (v,s)                (*IGNORE sort "type"*)
  | sorts_on_typs ((FOLTVar indx), s::ss) =
      LTVar(make_type_class s, make_schematic_type_var indx) :: 
      sorts_on_typs ((FOLTVar indx), ss)
  | sorts_on_typs ((FOLTFree x), s::ss) =
      LTFree(make_type_class s, make_fixed_type_var x) :: 
      sorts_on_typs ((FOLTFree x), ss);


fun pred_of_sort (LTVar (s,ty)) = (s,1)
|   pred_of_sort (LTFree (s,ty)) = (s,1)

(*Given a list of sorted type variables, return two separate lists.
  The first is for TVars, the second for TFrees.*)
fun add_typs_aux [] = ([],[])
  | add_typs_aux ((FOLTVar indx,s)::tss) = 
      let val vs = sorts_on_typs (FOLTVar indx, s)
	  val (vss,fss) = add_typs_aux tss
      in
	  (vs union vss, fss)
      end
  | add_typs_aux ((FOLTFree x,s)::tss) =
      let val fs = sorts_on_typs (FOLTFree x, s)
	  val (vss,fss) = add_typs_aux tss
      in
	  (vss, fs union fss)
      end;


(** make axiom and conjecture clauses. **)

fun get_tvar_strs [] = []
  | get_tvar_strs ((FOLTVar indx,s)::tss) = 
      (make_schematic_type_var indx) ins (get_tvar_strs tss)
  | get_tvar_strs((FOLTFree x,s)::tss) = get_tvar_strs tss

(* check if a clause is first-order before making a conjecture clause*)
fun make_conjecture_clause n t =
    let val _ = check_is_fol_term t
	    handle TERM("check_is_fol_term",_) => raise CLAUSE("Goal is not FOL",t)
	val (lits,types_sorts) = literals_of_term t
    in
	make_clause(n, "conjecture", Conjecture, lits, types_sorts)
    end;
    
fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (t::ts) =
      make_conjecture_clause n t :: make_conjecture_clauses_aux (n+1) ts

val make_conjecture_clauses = make_conjecture_clauses_aux 0

(** Too general means, positive equality literal with a variable X as one operand,
  when X does not occur properly in the other operand. This rules out clearly
  inconsistent clauses such as V=a|V=b, though it by no means guarantees soundness. **)

fun occurs a (UVar(b,_)) = a=b
  | occurs a (Fun (_,_,ts)) = exists (occurs a) ts

(*Is the first operand a variable that does not properly occur in the second operand?*)
fun too_general_terms (UVar _, UVar _) = false
  | too_general_terms (Fun _, _) = false
  | too_general_terms (UVar (a,_), t) = not (occurs a t);

fun too_general_lit (Literal (true,Predicate("equal",_,[x,y]),_)) =
      too_general_terms (x,y) orelse too_general_terms(y,x)
  | too_general_lit _ = false;

(*before converting an axiom clause to "clause" format, check if it is FOL*)
fun make_axiom_clause term (ax_name,cls_id) =
    let val _ = check_is_fol_term term 
	    handle TERM("check_is_fol_term",_) => raise CLAUSE("Axiom is not FOL", term) 
	val (lits,types_sorts) = literals_of_term term
    in 
	if forall too_general_lit lits then
	   (Output.debug ("Omitting " ^ ax_name ^ ": equalities are too general"); 
	    NONE)
	else SOME (make_clause(cls_id, ax_name, Axiom, sort_lits lits, types_sorts))
    end;


(**** Isabelle arities ****)

exception ARCLAUSE of string;
 
type class = string; 
type tcons = string; 

datatype arLit = TConsLit of bool * (class * tcons * string list)
               | TVarLit of bool * (class * string);
 
datatype arityClause =  
	 ArityClause of {clause_id: clause_id,
	  	         axiom_name: axiom_name,
			 kind: kind,
			 conclLit: arLit,
			 premLits: arLit list};


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort(tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =  (make_type_class cls, tvar) :: pack_sort(tvar, srt);
    
fun make_TVarLit (b, (cls,str)) = TVarLit(b, (cls,str));
fun make_TConsLit (b, (cls,tcons,tvars)) = 
      TConsLit(b, (make_type_class cls, make_fixed_type_const tcons, tvars));

(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause (tcons, n, (res,args)) =
   let val nargs = length args
       val tvars = gen_TVars nargs
       val tvars_srts = ListPair.zip (tvars,args)
       val tvars_srts' = union_all(map pack_sort tvars_srts)
       val false_tvars_srts' = map (pair false) tvars_srts'
   in
      ArityClause {clause_id = n, kind = Axiom, 
                   axiom_name = lookup_type_const tcons,
                   conclLit = make_TConsLit(true, (res,tcons,tvars)), 
                   premLits = map make_TVarLit false_tvars_srts'}
   end;


(**** Isabelle class relations ****)

datatype classrelClause = 
	 ClassrelClause of {axiom_name: axiom_name,
			    subclass: class,
			    superclass: class};

fun make_axiom_classrelClause n subclass superclass =
  ClassrelClause {axiom_name = clrelclause_prefix ^ ascii_of subclass ^ 
                                "_" ^ Int.toString n,
                  subclass = make_type_class subclass, 
                  superclass = make_type_class superclass};

fun classrelClauses_of_aux n sub [] = []
  | classrelClauses_of_aux n sub ("HOL.type"::sups) = (*Should be ignored*)
      classrelClauses_of_aux n sub sups
  | classrelClauses_of_aux n sub (sup::sups) =
      make_axiom_classrelClause n sub sup :: classrelClauses_of_aux (n+1) sub sups;

fun classrelClauses_of (sub,sups) = classrelClauses_of_aux 0 sub sups;

val classrel_of = #2 o #classes o Type.rep_tsig o Sign.tsig_of;

fun classrel_clauses_classrel (C: Sorts.classes) =
  map classrelClauses_of (Graph.dest C);

val classrel_clauses_thy = List.concat o classrel_clauses_classrel o classrel_of;


(** Isabelle arities **)

fun arity_clause _ (tcons, []) = []
  | arity_clause n (tcons, ("HOL.type",_)::ars) =  (*Should be ignored*)
      arity_clause n (tcons,ars)
  | arity_clause n (tcons, ar::ars) =
      make_axiom_arity_clause (tcons,n,ar) :: 
      arity_clause (n+1) (tcons,ars);

fun multi_arity_clause [] = []
  | multi_arity_clause (tcon_ar :: tcons_ars)  =
      arity_clause 0 tcon_ar  @  multi_arity_clause tcons_ars 

fun arity_clause_thy thy =
  let val arities = #arities (Type.rep_tsig (Sign.tsig_of thy))
  in multi_arity_clause (Symtab.dest arities) end;


(**** Find occurrences of predicates in clauses ****)

(*FIXME: multiple-arity checking doesn't work, as update_new is the wrong 
  function (it flags repeated declarations of a function, even with the same arity)*)

fun update_many (tab, keypairs) = foldl (uncurry Symtab.update) tab keypairs;

fun add_predicate_preds (Predicate(pname,tys,tms), preds) = 
  if pname = "equal" then preds (*equality is built-in and requires no declaration*)
  else Symtab.update (pname, length tys + length tms) preds

fun add_literal_preds (Literal(_,pred,_), preds) = add_predicate_preds (pred,preds)

fun add_type_sort_preds ((FOLTVar indx,s), preds) = 
      update_many (preds, map pred_of_sort (sorts_on_typs (FOLTVar indx, s)))
  | add_type_sort_preds ((FOLTFree x,s), preds) =
      update_many (preds, map pred_of_sort (sorts_on_typs (FOLTFree x, s)));

fun add_clause_preds (Clause {literals, types_sorts, ...}, preds) =
  foldl add_literal_preds (foldl add_type_sort_preds preds types_sorts) literals
  handle Symtab.DUP a => raise ERROR ("predicate " ^ a ^ " has multiple arities")

fun add_classrelClause_preds (ClassrelClause {subclass,superclass,...}, preds) =
  Symtab.update (subclass,1) (Symtab.update (superclass,1) preds);

fun add_arityClause_preds (ArityClause {conclLit,...}, preds) =
  let val TConsLit(_, (tclass, _, _)) = conclLit
  in  Symtab.update (tclass,1) preds  end;

fun preds_of_clauses clauses clsrel_clauses arity_clauses = 
  Symtab.dest
    (foldl add_classrelClause_preds 
      (foldl add_arityClause_preds
        (foldl add_clause_preds Symtab.empty clauses)
        arity_clauses)
      clsrel_clauses)

(*** Find occurrences of functions in clauses ***)

fun add_foltype_funcs (AtomV _, funcs) = funcs
  | add_foltype_funcs (AtomF a, funcs) = Symtab.update (a,0) funcs
  | add_foltype_funcs (Comp(a,tys), funcs) = 
      foldl add_foltype_funcs (Symtab.update (a, length tys) funcs) tys;

fun add_folterm_funcs (UVar _, funcs) = funcs
  | add_folterm_funcs (Fun(a,tys,[]), funcs) = Symtab.update (a,0) funcs
      (*A constant is a special case: it has no type argument even if overloaded*)
  | add_folterm_funcs (Fun(a,tys,tms), funcs) = 
      foldl add_foltype_funcs 
	    (foldl add_folterm_funcs (Symtab.update (a, length tys + length tms) funcs) 
	           tms) 
	    tys

fun add_predicate_funcs (Predicate(_,tys,tms), funcs) = 
    foldl add_foltype_funcs (foldl add_folterm_funcs funcs tms) tys;

fun add_literal_funcs (Literal(_,pred,_), funcs) = add_predicate_funcs (pred,funcs)

fun add_arityClause_funcs (ArityClause {conclLit,...}, funcs) =
  let val TConsLit(_, (_, tcons, tvars)) = conclLit
  in  Symtab.update (tcons, length tvars) funcs  end;

fun add_clause_funcs (Clause {literals, ...}, funcs) =
  foldl add_literal_funcs funcs literals
  handle Symtab.DUP a => raise ERROR ("function " ^ a ^ " has multiple arities")

fun funcs_of_clauses clauses arity_clauses = 
  Symtab.dest (foldl add_arityClause_funcs 
                     (foldl add_clause_funcs Symtab.empty clauses)
                     arity_clauses)


(**** String-oriented operations ****)

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
      in  name ^ (paren_pack (terms_as_strings @ typs'))  end;

(* before output the string of the predicate, check if the predicate corresponds to an equality or not. *)
fun string_of_predicate (Predicate("equal",[typ],terms)) = string_of_equality(typ,terms)
  | string_of_predicate (Predicate(name,typs,terms)) = 
      let val terms_as_strings = map string_of_term terms
	  val typs' = if !keep_types then map string_of_fol_type typs else []
      in  name ^ (paren_pack (terms_as_strings @ typs'))  end;

fun string_of_clausename (cls_id,ax_name) = 
    clause_prefix ^ ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);

(*Write a list of strings to a file*)
fun writeln_strs os = List.app (fn s => TextIO.output (os,s));

    
(**** Producing DFG files ****)

(*Attach sign in DFG syntax: false means negate.*)
fun dfg_sign true s = s
  | dfg_sign false s = "not(" ^ s ^ ")"  

fun dfg_literal (Literal(pol,pred,tag)) = dfg_sign pol (string_of_predicate pred)

fun dfg_of_typeLit (LTVar (s,ty)) = "not(" ^ s ^ "(" ^ ty ^ "))"
  | dfg_of_typeLit (LTFree (s,ty)) = s ^ "(" ^ ty ^ ")";
 
(*Enclose the clause body by quantifiers, if necessary*)
fun dfg_forall [] body = body  
  | dfg_forall vars body = "forall([" ^ commas vars ^ "],\n" ^ body ^ ")"

fun gen_dfg_cls (cls_id, ax_name, knd, lits, vars) = 
    "clause( %(" ^ knd ^ ")\n" ^ 
    dfg_forall vars ("or(" ^ lits ^ ")") ^ ",\n" ^ 
    string_of_clausename (cls_id,ax_name) ^  ").\n\n";

fun dfg_clause_aux (Clause{literals, types_sorts, ...}) = 
  let val lits = map dfg_literal literals
      val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
      val tvar_lits_strs = 
	  if !keep_types then map dfg_of_typeLit tvar_lits else []
      val tfree_lits =
          if !keep_types then map dfg_of_typeLit tfree_lits else []
  in
      (tvar_lits_strs @ lits, tfree_lits)
  end; 

fun dfg_folterms (Literal(pol,pred,tag)) = 
  let val Predicate (_, _, folterms) = pred
  in  folterms  end

fun get_uvars (UVar(a,typ)) = [a] 
  | get_uvars (Fun (_,typ,tlist)) = union_all(map get_uvars tlist)

fun dfg_vars (Clause {literals,...}) =
  union_all (map get_uvars (List.concat (map dfg_folterms literals)))

fun clause2dfg (cls as Clause{axiom_name,clause_id,kind,types_sorts,...}) =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
            (*"lits" includes the typing assumptions (TVars)*)
        val vars = dfg_vars cls
        val tvars = get_tvar_strs types_sorts
	val knd = name_of_kind kind
	val lits_str = commas lits
	val cls_str = gen_dfg_cls(clause_id, axiom_name, knd, lits_str, tvars@vars) 
    in (cls_str, tfree_lits) end;

fun string_of_arity (name, num) =  "(" ^ name ^ "," ^ Int.toString num ^ ")"

fun string_of_preds [] = ""
  | string_of_preds preds = "predicates[" ^ commas(map string_of_arity preds) ^ "].\n";

fun string_of_funcs [] = ""
  | string_of_funcs funcs = "functions[" ^ commas(map string_of_arity funcs) ^ "].\n" ;

fun string_of_symbols predstr funcstr = 
  "list_of_symbols.\n" ^ predstr  ^ funcstr  ^ "end_of_list.\n\n";

fun string_of_start name = "begin_problem(" ^ name ^ ").\n\n";

fun string_of_descrip name = 
  "list_of_descriptions.\nname({*" ^ name ^ 
  "*}).\nauthor({*Isabelle*}).\nstatus(unknown).\ndescription({*auto-generated*}).\nend_of_list.\n\n"

fun dfg_tfree_clause tfree_lit =
  "clause( %(conjecture)\n" ^ "or( " ^ tfree_lit ^ "),\n" ^ "tfree_tcs" ^ ").\n\n"

fun string_of_arClauseID (ArityClause {clause_id,axiom_name,...}) =
    arclause_prefix ^ ascii_of axiom_name ^ "_" ^ Int.toString clause_id;

fun dfg_of_arLit (TConsLit(pol,(c,t,args))) =
      dfg_sign pol (c ^ "(" ^ t ^ paren_pack args ^ ")")
  | dfg_of_arLit (TVarLit(pol,(c,str))) =
      dfg_sign pol (c ^ "(" ^ str ^ ")")
    
fun dfg_classrelLits sub sup = 
    let val tvar = "(T)"
    in 
	"not(" ^ sub ^ tvar ^ "), " ^ sup ^ tvar
    end;

fun dfg_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "clause(forall([T],\nor( " ^ dfg_classrelLits subclass superclass ^ ")),\n" ^
  axiom_name ^ ").\n\n";
      
fun dfg_arity_clause (arcls as ArityClause{kind,conclLit,premLits,...}) = 
  let val arcls_id = string_of_arClauseID arcls
      val knd = name_of_kind kind
      val TConsLit(_, (_,_,tvars)) = conclLit
      val lits = map dfg_of_arLit (conclLit :: premLits)
  in
      "clause( %(" ^ knd ^ ")\n" ^ 
      dfg_forall tvars ("or( " ^ commas lits ^ ")") ^ ",\n" ^
      arcls_id ^ ").\n\n"
  end;

(* write out a subgoal in DFG format to the file "xxxx_N"*)
fun dfg_write_file ths filename (axclauses,classrel_clauses,arity_clauses) = 
  let 
    val conjectures = make_conjecture_clauses (map prop_of ths)
    val (dfg_clss, tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
    val clss = conjectures @ axclauses
    val funcs = funcs_of_clauses clss arity_clauses
    and preds = preds_of_clauses clss classrel_clauses arity_clauses
    val out = TextIO.openOut filename
    and probname = Path.pack (Path.base (Path.unpack filename))
    val (axstrs, _) = ListPair.unzip (map clause2dfg axclauses)
    val tfree_clss = map dfg_tfree_clause (union_all tfree_litss) 
  in
    TextIO.output (out, string_of_start probname); 
    TextIO.output (out, string_of_descrip probname); 
    TextIO.output (out, string_of_symbols (string_of_funcs funcs) (string_of_preds preds)); 
    TextIO.output (out, "list_of_clauses(axioms,cnf).\n");
    writeln_strs out axstrs;
    List.app (curry TextIO.output out o dfg_classrelClause) classrel_clauses;
    List.app (curry TextIO.output out o dfg_arity_clause) arity_clauses;
    TextIO.output (out, "end_of_list.\n\nlist_of_clauses(conjectures,cnf).\n");
    writeln_strs out tfree_clss;
    writeln_strs out dfg_clss;
    TextIO.output (out, "end_of_list.\n\nend_problem.\n");
    TextIO.closeOut out
  end;


(**** Produce TPTP files ****)

(*Attach sign in TPTP syntax: false means negate.*)
fun tptp_sign true s = "++" ^ s
  | tptp_sign false s = "--" ^ s

fun tptp_literal (Literal(pol,pred,tag)) =  (*FIXME REMOVE TAGGING*)
    let val pred_string = string_of_predicate pred
	val tagged_pol = 
	      if (tag andalso !tagged) then (if pol then "+++" else "---")
	      else (if pol then "++" else "--")
     in
	tagged_pol ^ pred_string
    end;

fun tptp_of_typeLit (LTVar (s,ty)) = "--" ^ s ^ "(" ^ ty ^ ")"
  | tptp_of_typeLit (LTFree (s,ty)) = "++" ^ s ^ "(" ^ ty ^ ")";
 
fun gen_tptp_cls (cls_id,ax_name,knd,lits) = 
    "input_clause(" ^ string_of_clausename (cls_id,ax_name) ^ "," ^ 
    knd ^ "," ^ lits ^ ").\n";

fun gen_tptp_type_cls (cls_id,ax_name,knd,tfree_lit,idx) = 
    "input_clause(" ^ string_of_type_clsname (cls_id,ax_name,idx) ^ "," ^ 
    knd ^ ",[" ^ tfree_lit ^ "]).\n";

fun tptp_type_lits (Clause {literals, types_sorts, ...}) = 
    let val lits = map tptp_literal literals
	val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
        val tvar_lits_strs =
            if !keep_types then map tptp_of_typeLit tvar_lits else []
	val tfree_lits =
	    if !keep_types then map tptp_of_typeLit tfree_lits else []
    in
	(tvar_lits_strs @ lits, tfree_lits)
    end; 

fun clause2tptp (cls as Clause {clause_id, axiom_name, kind, ...}) =
    let val (lits,tfree_lits) = tptp_type_lits cls 
            (*"lits" includes the typing assumptions (TVars)*)
	val knd = name_of_kind kind
	val cls_str = gen_tptp_cls(clause_id, axiom_name, knd, bracket_pack lits) 
    in
	(cls_str,tfree_lits) 
    end;

fun tptp_tfree_clause tfree_lit =
    "input_clause(" ^ "tfree_tcs," ^ "conjecture" ^ ",[" ^ tfree_lit ^ "]).\n";

fun tptp_of_arLit (TConsLit(b,(c,t,args))) =
      tptp_sign b (c ^ "(" ^ t ^ paren_pack args ^ ")")
  | tptp_of_arLit (TVarLit(b,(c,str))) =
      tptp_sign b (c ^ "(" ^ str ^ ")")
    
fun tptp_arity_clause (arcls as ArityClause{kind,conclLit,premLits,...}) = 
  let val arcls_id = string_of_arClauseID arcls
      val knd = name_of_kind kind
      val lits = map tptp_of_arLit (conclLit :: premLits)
  in
    "input_clause(" ^ arcls_id ^ "," ^ knd ^ "," ^ bracket_pack lits ^ ").\n"
  end;

fun tptp_classrelLits sub sup = 
    let val tvar = "(T)"
    in 
	"[--" ^ sub ^ tvar ^ ",++" ^ sup ^ tvar ^ "]"
    end;

fun tptp_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "input_clause(" ^ axiom_name ^ ",axiom," ^ tptp_classrelLits subclass superclass ^ ").\n" 

(* write out a subgoal as tptp clauses to the file "xxxx_N"*)
fun tptp_write_file ths filename (axclauses,classrel_clauses,arity_clauses) =
  let
    val clss = make_conjecture_clauses (map prop_of ths)
    val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp clss)
    val tfree_clss = map tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
    val out = TextIO.openOut filename
  in
    List.app (curry TextIO.output out o #1 o clause2tptp) axclauses;
    writeln_strs out tfree_clss;
    writeln_strs out tptp_clss;
    List.app (curry TextIO.output out o tptp_classrelClause) classrel_clauses;
    List.app (curry TextIO.output out o tptp_arity_clause) arity_clauses;
    TextIO.closeOut out
  end;

end;
