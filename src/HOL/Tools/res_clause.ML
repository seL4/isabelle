(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ML data structure for storing/printing FOL clauses and arity clauses.
Typed equality is treated differently.
*)

(*FIXME: is this signature necessary? Or maybe define and open a Basic_ResClause?*)
signature RES_CLAUSE =
  sig
  exception CLAUSE of string * term
  type clause and arityClause and classrelClause
  datatype fol_type = AtomV of string
                    | AtomF of string
                    | Comp of string * fol_type list;
  datatype fol_term = UVar of string
                    | Fun of string * fol_type list * fol_term list;
  datatype predicate = Predicate of string * fol_type list * fol_term list;
  datatype kind = Axiom | Conjecture;
  val name_of_kind : kind -> string
  type typ_var and type_literal and literal
  val literals_of_term: Term.term -> literal list * (typ_var * Term.sort) list
  val add_typs_aux : (typ_var * string list) list -> type_literal list * type_literal list
  val ascii_of : string -> string
  val tptp_pack : string list -> string
  val make_arity_clauses: theory -> (class list * arityClause list)
  val make_classrel_clauses: theory -> class list -> class list -> classrelClause list 
  val clause_prefix : string 
  val clause2tptp : clause -> string * string list
  val const_prefix : string
  val dfg_write_file:  thm list -> string -> 
       ((thm * (string * int)) list * classrelClause list * arityClause list) -> string list
  val fixed_var_prefix : string
  val gen_tptp_cls : int * string * string * string list -> string
  val get_axiomName : clause ->  string
  val get_literals : clause -> literal list
  val init : theory -> unit
  val isMeta : string -> bool
  val isTaut : clause -> bool
  val list_ord : ('a * 'b -> order) -> 'a list * 'b list -> order
  val make_axiom_clause : thm -> string * int -> clause option
  val make_conjecture_clauses : thm list -> clause list
  val make_fixed_const : string -> string		
  val make_fixed_type_const : string -> string   
  val make_fixed_type_var : string -> string
  val make_fixed_var : string -> string
  val make_schematic_type_var : string * int -> string
  val make_schematic_var : string * int -> string
  val make_type_class : string -> string
  val mk_typ_var_sort : Term.typ -> typ_var * sort
  val paren_pack : string list -> string
  val schematic_var_prefix : string
  val string_of_fol_type : fol_type -> string
  val tconst_prefix : string 
  val tfree_prefix : string
  val tvar_prefix : string
  val tptp_arity_clause : arityClause -> string
  val tptp_classrelClause : classrelClause -> string
  val tptp_of_typeLit : type_literal -> string
  val tptp_tfree_clause : string -> string
  val tptp_write_file: thm list -> string -> 
       ((thm * (string * int)) list * classrelClause list * arityClause list) -> string list
  val union_all : ''a list list -> ''a list
  val writeln_strs: TextIO.outstream -> TextIO.vector list -> unit
  val dfg_sign: bool -> string -> string
  val dfg_of_typeLit: type_literal -> string
  val get_tvar_strs: (typ_var * sort) list -> string list
  val gen_dfg_cls: int * string * string * string * string list -> string
  val add_foltype_funcs: fol_type * int Symtab.table -> int Symtab.table
  val add_arityClause_funcs: arityClause * int Symtab.table -> int Symtab.table
  val add_arityClause_preds: arityClause * int Symtab.table -> int Symtab.table
  val add_classrelClause_preds : classrelClause * int Symtab.table -> int Symtab.table
  val dfg_tfree_clause : string -> string
  val string_of_start: string -> string
  val string_of_descrip : string -> string
  val string_of_symbols: string -> string -> string
  val string_of_funcs: (string * int) list -> string
  val string_of_preds: (string * Int.int) list -> string
  val dfg_classrelClause: classrelClause -> string
  val dfg_arity_clause: arityClause -> string
end;

structure ResClause =
struct

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
	  	   (@{const_name Orderings.less_eq}, "lessequals"),
		   (@{const_name Orderings.less}, "less"),
		   ("op &", "and"),
		   ("op |", "or"),
		   (@{const_name HOL.plus}, "plus"),
		   (@{const_name HOL.minus}, "minus"),
		   (@{const_name HOL.times}, "times"),
		   (@{const_name Divides.div}, "div"),
		   (@{const_name HOL.divide}, "divide"),
		   ("op -->", "implies"),
		   ("{}", "emptyset"),
		   ("op :", "in"),
		   ("op Un", "union"),
		   ("op Int", "inter"),
		   ("List.op @", "append"),
		   ("ATP_Linkup.fequal", "fequal"),
		   ("ATP_Linkup.COMBI", "COMBI"),
		   ("ATP_Linkup.COMBK", "COMBK"),
		   ("ATP_Linkup.COMBB", "COMBB"),
		   ("ATP_Linkup.COMBC", "COMBC"),
		   ("ATP_Linkup.COMBS", "COMBS"),
		   ("ATP_Linkup.COMBB'", "COMBB_e"),
		   ("ATP_Linkup.COMBC'", "COMBC_e"),
		   ("ATP_Linkup.COMBS'", "COMBS_e")];

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

(*TSTP format uses (...) rather than the old [...]*)
fun tptp_pack strings = "(" ^ space_implode " | " strings ^ ")";


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

datatype kind = Axiom | Conjecture;
fun name_of_kind Axiom = "axiom"
  | name_of_kind Conjecture = "negated_conjecture";

type clause_id = int;
type axiom_name = string;
type polarity = bool;

(**** Isabelle FOL clauses ****)

datatype typ_var = FOLTVar of indexname | FOLTFree of string;

(*FIXME: give the constructors more sensible names*)
datatype fol_type = AtomV of string
		  | AtomF of string
		  | Comp of string * fol_type list;

fun string_of_fol_type (AtomV x) = x
  | string_of_fol_type (AtomF x) = x
  | string_of_fol_type (Comp(tcon,tps)) = 
      tcon ^ (paren_pack (map string_of_fol_type tps));
      
(*First string is the type class; the second is a TVar or TFfree*)
datatype type_literal = LTVar of string * string | LTFree of string * string;

datatype fol_term = UVar of string
                  | Fun of string * fol_type list * fol_term list;
datatype predicate = Predicate of string * fol_type list * fol_term list;

datatype literal = Literal of polarity * predicate;

fun mk_typ_var_sort (TFree(a,s)) = (FOLTFree a,s)
  | mk_typ_var_sort (TVar(v,s)) = (FOLTVar v,s);


(*A clause has first-order literals and other, type-related literals*)
datatype clause = 
	 Clause of {clause_id: clause_id,
		    axiom_name: axiom_name,
		    th: thm,
		    kind: kind,
		    literals: literal list,
		    types_sorts: (typ_var * sort) list};

fun get_axiomName (Clause cls) = #axiom_name cls;

fun get_literals (Clause cls) = #literals cls;

exception CLAUSE of string * term;

fun isFalse (Literal (pol, Predicate(pname,_,[]))) =
      (pol andalso pname = "c_False") orelse
      (not pol andalso pname = "c_True")
  | isFalse _ = false;

fun isTrue (Literal (pol, Predicate(pname,_,[]))) =
      (pol andalso pname = "c_True") orelse
      (not pol andalso pname = "c_False")
  | isTrue _ = false;
  
fun isTaut (Clause {literals,...}) = exists isTrue literals;  


(*Declarations of the current theory--to allow suppressing types.*)
val const_typargs = ref (Library.K [] : (string*typ -> typ list));

fun num_typargs(s,T) = length (!const_typargs (s,T));

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

fun fun_name_type (Const(c,T)) args = (make_fixed_const c, const_types_of (c,T))
  | fun_name_type (Free(x,T)) args  = 
       if isMeta x then raise CLAUSE("Function Not First Order", Free(x,T))
       else (make_fixed_var x, ([],[]))
  | fun_name_type f args = raise CLAUSE("Function Not First Order 1", f);

(*Convert a term to a fol_term while accumulating sort constraints on the TFrees and
  TVars it contains.*)    
fun term_of (Var(ind_nm,T)) = 
      let val (_,ts) = type_of T
      in (UVar(make_schematic_var ind_nm), ts) end
  | term_of (Free(x,T)) = 
      let val (_,ts) = type_of T
      in
	  if isMeta x then (UVar(make_schematic_var(x,0)), ts)
	  else (Fun(make_fixed_var x, [], []), ts)
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
      let val (args',ts) = terms_of args
      in
	  (Predicate(make_fixed_const "op =", [], args'),
	   union_all ts)
      end
  | pred_of (pred,args) = 
      let val (pname, (predType,ts1)) = pred_name_type pred
	  val (args',ts2) = terms_of args
      in
	  (Predicate(pname,predType,args'), union_all (ts1::ts2))
      end;

(*Treatment of literals, possibly negated*)
fun predicate_of ((Const("Not",_) $ P), polarity) = predicate_of (P, not polarity)
  | predicate_of (term,polarity) = (pred_of (strip_comb term), polarity);

fun literals_of_term1 args (Const("Trueprop",_) $ P) = literals_of_term1 args P
  | literals_of_term1 args (Const("op |",_) $ P $ Q) = 
      literals_of_term1 (literals_of_term1 args P) Q
  | literals_of_term1 (lits, ts) P =
      let val ((pred, ts'), polarity) = predicate_of (P,true)
	  val lits' = Literal(polarity,pred) :: lits
      in
	  (lits', ts union ts')
      end;

val literals_of_term = literals_of_term1 ([],[]);


fun list_ord _ ([],[]) = EQUAL
  | list_ord _ ([],_) = LESS
  | list_ord _ (_,[]) = GREATER
  | list_ord ord (x::xs, y::ys) = 
      (case ord(x,y) of EQUAL => list_ord ord (xs,ys)
	 	      | xy_ord => xy_ord);
		     
(*Make literals for sorted type variables*) 
fun sorts_on_typs (_, [])   = []
  | sorts_on_typs (v,  s::ss) = 
      let val sorts = sorts_on_typs (v, ss)
      in
          if s = "HOL.type" then sorts
          else case v of
              FOLTVar indx => LTVar(make_type_class s, make_schematic_type_var indx) :: sorts
            | FOLTFree x => LTFree(make_type_class s, make_fixed_type_var x) :: sorts
      end;

fun pred_of_sort (LTVar (s,ty)) = (s,1)
  | pred_of_sort (LTFree (s,ty)) = (s,1)

(*Given a list of sorted type variables, return two separate lists.
  The first is for TVars, the second for TFrees.*)
fun add_typs_aux [] = ([],[])
  | add_typs_aux ((FOLTVar indx, s) :: tss) = 
      let val vs = sorts_on_typs (FOLTVar indx, s)
	  val (vss,fss) = add_typs_aux tss
      in
	  (vs union vss, fss)
      end
  | add_typs_aux ((FOLTFree x, s) :: tss) =
      let val fs = sorts_on_typs (FOLTFree x, s)
	  val (vss,fss) = add_typs_aux tss
      in
	  (vss, fs union fss)
      end;


(** make axiom and conjecture clauses. **)

exception MAKE_CLAUSE;
fun make_clause (clause_id, axiom_name, th, kind) =
  let val (lits,types_sorts) = literals_of_term (prop_of th)
  in if forall isFalse lits 
     then error "Problem too trivial for resolution (empty clause)"
     else Clause {clause_id = clause_id, axiom_name = axiom_name, th = th, 
                  kind = kind, literals = lits, types_sorts = types_sorts}
  end;		     

fun get_tvar_strs [] = []
  | get_tvar_strs ((FOLTVar indx,s)::tss) = 
      insert (op =) (make_schematic_type_var indx) (get_tvar_strs tss)
  | get_tvar_strs((FOLTFree x,s)::tss) = get_tvar_strs tss

(* check if a clause is first-order before making a conjecture clause*)
fun make_conjecture_clause n th =
  if Meson.is_fol_term (theory_of_thm th) (prop_of th) 
  then make_clause(n, "conjecture", th, Conjecture)
  else raise CLAUSE("Goal is not FOL", prop_of th);
  
fun make_conjecture_clauses_aux _ [] = []
  | make_conjecture_clauses_aux n (t::ts) =
      make_conjecture_clause n t :: make_conjecture_clauses_aux (n+1) ts

val make_conjecture_clauses = make_conjecture_clauses_aux 0

(*before converting an axiom clause to "clause" format, check if it is FOL*)
fun make_axiom_clause th (ax_name,cls_id) =
  if Meson.is_fol_term (theory_of_thm th) (prop_of th) 
  then (SOME (make_clause(cls_id, ax_name, th, Axiom)) handle MAKE_CLAUSE => NONE)
  else (Output.debug (fn () => ("Omitting " ^ ax_name ^ ": Axiom is not FOL")); NONE)
    
fun make_axiom_clauses [] = []
  | make_axiom_clauses ((th,(name,id))::thms) =
      case make_axiom_clause th (name,id) of 
          SOME cls => if isTaut cls then make_axiom_clauses thms 
                      else (name,cls) :: make_axiom_clauses thms
        | NONE => make_axiom_clauses thms;

(**** Isabelle arities ****)

exception ARCLAUSE of string;
 
type class = string; 
type tcons = string; 

datatype arLit = TConsLit of class * tcons * string list
               | TVarLit of class * string;
 
datatype arityClause =  
	 ArityClause of {axiom_name: axiom_name,
			 kind: kind,
			 conclLit: arLit,
			 premLits: arLit list};


fun gen_TVars 0 = []
  | gen_TVars n = ("T_" ^ Int.toString n) :: gen_TVars (n-1);

fun pack_sort(_,[])  = []
  | pack_sort(tvar, "HOL.type"::srt) = pack_sort(tvar, srt)   (*IGNORE sort "type"*)
  | pack_sort(tvar, cls::srt) =  (cls, tvar) :: pack_sort(tvar, srt);
    
(*Arity of type constructor tcon :: (arg1,...,argN)res*)
fun make_axiom_arity_clause (tcons, axiom_name, (cls,args)) =
   let val tvars = gen_TVars (length args)
       val tvars_srts = ListPair.zip (tvars,args)
   in
      ArityClause {axiom_name = axiom_name, kind = Axiom, 
                   conclLit = TConsLit (cls, make_fixed_type_const tcons, tvars), 
                   premLits = map TVarLit (union_all(map pack_sort tvars_srts))}
   end;


(**** Isabelle class relations ****)

datatype classrelClause = 
	 ClassrelClause of {axiom_name: axiom_name,
			    subclass: class,
			    superclass: class};
 
(*Generate all pairs (sub,super) such that sub is a proper subclass of super in theory thy.*)
fun class_pairs thy [] supers = []
  | class_pairs thy subs supers =
      let val class_less = Sorts.class_less(Sign.classes_of thy)
	  fun add_super sub (super,pairs) = 
		if class_less (sub,super) then (sub,super)::pairs else pairs
	  fun add_supers (sub,pairs) = foldl (add_super sub) pairs supers
      in  foldl add_supers [] subs  end;

fun make_classrelClause (sub,super) =
  ClassrelClause {axiom_name = clrelclause_prefix ^ ascii_of sub ^ "_" ^ ascii_of super,
                  subclass = make_type_class sub, 
                  superclass = make_type_class super};

fun make_classrel_clauses thy subs supers =
  map make_classrelClause (class_pairs thy subs supers);


(** Isabelle arities **)

fun arity_clause _ _ (tcons, []) = []
  | arity_clause seen n (tcons, ("HOL.type",_)::ars) =  (*ignore*)
      arity_clause seen n (tcons,ars)
  | arity_clause seen n (tcons, (ar as (class,_)) :: ars) =
      if class mem_string seen then (*multiple arities for the same tycon, class pair*)
	  make_axiom_arity_clause (tcons, lookup_type_const tcons ^ "_" ^ class ^ "_" ^ Int.toString n, ar) :: 
	  arity_clause seen (n+1) (tcons,ars)
      else
	  make_axiom_arity_clause (tcons, lookup_type_const tcons ^ "_" ^ class, ar) :: 
	  arity_clause (class::seen) n (tcons,ars)

fun multi_arity_clause [] = []
  | multi_arity_clause ((tcons,ars) :: tc_arlists) =
      arity_clause [] 1 (tcons, ars)  @  multi_arity_clause tc_arlists 

(*Generate all pairs (tycon,class,sorts) such that tycon belongs to class in theory thy
  provided its arguments have the corresponding sorts.*)
fun type_class_pairs thy tycons classes =
  let val alg = Sign.classes_of thy
      fun domain_sorts (tycon,class) = Sorts.mg_domain alg tycon [class]
      fun add_class tycon (class,pairs) = 
            (class, domain_sorts(tycon,class))::pairs 
            handle Sorts.CLASS_ERROR _ => pairs
      fun try_classes tycon = (tycon, foldl (add_class tycon) [] classes)
  in  map try_classes tycons  end;

(*Proving one (tycon, class) membership may require proving others, so iterate.*)
fun iter_type_class_pairs thy tycons [] = ([], [])
  | iter_type_class_pairs thy tycons classes =
      let val cpairs = type_class_pairs thy tycons classes
          val newclasses = union_all (union_all (union_all (map (map #2 o #2) cpairs))) \\ classes \\ HOLogic.typeS
          val _ = if null newclasses then () 
                  else Output.debug (fn _ => "New classes: " ^ space_implode ", " newclasses)
          val (classes', cpairs') = iter_type_class_pairs thy tycons newclasses  
      in  (classes' union classes, cpairs' union cpairs)  end;
      
fun make_arity_clauses thy tycons classes =
  let val (classes', cpairs) = iter_type_class_pairs thy tycons classes  
  in  (classes', multi_arity_clause cpairs)  end;


(**** Find occurrences of predicates in clauses ****)

(*FIXME: multiple-arity checking doesn't work, as update_new is the wrong 
  function (it flags repeated declarations of a function, even with the same arity)*)

fun update_many (tab, keypairs) = foldl (uncurry Symtab.update) tab keypairs;

fun add_predicate_preds (Predicate(pname,tys,tms), preds) = 
  if pname = "equal" then preds (*equality is built-in and requires no declaration*)
  else Symtab.update (pname, length tys + length tms) preds

fun add_literal_preds (Literal(_,pred), preds) = add_predicate_preds (pred,preds)

fun add_type_sort_preds ((FOLTVar indx,s), preds) = 
      update_many (preds, map pred_of_sort (sorts_on_typs (FOLTVar indx, s)))
  | add_type_sort_preds ((FOLTFree x,s), preds) =
      update_many (preds, map pred_of_sort (sorts_on_typs (FOLTFree x, s)));

fun add_clause_preds (Clause {literals, types_sorts, ...}, preds) =
  foldl add_literal_preds (foldl add_type_sort_preds preds types_sorts) literals
  handle Symtab.DUP a => raise ERROR ("predicate " ^ a ^ " has multiple arities")

fun add_classrelClause_preds (ClassrelClause {subclass,superclass,...}, preds) =
  Symtab.update (subclass,1) (Symtab.update (superclass,1) preds);

fun class_of_arityLit (TConsLit (tclass, _, _)) = tclass
  | class_of_arityLit (TVarLit (tclass, _)) = tclass;

fun add_arityClause_preds (ArityClause {conclLit,premLits,...}, preds) =
  let val classes = map (make_type_class o class_of_arityLit) (conclLit::premLits)
      fun upd (class,preds) = Symtab.update (class,1) preds
  in  foldl upd preds classes  end;

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
  | add_folterm_funcs (Fun(a,tys,tms), funcs) = 
      foldl add_foltype_funcs 
	    (foldl add_folterm_funcs (Symtab.update (a, length tys + length tms) funcs) 
	           tms) 
	    tys

fun add_predicate_funcs (Predicate(_,tys,tms), funcs) = 
    foldl add_foltype_funcs (foldl add_folterm_funcs funcs tms) tys;

fun add_literal_funcs (Literal(_,pred), funcs) = add_predicate_funcs (pred,funcs)

(*TFrees are recorded as constants*)
fun add_type_sort_funcs ((FOLTVar _, _), funcs) = funcs
  | add_type_sort_funcs ((FOLTFree a, _), funcs) = 
      Symtab.update (make_fixed_type_var a, 0) funcs

fun add_arityClause_funcs (ArityClause {conclLit,...}, funcs) =
  let val TConsLit (_, tcons, tvars) = conclLit
  in  Symtab.update (tcons, length tvars) funcs  end;

fun add_clause_funcs (Clause {literals, types_sorts, ...}, funcs) =
  foldl add_literal_funcs (foldl add_type_sort_funcs funcs types_sorts)
       literals
  handle Symtab.DUP a => raise ERROR ("function " ^ a ^ " has multiple arities")

fun funcs_of_clauses clauses arity_clauses = 
  Symtab.dest (foldl add_arityClause_funcs 
                     (foldl add_clause_funcs Symtab.empty clauses)
                     arity_clauses)


(**** String-oriented operations ****)

fun string_of_term (UVar x) = x
  | string_of_term (Fun (name,typs,terms)) = 
      name ^ (paren_pack (map string_of_term terms @ map string_of_fol_type typs));

fun string_of_pair [t1,t2] = (string_of_term t1, string_of_term t2)
  | string_of_pair _ = raise ERROR ("equality predicate requires two arguments");

fun string_of_equality ts =
  let val (s1,s2) = string_of_pair ts
  in "equal(" ^ s1 ^ "," ^ s2 ^ ")" end;

(* before output the string of the predicate, check if the predicate corresponds to an equality or not. *)
fun string_of_predicate (Predicate("equal",_,ts)) = string_of_equality ts
  | string_of_predicate (Predicate(name,typs,ts)) = 
      name ^ (paren_pack (map string_of_term ts @ map string_of_fol_type typs));

fun string_of_clausename (cls_id,ax_name) = 
    clause_prefix ^ ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun clause_name_of (cls_id,ax_name) = 
    ascii_of ax_name ^ "_" ^ Int.toString cls_id;

fun string_of_type_clsname (cls_id,ax_name,idx) = 
    string_of_clausename (cls_id,ax_name) ^ "_tcs" ^ (Int.toString idx);

(*Write a list of strings to a file*)
fun writeln_strs os = List.app (fn s => TextIO.output (os,s));

    
(**** Producing DFG files ****)

(*Attach sign in DFG syntax: false means negate.*)
fun dfg_sign true s = s
  | dfg_sign false s = "not(" ^ s ^ ")"  

fun dfg_literal (Literal(pol,pred)) = dfg_sign pol (string_of_predicate pred)

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
  let val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
  in  (map dfg_of_typeLit tvar_lits @ map dfg_literal literals, 
       map dfg_of_typeLit tfree_lits)
  end; 

fun dfg_folterms (Literal(pol,pred)) = 
  let val Predicate (_, _, folterms) = pred
  in  folterms  end

fun get_uvars (UVar a) = [a] 
  | get_uvars (Fun (_,typ,tlist)) = union_all(map get_uvars tlist)

fun dfg_vars (Clause {literals,...}) =
  union_all (map get_uvars (List.concat (map dfg_folterms literals)))

fun clause2dfg (cls as Clause{axiom_name,clause_id,kind,types_sorts,...}) =
    let val (lits,tfree_lits) = dfg_clause_aux cls 
            (*"lits" includes the typing assumptions (TVars)*)
        val vars = dfg_vars cls
        val tvars = get_tvar_strs types_sorts
	val cls_str = gen_dfg_cls(clause_id, axiom_name, name_of_kind kind, 
	                           commas lits, tvars@vars) 
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
  "clause( %(negated_conjecture)\n" ^ "or( " ^ tfree_lit ^ "),\n" ^ "tfree_tcs" ^ ").\n\n"

fun dfg_of_arLit (TConsLit (c,t,args)) =
      dfg_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | dfg_of_arLit (TVarLit (c,str)) =
      dfg_sign false (make_type_class c ^ "(" ^ str ^ ")")
    
fun dfg_classrelLits sub sup =  "not(" ^ sub ^ "(T)), " ^ sup ^ "(T)";

fun dfg_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "clause(forall([T],\nor( " ^ dfg_classrelLits subclass superclass ^ ")),\n" ^
  axiom_name ^ ").\n\n";
      
fun string_of_ar axiom_name = arclause_prefix ^ ascii_of axiom_name;

fun dfg_arity_clause (ArityClause{axiom_name,kind,conclLit,premLits,...}) = 
  let val TConsLit (_,_,tvars) = conclLit
      val lits = map dfg_of_arLit (conclLit :: premLits)
  in
      "clause( %(" ^ name_of_kind kind ^ ")\n" ^ 
      dfg_forall tvars ("or( " ^ commas lits ^ ")") ^ ",\n" ^
      string_of_ar axiom_name ^ ").\n\n"
  end;

(* write out a subgoal in DFG format to the file "xxxx_N"*)
fun dfg_write_file thms filename (ax_tuples,classrel_clauses,arity_clauses) = 
  let 
    val _ = Output.debug (fn () => ("Preparing to write the DFG file " ^ filename))
    val conjectures = make_conjecture_clauses thms
    val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses ax_tuples)
    val (dfg_clss, tfree_litss) = ListPair.unzip (map clause2dfg conjectures)
    val clss = conjectures @ axclauses
    val funcs = funcs_of_clauses clss arity_clauses
    and preds = preds_of_clauses clss classrel_clauses arity_clauses
    and probname = Path.implode (Path.base (Path.explode filename))
    val (axstrs, _) = ListPair.unzip (map clause2dfg axclauses)
    val tfree_clss = map dfg_tfree_clause (union_all tfree_litss) 
    val out = TextIO.openOut filename
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
    TextIO.closeOut out;
    clnames
  end;


(**** Produce TPTP files ****)

(*Attach sign in TPTP syntax: false means negate.*)
fun tptp_sign true s = s
  | tptp_sign false s = "~ " ^ s

fun tptp_of_equality pol ts =
  let val (s1,s2) = string_of_pair ts
      val eqop = if pol then " = " else " != "
  in  s1 ^ eqop ^ s2  end;

fun tptp_literal (Literal(pol,Predicate("equal",_,ts))) = tptp_of_equality pol ts
  | tptp_literal (Literal(pol,pred)) = tptp_sign pol (string_of_predicate pred);

fun tptp_of_typeLit (LTVar (s,ty))  = tptp_sign false (s ^ "(" ^ ty ^ ")")
  | tptp_of_typeLit (LTFree (s,ty)) = tptp_sign true  (s ^ "(" ^ ty ^ ")");
 
fun gen_tptp_cls (cls_id,ax_name,knd,lits) = 
    "cnf(" ^ string_of_clausename (cls_id,ax_name) ^ "," ^ 
    name_of_kind knd ^ "," ^ tptp_pack lits ^ ").\n";

fun tptp_type_lits (Clause {literals, types_sorts, ...}) = 
  let val (tvar_lits,tfree_lits) = add_typs_aux types_sorts
  in
      (map tptp_of_typeLit tvar_lits @ map tptp_literal literals,
       map tptp_of_typeLit tfree_lits)
  end; 

fun clause2tptp (cls as Clause {clause_id, axiom_name, kind, ...}) =
    let val (lits,tfree_lits) = tptp_type_lits cls 
            (*"lits" includes the typing assumptions (TVars)*)
	val cls_str = gen_tptp_cls(clause_id, axiom_name, kind, lits) 
    in
	(cls_str,tfree_lits) 
    end;

fun tptp_tfree_clause tfree_lit =
    "cnf(" ^ "tfree_tcs," ^ "negated_conjecture" ^ "," ^ tptp_pack[tfree_lit] ^ ").\n";
    
fun tptp_of_arLit (TConsLit (c,t,args)) =
      tptp_sign true (make_type_class c ^ "(" ^ t ^ paren_pack args ^ ")")
  | tptp_of_arLit (TVarLit (c,str)) =
      tptp_sign false (make_type_class c ^ "(" ^ str ^ ")")
    
fun tptp_arity_clause (ArityClause{axiom_name,kind,conclLit,premLits,...}) = 
  "cnf(" ^ string_of_ar axiom_name ^ "," ^ name_of_kind kind ^ "," ^ 
  tptp_pack (map tptp_of_arLit (conclLit :: premLits)) ^ ").\n";

fun tptp_classrelLits sub sup = 
  let val tvar = "(T)"
  in  tptp_pack [tptp_sign false (sub^tvar), tptp_sign true (sup^tvar)]  end;

fun tptp_classrelClause (ClassrelClause {axiom_name,subclass,superclass,...}) =
  "cnf(" ^ axiom_name ^ ",axiom," ^ tptp_classrelLits subclass superclass ^ ").\n" 

(* write out a subgoal as tptp clauses to the file "xxxx_N"*)
fun tptp_write_file thms filename (ax_tuples,classrel_clauses,arity_clauses) =
  let
    val _ = Output.debug (fn () => ("Preparing to write the TPTP file " ^ filename))
    val clss = make_conjecture_clauses thms
    val (clnames,axclauses) = ListPair.unzip (make_axiom_clauses ax_tuples)
    val (tptp_clss,tfree_litss) = ListPair.unzip (map clause2tptp clss)
    val tfree_clss = map tptp_tfree_clause (foldl (op union_string) [] tfree_litss)
    val out = TextIO.openOut filename
  in
    List.app (curry TextIO.output out o #1 o clause2tptp) axclauses;
    writeln_strs out tfree_clss;
    writeln_strs out tptp_clss;
    List.app (curry TextIO.output out o tptp_classrelClause) classrel_clauses;
    List.app (curry TextIO.output out o tptp_arity_clause) arity_clauses;
    TextIO.closeOut out;
    clnames
  end;

end;
