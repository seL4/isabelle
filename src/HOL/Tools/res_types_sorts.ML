(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID:         $Id$
    Copyright 2004 University of Cambridge

transformation of Isabelle arities and class relations into clauses (defined in the structure Clause). 
*)

signature RES_TYPES_SORTS =
sig

exception ARITIES of string
val arity_clause :
    string * (string * string list list) list -> ResClause.arityClause list
val arity_clause_sig :
    Sign.sg -> ResClause.arityClause list list * (string * 'a list) list
val arity_clause_thy :
    Theory.theory ->
    ResClause.arityClause list list * (string * 'a list) list
type classrelClauses
val classrel_clause : string * string list -> ResClause.classrelClause list
val classrel_clauses_classrel :
    'a Graph.T -> ResClause.classrelClause list list
val classrel_clauses_sg : Sign.sg -> ResClause.classrelClause list list
val classrel_clauses_thy :
    Theory.theory -> ResClause.classrelClause list list
val classrel_of_sg : Sign.sg -> Sorts.classes
val multi_arity_clause :
    (string * (string * string list list) list) list ->
    (string * 'a list) list ->
    ResClause.arityClause list list * (string * 'a list) list
val tptp_arity_clause_thy : Theory.theory -> string list list
val tptp_classrel_clauses_sg : Sign.sg -> string list list
val tsig_of : Theory.theory -> Type.tsig
val tsig_of_sg : Sign.sg -> Type.tsig

end;
				
structure ResTypesSorts : RES_TYPES_SORTS =
    
struct
    
(**** Isabelle arities ****)
    
exception ARITIES of string;


fun arity_clause (tcons, []) = raise ARITIES(tcons)
  | arity_clause (tcons,[ar]) = [ResClause.make_axiom_arity_clause (tcons,ar)]
  | arity_clause (tcons,ar1::ars) = (ResClause.make_axiom_arity_clause (tcons,ar1)) :: (arity_clause (tcons,ars));


fun multi_arity_clause [] expts = ([], expts)
  | multi_arity_clause ((tcon,[])::tcons_ars) expts =
    multi_arity_clause tcons_ars ((tcon,[])::expts)
  | multi_arity_clause (tcon_ar::tcons_ars) expts =
    let val result = multi_arity_clause tcons_ars expts
    in
	(((arity_clause tcon_ar) :: (fst result)),snd result)
    end;

    
fun tsig_of thy = #tsig(Sign.rep_sg (sign_of thy));

fun tsig_of_sg sg = #tsig(Sign.rep_sg sg);


(* Isabelle arities *)
fun arity_clause_thy thy = 
    let val tsig = tsig_of thy
	val arities = #arities (Type.rep_tsig tsig) 
        val entries = Symtab.dest arities 
    in
	multi_arity_clause entries []
    end;

fun arity_clause_sig sg =
    let val tsig = #tsig(Sign.rep_sg sg)
	val arities = #arities (Type.rep_tsig tsig) 
        val entries = Symtab.dest arities 
    in
	multi_arity_clause entries []
    end;


fun tptp_arity_clause_thy thy = 
    let val (arclss,_) = arity_clause_thy thy
    in	
	map (map ResClause.tptp_arity_clause) arclss
    end;



(**** Isabelle classrel ****)

type classrelClauses = (ResClause.classrelClause list) Symtab.table;



(* The new version of finding class relations from a signature *)
fun classrel_of_sg sg = #classes (Type.rep_tsig (tsig_of_sg sg));

fun classrel_clause (sub, sups) = ResClause.classrelClauses_of (sub,sups);



(* new version of classrel_clauses_classrel *)
fun classrel_clauses_classrel classrel =
    let val entries = Graph.dest classrel
    in
	map classrel_clause entries
    end;

fun classrel_clauses_sg sg =
    let val classrel = classrel_of_sg sg 
    in
	classrel_clauses_classrel classrel
    end;


val classrel_clauses_thy = classrel_clauses_sg o sign_of;
 
  
fun tptp_classrel_clauses_sg sg =
    let val relclss = classrel_clauses_sg sg
    in
	map (map  ResClause.tptp_classrelClause) relclss
    end; 




end;
