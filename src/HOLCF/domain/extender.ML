(* extender.ML
   ID:         $Id$
   Author : David von Oheimb
   Created: 17-May-95
   Updated: 31-May-95 extracted syntax.ML, theorems.ML
   Updated: 07-Jul-95 streamlined format of cons list
   Updated: 21-Jul-95 gen_by-section
   Updated: 28-Aug-95 simultaneous domain equations
   Copyright 1995 TU Muenchen
*)


structure Extender =
struct

local

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------------- *)

  fun check_domain(eqs':((string * typ list) *
		  (string * ThyOps.cmixfix * (bool*string*typ) list) list) list) = let
    val dtnvs = map fst eqs';
    val cons' = flat (map snd eqs');
    val test_dupl_typs = (case duplicates (map fst dtnvs) of 
	[] => false | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cons = (case duplicates (map first cons') of 
	[] => false | dups => error ("Duplicate constructors: " ^ commas_quote dups));
    val test_dupl_sels = (case duplicates(map second (flat(map third cons'))) of
        [] => false | dups => error ("Duplicate selectors: "^commas_quote dups));
    val test_dupl_tvars = let fun vname (TFree(v,_)) = v
			      |   vname _            = Imposs "extender:vname";
			  in exists (fn tvars => case duplicates (map vname tvars) of
	[] => false | dups => error ("Duplicate type arguments: " ^commas_quote dups))
	(map snd dtnvs) end;
    (*test for free type variables and invalid use of recursive type*)
    val analyse_types = forall (fn ((_,typevars),cons') => 
	forall (fn con' => let
	  val types = map third (third con');
          fun analyse(t as TFree(v,_)) = t mem typevars orelse
					error ("Free type variable " ^ v ^ " on rhs.")
	    | analyse(Type(s,typl)) = (case assoc (dtnvs,s) of None => analyses typl
				      | Some tvs => tvs = typl orelse 
		       error ("Recursion of type " ^ s ^ " with different arguments"))
	    | analyse(TVar _) = Imposs "extender:analyse"
	  and analyses ts = forall analyse ts;
	  in analyses types end) cons' 
	) eqs';
    in true end; (* let *)

  fun check_gen_by thy' (typs': string list,cnstrss': string list list) = let
    val test_dupl_typs = (case duplicates typs' of [] => false
	  | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cnstrs = map (fn cnstrs' => (case duplicates cnstrs' of [] => false
	  | dups => error ("Duplicate constructors: " ^ commas_quote dups))) cnstrss';
    val tsig = #tsig(Sign.rep_sg(sign_of thy'));
    val tycons = map fst (#tycons(Type.rep_tsig tsig));
    val test_types = forall(fn t=>t mem tycons orelse error("Unknown type: "^t))typs';
    val cnstrss = let
	fun type_of c = case (Sign.const_type(sign_of thy') c) of Some t => t
				| None => error ("Unknown constructor: "^c);
	fun args_result_type (t as (Type(tn,[arg,rest]))) = 
			if tn = "->" orelse tn = "=>"
			then let val (ts,r) = args_result_type rest in (arg::ts,r) end
			else ([],t)
	|   args_result_type t = ([],t);
    in map (map (fn cn => let val (args,res) = args_result_type (type_of cn) in
	                 (cn,mk_var_names args,(args,res)) end)) cnstrss' 
	: (string * 			(* operator name of constr *)
	   string list *		(* argument name list *)
	   (typ list *			(* argument types *)
	    typ))			(* result type *)
	  list list end;
    fun test_equal_type tn (cn,_,(_,rt)) = fst (type_name_vars rt) = tn orelse
			       error("Inappropriate result type for constructor "^cn);
    val typs = map (fn (tn, cnstrs) => 
		     (map (test_equal_type tn) cnstrs; snd(third(hd(cnstrs)))))
		   (typs'~~cnstrss);
    val test_typs = map (fn (typ,cnstrs) => 
			if not (Type.typ_instance(tsig,typ,TVar(("'a",0),["pcpo"])))
			then error("Not a pcpo type: "^fst(type_name_vars typ))
			else map (fn (cn,_,(_,rt)) => rt=typ 
		 	  orelse error("Non-identical result types for constructors "^
			  first(hd cnstrs)^" and "^ cn )) cnstrs) (typs~~cnstrss);
    val proper_args = let
	fun occurs tn (Type(tn',ts)) = (tn'=tn) orelse exists (occurs tn) ts
	|   occurs _  _              = false;
	fun proper_arg cn atyp = forall (fn typ => let 
				   val tn = fst(type_name_vars typ) 
				   in atyp=typ orelse not (occurs tn atyp) orelse 
				      error("Illegal use of type "^ tn ^
					 " as argument of constructor " ^cn)end )typs;
	fun proper_curry (cn,_,(args,_)) = forall (proper_arg cn) args;
    in map (map proper_curry) cnstrss end;
  in (typs, flat cnstrss) end;

(* ----- calls for building new thy and thms -------------------------------------- *)

in

  fun add_domain (comp_dname,eqs') thy'' = let
    val ok_dummy = check_domain eqs';
    val thy' = thy'' |> Domain_Syntax.add_syntax (comp_dname,eqs');
    val dts  = map (Type o fst) eqs';
    fun cons cons' = (map (fn (con,syn,args) =>
	(ThyOps.const_name con syn,
	 map (fn ((lazy,sel,tp),vn) => ((lazy,
					 find (tp,dts) handle LIST "find" => ~1),
					sel,vn))
	     (args~~(mk_var_names(map third args)))
	 )) cons') : cons list;
    val eqs = map (fn (dtnvs,cons') => (dtnvs,cons cons')) eqs' : eq list;
    val thy         = thy' |> Domain_Axioms.add_axioms (comp_dname,eqs);
  in (thy,eqs) end;

  fun add_gen_by ((tname,finite),(typs',cnstrss')) thy' = let
   val (typs,cnstrs) = check_gen_by thy' (typs',cnstrss');
  in
   Domain_Axioms.add_gen_by ((tname,finite),(typs,cnstrs)) thy' end;

end (* local *)
end (* struct *)
