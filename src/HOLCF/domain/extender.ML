(*  Title:      HOLCF/domain/extender.ML
    ID:         $Id$
    Author : David von Oheimb
    Copyright 1995, 1996 TU Muenchen

theory extender for domain section
*)


structure Domain_Extender =
struct

local

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------- *)

  fun check_and_sort_domain (eqs'':((string * typ list) *
     (string * ThyOps.cmixfix * (bool*string*typ) list) list) list) thy'' = let
    val dtnvs = map fst eqs'';
    val cons' = flat (map snd eqs'');
    val test_dupl_typs = (case duplicates (map fst dtnvs) of 
	[] => false | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cons = (case duplicates (map first cons') of 
	[] => false | dups => error ("Duplicate constructors: " ^ commas_quote dups));
    val test_dupl_sels = (case duplicates(map second (flat(map third cons'))) of
        [] => false | dups => error("Duplicate selectors: "^commas_quote dups));
    val test_dupl_tvars = exists(fn s=>case duplicates(map(fst o rep_TFree)s)of
	[] => false | dups => error("Duplicate type arguments: " 
							   ^commas_quote dups))
	(map snd dtnvs);
    val default = ["_default"];
    (*test for free type variables, Inconsistent sort constraints,
	       non-pcpo-types and invalid use of recursive type*)
    in map (fn ((dname,typevars),cons') => let
      val tvars = ref (map rep_TFree typevars) : (string * sort) list ref;
      fun newsort (TFree(v,s)) = TFree(v,case assoc_string (!tvars,v) of
		None   => Imposs "extender:newsort"
	      | Some s => if s=default then Type.defaultS(tsig_of thy'') else s)
      |   newsort (Type(s,typl)) = Type(s,map newsort typl)
      |   newsort (TVar _) = Imposs "extender:newsort 2";
      val analyse_cons = forall (fn con' => let
	  val types = map third (third con');
	  fun rm_sorts (TFree(s,_)) = TFree(s,[])
	  |   rm_sorts (Type(s,ts)) = Type(s,remove_sorts ts)
	  |   rm_sorts (TVar(s,_))  = TVar(s,[])
	  and remove_sorts l = map rm_sorts l;
          fun analyse(TFree(v,s)) = (case assoc_string(!tvars,v) of 
			None =>	error ("Free type variable " ^ v ^ " on rhs.")
		      | Some sort => s = default orelse
				     if sort = default 
					then (tvars:= (v,s):: !tvars;true)
					else eq_set_string (s,sort) orelse
					error ("Inconsistent sort constraints "^
					       "for type variable "^quote v))
	    | analyse(Type(s,typl)) = (case assoc_string (dtnvs,s) of 
			None => forall analyse typl
		      | Some tvs => remove_sorts tvs = remove_sorts typl orelse 
		       		    error ("Recursion of type " ^ s ^ 
					   " with different arguments"))
	    | analyse(TVar _) = Imposs "extender:analyse";
	  in forall analyse types end) cons';
      fun check_pcpo t = (pcpo_type thy'' t orelse 
			  error("Not a pcpo type: "^string_of_typ thy'' t); t);
      fun check_type (t as Type(s,typl)) = (case assoc_string (dtnvs,s) of 
			None => check_pcpo t | Some _ => t)
      |   check_type t = check_pcpo t;
      in ((dname,map newsort typevars),
	  map (upd_third (map (upd_third (check_type o newsort)))) cons')
      end) eqs''
    end; (* let *)
  fun check_gen_by thy' (typs': string list,cnstrss': string list list) = let
    val test_dupl_typs = (case duplicates typs' of [] => false
	  | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cnstrs = map (fn cs => (case duplicates cs of [] => false 
	| ds => error ("Duplicate constructors: " ^ commas_quote ds))) cnstrss';
    val tycons = map fst (#tycons(Type.rep_tsig (tsig_of thy')));
    val test_types = forall (fn t => t mem tycons orelse 
				     error("Unknown type: "^t)) typs';
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
    fun test_equal_type tn (cn,_,(_,rt)) = fst (rep_Type rt) = tn orelse
		      error("Inappropriate result type for constructor "^cn);
    val typs = map (fn (tn, cnstrs) => (map (test_equal_type tn) cnstrs; 
				snd(third(hd(cnstrs)))))  (typs'~~cnstrss);
    val test_typs = map (fn (typ,cnstrs) => 
			if not (pcpo_type thy' typ)
			then error("Not a pcpo type: "^string_of_typ thy' typ)
			else map (fn (cn,_,(_,rt)) => rt=typ orelse error(
				"Non-identical result types for constructors "^
			        first(hd cnstrs)^" and "^ cn ))  cnstrs)
		    (typs~~cnstrss);
    val proper_args = let
	fun occurs tn (Type(tn',ts)) = (tn'=tn) orelse exists (occurs tn) ts
	|   occurs _  _              = false;
	fun proper_arg cn atyp = forall (fn typ => let 
				   val tn = fst (rep_Type typ) 
				   in atyp=typ orelse not (occurs tn atyp) orelse 
				      error("Illegal use of type "^ tn ^
					 " as argument of constructor " ^cn)end )typs;
	fun proper_curry (cn,_,(args,_)) = forall (proper_arg cn) args;
    in map (map proper_curry) cnstrss end;
  in (typs, flat cnstrss) end;

(* ----- calls for building new thy and thms -------------------------------------- *)

in

  fun add_domain (comp_dname,eqs'') thy'' = let
    val eqs' = check_and_sort_domain eqs'' thy'';
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
   Domain_Axioms.add_induct ((tname,finite),(typs,cnstrs)) thy' end;

end (* local *)
end (* struct *)
