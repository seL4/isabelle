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

  fun check_and_sort_domain (dtnvs: (string * typ list) list, cons'' :
     ((string * ThyOps.cmixfix * (bool*string*typ) list) list) list) sg =
  let
    val defaultS = Type.defaultS (tsig_of sg);
    val test_dupl_typs = (case duplicates (map fst dtnvs) of 
	[] => false | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cons = (case duplicates (map first (flat cons'')) of 
	[] => false | dups => error ("Duplicate constructors: " 
							 ^ commas_quote dups));
    val test_dupl_sels = (case duplicates 
			       (map second (flat (map third (flat cons'')))) of
        [] => false | dups => error("Duplicate selectors: "^commas_quote dups));
    val test_dupl_tvars = exists(fn s=>case duplicates(map(fst o rep_TFree)s)of
	[] => false | dups => error("Duplicate type arguments: " 
		   ^commas_quote dups)) (map snd dtnvs);
    (* test for free type variables, illegal sort constraints on rhs,
	       non-pcpo-types and invalid use of recursive type;
       replace sorts in type variables on rhs *)
    fun analyse_equation ((dname,typevars),cons') = 
      let
	val tvars = map rep_TFree typevars;
	fun distinct_name s = "'"^Sign.base_name dname^"_"^s;
	val distinct_typevars = map (fn (n,sort) => 
				     TFree (distinct_name n,sort)) tvars;
	fun rm_sorts (TFree(s,_)) = TFree(s,[])
	|   rm_sorts (Type(s,ts)) = Type(s,remove_sorts ts)
	|   rm_sorts (TVar(s,_))  = TVar(s,[])
	and remove_sorts l = map rm_sorts l;
	fun analyse(TFree(v,s)) = (case assoc_string(tvars,v) of 
		    None      => error ("Free type variable " ^ v ^ " on rhs.")
	          | Some sort => if eq_set_string (s,defaultS) orelse
				    eq_set_string (s,sort    )
				 then TFree(distinct_name v,sort)
				 else error ("Additional constraint on rhs "^
					     "for type variable "^quote v))
        |    analyse(Type(s,typl)) = if s <> dname 
			then Type(s,map analyse typl)
			else if remove_sorts typevars = remove_sorts typl 
				then Type(s,map analyse typl) 
				else error ("Recursion of type " ^ s ^ 
					    " with different arguments")
        | analyse(TVar _) = Imposs "extender:analyse";
	fun check_pcpo t = (pcpo_type sg t orelse 
			   error("Not a pcpo type: "^string_of_typ sg t); t);
	val analyse_con = upd_third (map (upd_third (check_pcpo o analyse)));
      in ((dname,distinct_typevars), map analyse_con cons') end; 
  in ListPair.map analyse_equation (dtnvs,cons'')
  end; (* let *)

  fun check_gen_by sg' (typs': string list,cnstrss': string list list) = let
    val test_dupl_typs = (case duplicates typs' of [] => false
	  | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cnstrs = map (fn cs => (case duplicates cs of [] => false 
	| ds => error ("Duplicate constructors: " ^ commas_quote ds))) cnstrss';
    val tycons = map fst (#tycons(Type.rep_tsig (tsig_of sg')));
    val test_types = forall (fn t => t mem tycons orelse 
				     error("Unknown type: "^t)) typs';
    val cnstrss = let
	fun type_of c = case (Sign.const_type sg' c) of Some t => t
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
    val typs = ListPair.map (fn (tn, cnstrs) =>(map (test_equal_type tn) cnstrs;
				snd(third(hd(cnstrs)))))  (typs',cnstrss);
    val test_typs = ListPair.map (fn (typ,cnstrs) => 
			if not (pcpo_type sg' typ)
			then error("Not a pcpo type: "^string_of_typ sg' typ)
			else map (fn (cn,_,(_,rt)) => rt=typ orelse error(
				"Non-identical result types for constructors "^
			        first(hd cnstrs)^" and "^ cn ))  cnstrs)
		    (typs,cnstrss);
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

(* ----- calls for building new thy and thms -------------------------------- *)

in

  fun add_domain (comp_dnam,eqs''') thy''' = let
    val sg''' = sign_of thy''';
    val dtnvs = map ((fn (dname,vs) => 
			 (Sign.full_name sg''' dname,map (str2typ sg''') vs))
                   o fst) eqs''';
    val cons''' = map snd eqs''';
    fun thy_type  (dname,tvars)  = (Sign.base_name dname, length tvars, NoSyn);
    fun thy_arity (dname,tvars)  = (dname, map (snd o rep_TFree) tvars, pcpoS);
    val thy'' = thy''' |> Theory.add_types     (map thy_type  dtnvs)
		       |> Theory.add_arities_i (map thy_arity dtnvs);
    val sg'' = sign_of thy'';
    val cons''=map (map (upd_third (map (upd_third (str2typ sg''))))) cons''';
    val eqs' = check_and_sort_domain (dtnvs,cons'') sg'';
    val thy' = thy'' |> Domain_Syntax.add_syntax (comp_dnam,eqs');
    val dts  = map (Type o fst) eqs';
    fun cons cons' = (map (fn (con,syn,args) =>
	((ThyOps.const_name con syn),
	 ListPair.map (fn ((lazy,sel,tp),vn) => ((lazy,
					find (tp,dts) handle LIST "find" => ~1),
					sel,vn))
	     (args,(mk_var_names(map third args)))
	 )) cons') : cons list;
    val eqs = map (fn (dtnvs,cons') => (dtnvs,cons cons')) eqs' : eq list;
    val thy       = thy' |> Domain_Axioms.add_axioms (comp_dnam,eqs);
    val thmss     = map (Domain_Theorems.theorems thy eqs) eqs;
    val comp_thms = Domain_Theorems.comp_theorems thy (comp_dnam, eqs, thmss);
  in (thy, thmss, comp_thms) end;

  fun add_gen_by ((tname,finite),(typs',cnstrss')) thy' = let
   val (typs,cnstrs) = check_gen_by (sign_of thy') (typs',cnstrss');
  in
   Domain_Axioms.add_induct ((tname,finite),(typs,cnstrs)) thy' end;

end (* local *)
end (* struct *)
