(*  Title:      HOLCF/domain/extender.ML
    ID:         $Id$
    Author:     David von Oheimb and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Theory extender for domain section, including new-style theory syntax.
*)

signature DOMAIN_EXTENDER =
sig
  val add_domain: string *
      ((bstring * string list) * (string * mixfix * (bool * string * string) list) list) list
    -> theory -> theory
end;

structure Domain_Extender: DOMAIN_EXTENDER =
struct

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------- *)

  fun check_and_sort_domain (dtnvs: (string * typ list) list, cons'' :
     ((string * mixfix * (bool*string*typ) list) list) list) sg =
  let
    val defaultS = Sign.defaultS sg;
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
	(** BUG OR FEATURE?: mutual recursion may use different arguments **)
        |   analyse(Type(s,typl)) = (case assoc_string((*dtnvs*)
						       [(dname,typevars)],s) of 
		None          => Type(s,map analyse typl)
	      | Some typevars => if remove_sorts typevars = remove_sorts typl 
				then Type(s,map analyse typl)
				else error ("Recursion of type " ^ s ^ 
					    " with different arguments"))
        |   analyse(TVar _) = Imposs "extender:analyse";
	fun check_pcpo t = (pcpo_type sg t orelse error(
			   "Type not of sort pcpo: "^string_of_typ sg t); t);
	val analyse_con = upd_third (map (upd_third (check_pcpo o analyse)));
      in ((dname,distinct_typevars), map analyse_con cons') end; 
  in ListPair.map analyse_equation (dtnvs,cons'')
  end; (* let *)

(* ----- calls for building new thy and thms -------------------------------- *)

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
    fun strip ss = drop (find_index_eq "'" ss +1, ss);
    fun typid (Type  (id,_)) =
          let val c = hd (Symbol.explode (Sign.base_name id))
          in if Symbol.is_letter c then c else "t" end
      | typid (TFree (id,_)   ) = hd (strip (tl (Symbol.explode id)))
      | typid (TVar ((id,_),_)) = hd (tl (Symbol.explode id));
    fun cons cons' = (map (fn (con,syn,args) =>
	((Syntax.const_name con syn),
	 ListPair.map (fn ((lazy,sel,tp),vn) => ((lazy,
					find_index_eq tp dts),
					sel,vn))
	     (args,(mk_var_names(map (typid o third) args)))
	 )) cons') : cons list;
    val eqs = map (fn (dtnvs,cons') => (dtnvs,cons cons')) eqs' : eq list;
    val thy        = thy' |> Domain_Axioms.add_axioms (comp_dnam,eqs);
    val (theorems_thy, (rewss, take_rews)) = (foldl_map (fn (thy0,eq) =>
      Domain_Theorems.theorems (eq,eqs) thy0) (thy,eqs))
      |>>> Domain_Theorems.comp_theorems (comp_dnam, eqs);
in
  theorems_thy
  |> Theory.add_path (Sign.base_name comp_dnam)
  |> (#1 o (PureThy.add_thmss [(("rews", flat rewss @ take_rews), [])]))
  |> Theory.parent_path
end;



(** outer syntax **)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val dest_decl =
  P.$$$ "(" |-- Scan.optional (P.$$$ "lazy" >> K true) false --
    P.name -- (P.$$$ "::" |-- P.typ)  --| P.$$$ ")" >> P.triple1;

val cons_decl =
  P.name -- Scan.repeat dest_decl -- P.opt_mixfix
  >> (fn ((c, ds), mx) => (c, mx, ds));

val domain_decl = (P.type_args -- P.name >> Library.swap) -- (P.$$$ "=" |-- P.enum1 "|" cons_decl);
val domains_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.and_list1 domain_decl
  >> (fn (opt_name, doms) =>
      (case opt_name of None => space_implode "_" (map (#1 o #1) doms) | Some s => s, doms));

val domainP =
  OuterSyntax.command "domain" "define recursive domains (HOLCF)" K.thy_decl
    (domains_decl >> (Toplevel.theory o add_domain));


val _ = OuterSyntax.add_keywords ["lazy"];
val _ = OuterSyntax.add_parsers [domainP];

end;

end;
