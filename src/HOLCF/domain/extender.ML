(*  Title:      HOLCF/domain/extender.ML
    ID:         $Id$
    Author:     David von Oheimb

Theory extender for domain section, including new-style theory syntax.

###TODO: 

this definition
domain empty = silly empty
yields
Exception-
   TERM
      ("typ_of_term: bad encoding of type",
         [Abs ("uu", "_", Const ("NONE", "_"))]) raised
but this works fine:
domain Empty = silly Empty

strange syntax errors are produced for:
domain xx = xx ("x yy")
domain 'a foo = foo (sel::"'a") 
and bar = bar ("'a dummy")

*)

signature DOMAIN_EXTENDER =
sig
  val add_domain: string *
      ((bstring * string list) * (string * mixfix * (bool * string option * string) list) list) list
    -> theory -> theory
end;

structure Domain_Extender: DOMAIN_EXTENDER =
struct

open Domain_Library;

(* ----- general testing and preprocessing of constructor list -------------- *)
  fun check_and_sort_domain (dtnvs: (string * typ list) list, 
     cons'' : ((string * mixfix * (bool*string option*typ) list) list) list) sg =
  let
    val defaultS = Sign.defaultS sg;
    val test_dupl_typs = (case duplicates (map fst dtnvs) of 
	[] => false | dups => error ("Duplicate types: " ^ commas_quote dups));
    val test_dupl_cons = (case duplicates (map first (List.concat cons'')) of 
	[] => false | dups => error ("Duplicate constructors: " 
							 ^ commas_quote dups));
    val test_dupl_sels = (case duplicates (List.mapPartial second
			       (List.concat (map third (List.concat cons'')))) of
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
	val indirect_ok = ["*","Cfun.->","Ssum.++","Sprod.**","Up.u"]
	fun analyse indirect (TFree(v,s))  = (case AList.lookup (op =) tvars v of 
		    NONE => error ("Free type variable " ^ quote v ^ " on rhs.")
	          | SOME sort => if eq_set_string (s,defaultS) orelse
				    eq_set_string (s,sort    )
				 then TFree(distinct_name v,sort)
				 else error ("Inconsistent sort constraint" ^
				             " for type variable " ^ quote v))
        |   analyse indirect (t as Type(s,typl)) = (case AList.lookup (op =) dtnvs s of
		NONE          => if exists (fn x => x = s) indirect_ok
				 then Type(s,map (analyse false) typl)
				 else Type(s,map (analyse true) typl)
	      | SOME typevars => if indirect 
                           then error ("Indirect recursion of type " ^ 
				        quote (string_of_typ sg t))
                           else if dname <> s orelse (** BUG OR FEATURE?: 
                                mutual recursion may use different arguments **)
				   remove_sorts typevars = remove_sorts typl 
				then Type(s,map (analyse true) typl)
				else error ("Direct recursion of type " ^ 
					     quote (string_of_typ sg t) ^ 
					    " with different arguments"))
        |   analyse indirect (TVar _) = Imposs "extender:analyse";
	fun check_pcpo t = (pcpo_type sg t orelse error(
      "Constructor argument type is not of sort pcpo: "^string_of_typ sg t); t);
	val analyse_con = upd_third (map (upd_third (check_pcpo o analyse false)));
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
    fun strip ss = Library.drop (find_index_eq "'" ss +1, ss);
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
  |> (#1 o (PureThy.add_thmss [(("rews", List.concat rewss @ take_rews), [])]))
  |> Theory.parent_path
end;



(** outer syntax **)

local structure P = OuterParse and K = OuterKeyword in

val dest_decl =
  P.$$$ "(" |-- Scan.optional (P.$$$ "lazy" >> K true) false --
    (P.name >> SOME) -- (P.$$$ "::" |-- P.typ)  --| P.$$$ ")" >> P.triple1
  || P.$$$ "(" |-- P.$$$ "lazy" |-- P.typ --| P.$$$ ")"
       >> (fn t => (true,NONE,t))
  || P.typ >> (fn t => (false,NONE,t));

val cons_decl =
  P.name -- Scan.repeat dest_decl -- P.opt_mixfix
  >> (fn ((c, ds), mx) => (c, mx, ds));

val type_var' = (P.type_ident ^^ 
                 Scan.optional (P.$$$ "::" ^^ P.!!! P.sort) "");
val type_args' = type_var' >> single ||
                 P.$$$ "(" |-- P.!!! (P.list1 type_var' --| P.$$$ ")") ||
 		 Scan.succeed [];

val domain_decl = (type_args' -- P.name >> Library.swap) -- 
                  (P.$$$ "=" |-- P.enum1 "|" cons_decl);
val domains_decl =
  Scan.option (P.$$$ "(" |-- P.name --| P.$$$ ")") -- P.and_list1 domain_decl
  >> (fn (opt_name, doms) =>
      (case opt_name of NONE => space_implode "_" (map (#1 o #1) doms) | SOME s => s, doms));

val domainP =
  OuterSyntax.command "domain" "define recursive domains (HOLCF)" K.thy_decl
    (domains_decl >> (Toplevel.theory o add_domain));


val _ = OuterSyntax.add_keywords ["lazy"];
val _ = OuterSyntax.add_parsers [domainP];

end;

end;
