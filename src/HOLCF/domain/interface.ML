(*  Title:      HOLCF/domain/interface.ML
    ID:         $Id$
    Author : David von Oheimb
    Copyright 1995, 1996 TU Muenchen

parser for domain section
*)


structure ThySynData: THY_SYN_DATA = (* overwrites old version of ThySynData !!!!!! *)

struct

local 
  open ThyParse;
  open Domain_Library;

(* --- generation of bindings for axioms and theorems in trailer of .thy.ML - *)

  fun gt_ax         name   = "get_axiom thy " ^ quote name;
  fun gen_val dname name   = "val "^name^" = "^ gt_ax (dname^"_"^name)^";";
  fun gen_vall      name l = "val "^name^" = "^ mk_list l^";";
  val rews1 = "iso_rews @ when_rews @\n\
 	      \con_rews @ sel_rews @ dis_rews @ dists_le @ dists_eq @\n\
	      \copy_rews";

  fun gen_domain eqname num ((dname,_), cons') = let
    val axioms1 = ["abs_iso", "rep_iso", "when_def"];
		   (* con_defs , sel_defs, dis_defs *) 
    val axioms2 = ["copy_def"];
    val theorems = 
	"iso_rews, exhaust, cases, when_rews, con_rews, sel_rews, dis_rews,\n    \
	\dists_le, dists_eq, inverts, injects, copy_rews";
    in
      "structure "^dname^" = struct\n"^
      cat_lines(map (gen_val dname) axioms1)^"\n"^
      gen_vall"con_defs"(map(fn (con,_,_) => gt_ax(strip_esc con^"_def")) cons')^"\n"^
      gen_vall"sel_defs"(flat(map (fn (_,_,args) => map (fn (_,sel,_) => 
					     gt_ax(sel^"_def")) args)    cons'))^"\n"^
      gen_vall"dis_defs"(map(fn (con,_,_) => gt_ax(dis_name_ con^"_def")) 
								          cons')^"\n"^
      cat_lines(map (gen_val dname) axioms2)^"\n"^
      "val ("^ theorems ^") =\n\
      \Domain_Theorems.theorems thy "^eqname^";\n" ^
      (if num > 1 then "val rews = " ^rews1 ^";\n" else "")
    end;

  fun mk_domain (eqs'') = let
    val dtnvs  = map (rep_Type o fst) eqs'';
    val dnames = map fst dtnvs;
    val num = length dnames;
    val comp_dname = implode (separate "_" dnames);
    val conss' = ListPair.map 
	(fn (dname,cons'') =>
	  let fun sel n m = upd_second 
			      (fn None   => dname^"_sel_"^(string_of_int n)^
						 "_"^(string_of_int m)
				| Some s => s)
	      fun fill_sels n con = upd_third (mapn (sel n) 1) con;
	  in mapn fill_sels 1 cons'' end)
	(dnames, map #2 eqs'');
    val eqs' = dtnvs~~conss';

(* ----- string for calling add_domain -------------------------------------- *)

    val thy_ext_string = let
      fun mk_tnv (n,v) = mk_pair (quote n, mk_list (map mk_typ v))
      and mk_typ (TFree(name,sort))= "TFree" ^ 
			 mk_pair (quote name, mk_list (map quote sort))
      |   mk_typ (Type (name,args))= "Type" ^mk_tnv(name,args)
      |   mk_typ _                 = Imposs "interface:mk_typ";
      fun mk_conslist cons' = 
	  mk_list (map 
		   (fn (c,syn,ts)=>
		    mk_triple(quote c, syn, 
			      mk_list
			      (map (fn (b,s ,tp) =>
				    mk_triple(Bool.toString b, quote s,
					      mk_typ tp)) ts))) cons');
    in "val (thy, "^comp_dname^"_equations) = thy |> Domain_Extender.add_domain \n"
       ^ mk_pair(quote comp_dname,
		 mk_list(map (fn (t,cs)=> mk_pair (mk_tnv t,mk_conslist cs)) eqs'))
       ^ ";\nval thy = thy"
    end;

(* ----- string for calling (comp_)theorems and producing the structures ---------- *)

    val val_gen_string =  let
      fun plural s = if num > 1 then s^"s" else "["^s^"]";
      val comp_axioms   = [(* copy, *) "reach", "take_def", "finite_def"
			   (*, "bisim_def" *)];
      val comp_theorems = "take_rews, " ^ implode (separate ", " (map plural
			       ["take_lemma","finite"]))^", finite_ind, ind, coind";
      fun eqname n = "(hd(funpow "^string_of_int n^" tl "^comp_dname^"_equations), "
							 ^comp_dname^"_equations)";
      fun collect sep name = if num = 1 then name else
			     implode (separate sep (map (fn s => s^"."^name) dnames));
    in
      implode (separate "end; (* struct *)\n\n" 
        	 (mapn (fn n => gen_domain (eqname n) num) 0 eqs'))^(if num > 1 then
      "end; (* struct *)\n\n\
      \structure "^comp_dname^" = struct\n" else "") ^
	(if num > 1 then gen_val comp_dname "copy_def" ^"\n" else "") ^
	implode ((map (fn s => gen_vall (plural s)
	           (map (fn dn => gt_ax(dn ^ "_" ^ s)) dnames) ^"\n") comp_axioms)) ^
	 gen_val comp_dname "bisim_def" ^"\n\
        \val ("^ comp_theorems ^") =\n\
	\Domain_Theorems.comp_theorems thy \
	\(" ^ quote comp_dname   ^ ","^ comp_dname ^"_equations,\n\
	\ ["^collect "    ," "cases"    ^"],\n\
	\  "^collect "@"     "con_rews " ^",\n\
	\  "^collect " @"    "copy_rews" ^");\n\
	\val rews = "^(if num>1 then collect" @ " "rews"else rews1)^ " @ take_rews;\n\
      \end; (* struct *)"
    end;
  in (thy_ext_string, val_gen_string) end;

(* ----- strings for calling add_gen_by and producing the value binding ----------- *)

  fun mk_gen_by (finite,eqs) = let
      val typs    = map fst eqs;
      val cnstrss = map snd eqs;
      val tname = implode (separate "_" typs) in
      ("|> Domain_Extender.add_gen_by "
       ^ mk_pair(mk_pair(quote tname, Bool.toString finite),
		 mk_pair(mk_list(map quote typs), 
			 mk_list (map (fn cns => mk_list(map quote cns)) cnstrss))),
       "val "^tname^"_induct = " ^gt_ax (tname^"_induct")^";") end;

(* ----- parser for domain declaration equation ----------------------------------- *)

  val name' = name >> strip_quotes;
  val type_var' = type_var >> strip_quotes;
  val sort = name' >> (fn s => [s])
	  || "{" $$-- !! (list name' --$$ "}");
  val tvar = (type_var' --(optional("::" $$-- !! sort)["_default"])) >>TFree;
(*val tvar = type_var >> (fn tv => TFree(strip_quotes tv,["pcpo"]));*)
  fun type_args l = ("(" $$-- !! (list1 typ --$$ ")")
	         || tvar  >> (fn x => [x])
	         || empty >> K []) l
  and con_typ l   = (type_args -- name' >> (fn (x,y) => Type(y,x))) l
			(* here ident may be used instead of name' 
			   to avoid ambiguity with standard mixfix option *)
  and typ l       = (con_typ 
		   || tvar) l;
  val domain_arg  = "(" $$-- (optional ($$ "lazy" >> K true) false)
			  -- (optional ((name' >> Some) --$$ "::") None)
			  -- typ --$$ ")" >> (fn ((lazy,sel),tp) => (lazy,sel,tp))
		 || name' >> (fn x => (false,None,Type(x,[]))) 
		 || tvar  >> (fn x => (false,None,x));
  val domain_cons = name' -- !! (repeat domain_arg) 
		    -- ThyOps.opt_cmixfix
		    >> (fn ((con,args),syn) => (con,syn,args));
in
  val domain_decl = (enum1 "," (con_typ --$$ "="  -- !! 
			       (enum1 "|" domain_cons))) 	    >> mk_domain;
  val gen_by_decl = (optional ($$ "finite" >> K true) false) -- 
		    (enum1 "," (name'   --$$ "by" -- !!
			       (enum1 "|" name'))) >> mk_gen_by;
end; (* local *)

val user_keywords = "lazy"::"by"::"finite"::
		(**)filter_out (fn s=>s="lazy" orelse s="by" orelse s="finite")(**)
		    ThySynData.user_keywords;
val user_sections = ("domain", domain_decl)::("generated", gen_by_decl)::
		(**)filter_out (fn (s,_)=>s="domain" orelse s="generated")(**)
		    ThySynData.user_sections;
end; (* struct *)

structure ThySyn = ThySynFun(ThySynData); (* overwrites old version of ThySyn!!!!!! *)
