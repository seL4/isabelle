(*  Title:      HOLCF/domain/interface.ML
    ID:         $Id$
    Author:     David von Oheimb
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Parser for domain section.
*)

local 
  open ThyParse;
  open Domain_Library;

(* --- generation of bindings for axioms and theorems in .thy.ML - *)

  fun get      dname name   = "get_thm thy " ^ quote (dname^"."^name);
  fun gen_vals dname name   = "val "^ name ^ " = get_thm" ^ 
			(if hd (rev (Symbol.explode name)) = "s" then "s" else "")^
			" thy " ^ quote (dname^"."^name)^";";
  fun gen_vall       name l = "val "^name^" = "^ mk_list l^";";
  val rews = "iso_rews @ when_rews @\n\
 	   \  con_rews @ sel_rews @ dis_rews @ dist_les @ dist_eqs @\n\
	   \  copy_rews";

  fun gen_struct num ((dname,_), cons') = let
    val axioms1 = ["abs_iso", "rep_iso", "when_def"];
		   (* con_defs , sel_defs, dis_defs *) 
    val axioms2 = ["copy_def", "reach", "take_def", "finite_def"];
    val theorems = ["iso_rews", "exhaust", "casedist", "when_rews", "con_rews", 
		    "sel_rews", "dis_rews", "dist_les", "dist_eqs", "inverts", 
		    "injects", "copy_rews"];
    in
      "structure "^dname^" = struct\n"^
      cat_lines (map (gen_vals dname) axioms1)^"\n"^
      gen_vall "con_defs"       (map (fn (con,_,_) => 
		get dname (strip_esc con^"_def")) cons')^"\n"^
      gen_vall "sel_defs" (flat (map (fn (_,_,args) => map (fn (_,sel,_) => 
		get dname (sel^"_def")) args)    cons'))^"\n"^
      gen_vall "dis_defs"       (map (fn (con,_,_) => 
		get dname (dis_name_ con^"_def")) cons')^"\n"^
      cat_lines (map (gen_vals dname) axioms2)^"\n"^
      cat_lines (map (gen_vals dname) theorems)^"\n"^
      (if num > 1 then "val rews = " ^rews ^";\n" else "")
    end;

  fun mk_domain eqs'' = let
    val num    = length eqs'';
    val dtnvs  = map fst eqs'';
    val dnames = map fst dtnvs;
    val comp_dname = implode (separate "_" dnames);
    val conss' = ListPair.map 
	(fn (dnam,cons'') => let fun sel n m = upd_second 
			     (fn None   => dnam^"_sel_"^(string_of_int n)^
						    "_"^(string_of_int m)
			       | Some s => s)
	      fun fill_sels n con = upd_third (mapn (sel n) 1) con;
	  in mapn fill_sels 1 cons'' end)
	(dnames, map snd eqs'');
    val eqs' = dtnvs~~conss';

(* ----- string for calling add_domain -------------------------------------- *)

    val thy_ext_string = let
      fun mk_conslist cons' = 
	  mk_list (map (fn (c,syn,ts)=> "\n"^
		    mk_triple(quote c, syn, mk_list (map (fn (b,s ,tp) =>
		    mk_triple(Bool.toString b, quote s, tp)) ts))) cons');
    in "val thy = thy |> Domain_Extender.add_domain "
       ^ mk_pair(quote comp_dname, mk_list(map (fn ((n,vs),cs) => "\n"^
				   mk_pair (mk_pair (quote n, mk_list vs), 
					    mk_conslist cs)) eqs'))
       ^ ";\n"
    end;

(* ----- string for producing the structures -------------------------------- *)

    val val_gen_string =  let
      val comp_axioms   = [(* copy, *) "reach", "take_def", "finite_def"
			   (*, "bisim_def" *)];
      val comp_theorems = ["take_rews", "take_lemmas", "finites", 
			   "finite_ind", "ind", "coind"];
      fun collect sep name = if num = 1 then name else
		   implode (separate sep (map (fn s => s^"."^name) dnames));
    in
	implode (separate "end; (* struct *)\n" 
			  (map (gen_struct num) eqs')) ^
	(if num > 1 then "end; (* struct *)\n\
		         \structure "^comp_dname^" = struct\n" ^
			 gen_vals comp_dname "copy_def" ^"\n" ^
			 cat_lines (map (fn name => gen_vall (name^"s")
			 (map (fn dn => dn^"."^name) dnames)) comp_axioms)^"\n"
		    else "") ^
	gen_vals comp_dname "bisim_def" ^"\n"^
        cat_lines (map (gen_vals comp_dname) comp_theorems)^"\n"^
	"val rews = "^(if num>1 then collect" @ " "rews"else rews)^ 
		    " @ take_rews;\n\
      \end; (* struct *)\n"
    end;
  in (thy_ext_string^
      val_gen_string^
      "val thy = thy",
      "") end;

(* ----- parser for domain declaration equation ----------------------------- *)

  val name' = name >> unenclose;
  val type_var' = type_var >> unenclose;
  fun esc_quote s = let fun esc [] = []
			|   esc ("\""::xs) = esc xs
			|   esc ("[" ::xs) = "{"::esc xs
			|   esc ("]" ::xs) = "}"::esc xs
			|   esc (x   ::xs) = x  ::esc xs
		    in implode (esc (Symbol.explode s)) end;
  val tvar = (type_var' ^^ 
	      optional ($$ "::" ^^ (sort >> esc_quote)) "") >> quote;
  fun type_args l = (tvar >> (fn x => [x])
                 ||  "(" $$-- !! (list1 tvar --$$ ")")
                 ||  empty >> K []) l
  fun con_typ l   = (type_args -- name' >> (fn (x,y) => (y,x))) l
                      (* here ident may be used instead of name' 
                         to avoid ambiguity with standard mixfix option *)
  val domain_arg  = "(" $$-- (optional ($$ "lazy" >> K true) false)
			  -- (optional ((name' >> Some) --$$ "::") None)
			  -- typ --$$ ")" 
		    >> (fn ((lazy,sel),tp) => (lazy,sel,tp))
		 || typ >> (fn x => (false,None,x)) 
  val domain_cons = name' -- !! (repeat domain_arg) 
		    -- ThyParse.opt_mixfix
		    >> (fn ((con,args),syn) => (con,syn,args));
in
  val domain_decl = (enum1 "and" (con_typ --$$ "="  -- !! 
				 (enum1 "|" domain_cons))) >> mk_domain;
  val _ = ThySyn.add_syntax
    ["lazy", "and"]
    [("domain", domain_decl)]

end; (* local *)
