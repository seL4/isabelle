(*  Title:      HOL/thy_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel and Lawrence C Paulson and Carsten Clasohm

Additional theory file sections for HOL.
*)

(*the kind of distinctiveness axioms depends on number of constructors*)
val dtK = 7;  (* FIXME rename?, move? *)


local

open ThyParse;


(** typedef **)

fun mk_typedef_decl (((((opt_name, vs), t), mx), rhs), wt) =
  let
    val name' = if_none opt_name t;
    val name = strip_quotes name';
  in
    (cat_lines [name', mk_triple (t, mk_list vs, mx), rhs, wt],
      [name ^ "_def", "Rep_" ^ name, "Rep_" ^ name ^ "_inverse",
        "Abs_" ^ name ^ "_inverse"])
  end;

val typedef_decl =
  optional ("(" $$-- name --$$ ")" >> Some) None --
  type_args -- name -- opt_infix --$$ "=" -- string -- opt_witness
  >> mk_typedef_decl;



(** record **)

val record_decl =
  name --$$ "=" -- optional (name --$$ "+" >> (parens o cat "Some")) "None" --
  repeat1 ((name --$$ "::" -- typ) >> mk_pair)
  >> (fn ((x, y), zs) => cat_lines [x, y, mk_big_list zs]);


(** (co)inductive **)

(*co is either "" or "Co"*)
fun inductive_decl co =
  let
    fun mk_intr_name (s, _) =   (*the "op" cancels any infix status*)
      if Syntax.is_identifier s then "op " ^ s else "_";
    fun mk_params (((recs, ipairs), monos), con_defs) =
      let val big_rec_name = space_implode "_" (map (scan_to_id o trim) recs)
          and srec_tms = mk_list recs
          and sintrs   = mk_big_list (map snd ipairs)
          val intrnl_name = big_rec_name ^ "_Intrnl"
      in
         (";\n\n\
          \structure " ^ intrnl_name ^ " =\n\
          \  struct\n\
          \  val _ = writeln \"" ^ co ^
                     "Inductive definition " ^ big_rec_name ^ "\"\n\
          \  val rec_tms\t= map (readtm (sign_of thy) Ind_Syntax.termTVar) "
                           ^ srec_tms ^ "\n\
          \  and intr_tms\t= map (readtm (sign_of thy) propT)\n"
                           ^ sintrs ^ "\n\
          \  end;\n\n\
          \val thy = thy |> " ^ co ^ "Ind.add_fp_def_i \n    (" ^
             intrnl_name ^ ".rec_tms, " ^
             intrnl_name ^ ".intr_tms)"
         ,
          "structure " ^ big_rec_name ^ " =\n\
          \ let\n\
          \  val _ = writeln \"Proofs for " ^ co ^ 
                     "Inductive definition " ^ big_rec_name ^ "\"\n\
          \  structure Result = " ^ co ^ "Ind_section_Fun\n\
          \\t  (open " ^ intrnl_name ^ "\n\
          \\t   val thy\t\t= thy\n\
          \\t   val monos\t\t= " ^ monos ^ "\n\
          \\t   val con_defs\t\t= " ^ con_defs ^ ");\n\n\
          \ in\n\
          \  struct\n\
          \  val " ^ mk_list (map mk_intr_name ipairs) ^ " = Result.intrs;\n\
          \  open Result\n\
          \  end\n\
          \ end;\n\n\
          \structure " ^ intrnl_name ^ " = struct end;\n\n"
         )
      end
    val ipairs = "intrs" $$-- repeat1 (ident -- !! string)
    fun optstring s = optional (s $$-- string >> trim) "[]"
  in
    repeat1 name -- ipairs -- optstring "monos" -- optstring "con_defs"
      >> mk_params
  end;



(** datatype **)

local
  (* FIXME err -> add_datatype *)
  fun mk_cons cs =
    (case duplicates (map (fst o fst) cs) of
      [] => map (fn ((s, ts), syn) => mk_triple (s, mk_list ts, syn)) cs
    | dups => error ("Duplicate constructors: " ^ commas_quote dups));

  (*generate names of distinctiveness axioms*)
  fun mk_distinct_rules cs tname =
    let
      val uqcs = map (fn ((s, _), _) => strip_quotes s) cs;
      (*combine all constructor names with all others w/o duplicates*)
      fun neg_one c = map (fn c2 => quote (c ^ "_not_" ^ c2));
      fun neg1 [] = []
        | neg1 (c1 :: cs) = neg_one c1 cs @ neg1 cs;
    in
      if length uqcs < dtK then neg1 uqcs
      else quote (tname ^ "_ord_distinct") ::
        map (fn c => quote (tname ^ "_ord_" ^ c)) uqcs
    end;

  fun mk_rules tname cons pre = " map (get_axiom thy) " ^
    mk_list (map (fn ((s,_), _) => quote (tname ^ pre ^ strip_quotes s)) cons);

  (*generate string for calling add_datatype and build_record*)
  fun mk_params ((ts, tname), cons) =
    "val (thy,"^tname^"_add_primrec,size_"^tname^"_eqns,split_"^tname^"_eqns) =\n\
    \    Datatype.add_datatype\n"
    ^ mk_triple (mk_list ts, quote tname, mk_list (mk_cons cons)) ^ " thy\n\
    \val thy = ("^tname^"_add_primrec size_"^tname^"_eqns thy)\n\
    \val _ = deny (" ^ quote tname ^ " mem (Sign.stamp_names_of (sign_of thy)))\n\
    \   (\"Datatype \\\""^tname^"\\\" would clash with the theory of the same name!\");\n\
    \structure " ^ tname ^ " =\n\
    \struct\n\
    \ val inject = map (get_axiom thy) " ^
        mk_list (map (fn ((s, _), _) => quote ("inject_" ^ strip_quotes s))
          (filter_out (null o snd o fst) cons)) ^ ";\n\
    \ val distinct = " ^
        (if length cons < dtK then "let val distinct' = " else "") ^
        "map (get_axiom thy) " ^ mk_list (mk_distinct_rules cons tname) ^
        (if length cons < dtK then
          "  in distinct' @ (map (fn t => sym COMP (t RS contrapos))\
          \ distinct') end"
         else "") ^ ";\n\
    \ val induct = get_axiom thy \"" ^ tname ^ "_induct\";\n\
    \ val cases =" ^ mk_rules tname cons "_case_" ^ ";\n\
    \ val recs =" ^ mk_rules tname cons "_rec_" ^ ";\n\
    \ val simps = inject @ distinct @ cases @ recs;\n\
    \ fun induct_tac a = res_inst_tac [(" ^ quote tname ^ ", a)] induct;\n\
    \end;\n\
    \val thy = thy |> Dtype.add_record " ^
      mk_triple
        ("Sign.intern_tycon (sign_of thy) " ^ quote tname,
          mk_list (map (fst o fst) cons),
          tname ^ ".induct_tac") ^ ";\n\
    \val dummy = context thy;\n\
    \val dummy = Addsimps(" ^ tname ^ ".cases @ " ^ tname ^ ".recs);\n\
    \val dummy = AddIffs " ^ tname ^ ".inject;\n\
    \val dummy = " ^
      (if length cons < dtK then "AddIffs " else "Addsimps ") ^
      tname ^ ".distinct;\n\
    \val dummy = Addsimps(map (fn (_,eqn) =>\n\
    \ prove_goalw thy [get_def thy " ^ quote("size_"^tname) ^
                     "] eqn (fn _ => [Simp_tac 1])) size_"^tname^"_eqns);\n\
    \val split_"^tname^"_case = prove_goal thy (#1(split_"^tname^"_eqns))\n\
    \  (fn _ => [#exhaust_tac (datatype_info thy (Sign.intern_tycon (sign_of thy) "
      ^ quote tname ^ ")) \""^tname^"0\" 1,\n\
    \            ALLGOALS Asm_simp_tac]);\n\
    \val split_"^tname^"_case_asm = prove_goal thy (#2(split_"^tname^"_eqns))\n\
    \  (fn _ => [#exhaust_tac (datatype_info thy (Sign.intern_tycon (sign_of thy) "
      ^ quote tname ^ ")) \""^tname^"0\" 1,\n\
    \            ALLGOALS Asm_simp_tac]);\n\
    \val thy = thy\n";

(*
The #exhaust_tac(snd(hd(!datatypes))) in the proof of split_"^tname^"_case
is a hack. Ideally I would just write exhaust_tac, but the latter extracts the
specific exhaustion tactic from the theory associated with the proof
state. However, the exhaustion tactic for the current datatype has only just
been added to !datatypes (a few lines above) but is not yet associated with
the theory. Hope this can be simplified in the future.
*)

  (*parsers*)
  val tvars = type_args >> map (cat "dtVar");

  val simple_typ = ident >> (cat "dtTyp" o curry mk_pair "[]" o quote) ||
    type_var >> cat "dtVar";

  fun complex_typ toks =
    let val typ = simple_typ || "(" $$-- complex_typ --$$ ")";
        val typ2 = complex_typ || "(" $$-- complex_typ --$$ ")";
    in
     (typ -- repeat (ident>>quote) >>
        (foldl (fn (x,y) => "dtTyp " ^ mk_pair (brackets x, y))) ||
      "(" $$-- !! (list1 typ2) --$$ ")" -- !! (repeat1 (ident>>quote)) >>
       (fn (fst, ids) => foldl (fn (x,y) => "dtTyp " ^
                         mk_pair (brackets x, y)) (commas fst, ids))) toks
    end;

  val opt_typs = repeat (simple_typ || ("(" $$-- complex_typ --$$ ")"));
  val constructor = name -- opt_typs -- opt_mixfix;
in
  val datatype_decl =
    tvars -- ident --$$ "=" -- enum1 "|" constructor >> mk_params;
end;



(** primrec **)

(*recursion equations have user-supplied names*)
fun mk_primrec_decl_1 ((fname, tname), axms) =
  let
    (*Isolate type name from the structure's identifier it may be stored in*)
    val tname' = implode (snd (take_suffix (not_equal ".") (explode tname)));

    fun mk_prove (name, eqn) =
      "val " ^ name ^ " = store_thm (" ^ quote name
      ^ ", prove_goalw thy [get_def thy "
      ^ (quote (strip_quotes fname ^ "_" ^ tname')) ^ "] " ^ eqn ^ "\n\
      \  (fn _ => [Simp_tac 1]));";

    val axs = mk_list (map (fn (n, a) => mk_pair (quote n, a)) axms);
  in ("|> " ^ tname ^ "_add_primrec " ^ axs
      , 
      cat_lines (map mk_prove axms)
      ^ "\nval dummy = Addsimps " ^ mk_list (map fst axms) ^ ";")
  end;

(*recursion equations have no names*)
fun mk_primrec_decl_2 ((fname, tname), axms) =
  let
    (*Isolate type name from the structure's identifier it may be stored in*)
    val tname' = implode (snd (take_suffix (not_equal ".") (explode tname)));

    fun mk_prove eqn =
      "prove_goalw thy [get_def thy "
      ^ (quote (strip_quotes fname ^ "_" ^ tname')) ^ "] " ^ eqn ^ " \
      \(fn _ => [Simp_tac 1])";

    val axs = mk_list (map (fn a => mk_pair ("\"\"", a)) axms);
  in ("|> " ^ tname ^ "_add_primrec " ^ axs
      ,
      "val dummy = Addsimps " ^
      brackets(space_implode ",\n" (map mk_prove axms)) ^ ";")
  end;

(*function name, argument type and either (name,axiom) pairs or just axioms*)
val primrec_decl =
  (name -- long_id -- repeat1 (ident -- string) >> mk_primrec_decl_1) ||
  (name -- long_id -- repeat1 string >> mk_primrec_decl_2) ;




(** rec: interface to Slind's TFL **)


(*fname: name of function being defined; rel: well-founded relation*)
fun mk_rec_decl ((((fname, rel), congs), ss), axms) =
  let val fid = trim fname
      val intrnl_name = fid ^ "_Intrnl"
  in
	 (";\n\n\
          \val _ = writeln \"Recursive function " ^ fid ^ "\"\n\
          \val (thy, pats_" ^ intrnl_name ^ ") = Tfl.define thy " ^ 
	                 quote fid ^ " " ^ 
	                 rel ^ "\n" ^ mk_big_list axms ^ ";\n\
          \val thy = thy"
         ,
          "structure " ^ fid ^ " =\n\
          \  struct\n\
          \  val _ = writeln \"Proofs for recursive function " ^ fid ^ "\"\n\
          \  val {rules, induct, tcs} = \n\
          \    \t Tfl.simplify_defn (" ^ ss ^ ", " ^ congs ^ ")\n\
          \    \t\t  (thy, (" ^ quote fid ^ ", pats_" ^ intrnl_name ^ "))\n\
          \  end;\n\
          \val pats_" ^ intrnl_name ^ " = ();\n")
  end;

val rec_decl = (name -- string -- 
		optional ("congs" $$-- string >> trim) "[]" -- 
		optional ("simpset" $$-- string >> trim) "simpset()" -- 
		repeat1 string >> mk_rec_decl) ;



(** augment thy syntax **)

in

val _ = ThySyn.add_syntax
 ["intrs", "monos", "con_defs", "congs", "simpset", "|"]
 [axm_section "typedef" "|> Typedef.add_typedef" typedef_decl,
  (section "record" "|> Record.add_record" record_decl),
  ("inductive", inductive_decl ""),
  ("coinductive", inductive_decl "Co"),
  (section "datatype" "" datatype_decl),
  ("primrec", primrec_decl),
  ("recdef", rec_decl)];

end;
