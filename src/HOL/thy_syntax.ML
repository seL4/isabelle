(*  Title:      HOL/thy_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel and Lawrence C Paulson and Carsten Clasohm

Additional theory file sections for HOL.

TODO:
  move datatype / primrec stuff to pre_datatype.ML (?)
*)

(*the kind of distinctiveness axioms depends on number of constructors*)
val dtK = 5;  (* FIXME rename?, move? *)

structure ThySynData: THY_SYN_DATA =
struct

open ThyParse;


(** subtype **)

fun mk_subtype_decl (((((opt_name, vs), t), mx), rhs), wt) =
  let
    val name' = if_none opt_name t;
    val name = strip_quotes name';
  in
    (cat_lines [name', mk_triple (t, mk_list vs, mx), rhs, wt],
      [name ^ "_def", "Rep_" ^ name, "Rep_" ^ name ^ "_inverse",
        "Abs_" ^ name ^ "_inverse"])
  end;

val subtype_decl =
  optional ("(" $$-- name --$$ ")" >> Some) None --
  type_args -- name -- opt_infix --$$ "=" -- string -- opt_witness
  >> mk_subtype_decl;



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
          val stri_name = big_rec_name ^ "_Intrnl"
      in
         (";\n\n\
          \structure " ^ stri_name ^ " =\n\
          \  struct\n\
          \  val _ = writeln \"" ^ co ^
                     "Inductive definition " ^ big_rec_name ^ "\"\n\
          \  val rec_tms\t= map (readtm (sign_of thy) Ind_Syntax.termTVar) "
                           ^ srec_tms ^ "\n\
          \  and intr_tms\t= map (readtm (sign_of thy) propT)\n"
                           ^ sintrs ^ "\n\
          \  end;\n\n\
          \val thy = thy |> " ^ co ^ "Ind.add_fp_def_i \n    (" ^
             stri_name ^ ".rec_tms, " ^
             stri_name ^ ".intr_tms)"
         ,
          "structure " ^ big_rec_name ^ " =\n\
          \ let\n\
          \  val _ = writeln \"Proofs for " ^ co ^ 
                     "Inductive definition " ^ big_rec_name ^ "\"\n\
          \  structure Result = " ^ co ^ "Ind_section_Fun\n\
          \\t  (open " ^ stri_name ^ "\n\
          \\t   val thy\t\t= thy\n\
          \\t   val monos\t\t= " ^ monos ^ "\n\
          \\t   val con_defs\t\t= " ^ con_defs ^ ");\n\n\
          \ in\n\
          \  struct\n\
          \  val " ^ mk_list (map mk_intr_name ipairs) ^ " = Result.intrs;\n\
          \  open Result\n\
          \  end\n\
          \ end;\n\n\
          \structure " ^ stri_name ^ " = struct end;\n\n"
         )
      end
    val ipairs = "intrs" $$-- repeat1 (ident -- !! string)
    fun optstring s = optional (s $$-- string) "\"[]\"" >> trim
  in
    repeat1 string -- ipairs -- optstring "monos" -- optstring "con_defs"
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
    mk_list (map (fn ((s, _), _) => quote (tname ^ pre ^ strip_quotes s)) cons);

  (*generate string for calling add_datatype*)
  fun mk_params ((ts, tname), cons) =
   ("val (thy, " ^ tname ^ "_add_primrec) = Datatype.add_datatype\n"
    ^ mk_triple (mk_list ts, quote tname, mk_list (mk_cons cons)) ^ " thy\n\
    \val thy = thy",
    "structure " ^ tname ^ " =\n\
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
    \val dummy = Addsimps " ^ tname ^ ".simps;\n");

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

fun mk_primrec_decl ((fname, tname), axms) =
  let
    fun mk_prove (name, eqn) =
      "val " ^ name ^ " = store_thm (" ^ quote name
      ^ ", prove_goalw thy [get_def thy " ^ fname ^ "] " ^ eqn ^ "\n\
      \  (fn _ => [Simp_tac 1]));";

    val axs = mk_list (map (fn (n, a) => mk_pair (quote n, a)) axms);
  in ("|> " ^ tname ^ "_add_primrec " ^ axs, cat_lines (map mk_prove axms)
      ^ "\nval dummy = Addsimps " ^ mk_list (map fst axms) ^ ";")
  end;

val primrec_decl =
  name -- long_id -- repeat1 (ident -- string) >> mk_primrec_decl;



(** sections **)

val user_keywords = ["intrs", "monos", "con_defs", "|"];

val user_sections =
 [axm_section "subtype" "|> Subtype.add_subtype" subtype_decl,
  ("inductive", inductive_decl ""),
  ("coinductive", inductive_decl "Co"),
  ("datatype", datatype_decl),
  ("primrec", primrec_decl)];


end;


structure ThySyn = ThySynFun(ThySynData);
init_thy_reader ();

