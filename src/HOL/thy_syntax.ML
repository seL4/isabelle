(*  Title:      HOL/thy_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel and Lawrence C Paulson and Carsten Clasohm

Additional theory file sections for HOL.
*)

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
  (type_args -- name >> (mk_pair o apfst mk_list)) --$$ "="
    -- optional (typ --$$ "+" >> (parens o cat "Some")) "None"
    -- repeat1 ((name --$$ "::" -- typ) >> mk_pair)
  >> (fn ((x, y), zs) => cat_lines [x, y, mk_big_list zs]);


(** (co)inductive **)

fun inductive_decl coind =
  let
    fun mk_intr_name (s, _) =   (*the "op" cancels any infix status*)
      if Syntax.is_identifier s then "op " ^ s else "_";
    fun mk_params (((recs, ipairs), monos), con_defs) =
      let val big_rec_name = space_implode "_" (map (scan_to_id o strip_quotes) recs)
          and srec_tms = mk_list recs
          and sintrs   = mk_big_list (map snd ipairs)
      in
        ";\n\n\
        \local\n\
        \val (thy, {defs, mono, unfold, intrs, elims, mk_cases, induct, ...}) =\n\
        \  InductivePackage.add_inductive true " ^
        (if coind then "true " else "false ") ^ srec_tms ^ " " ^
         sintrs ^ " " ^ mk_list monos ^ " " ^ mk_list con_defs ^ " thy;\n\
        \in\n\
        \structure " ^ big_rec_name ^ " =\n\
        \struct\n\
        \  val defs = defs;\n\
        \  val mono = mono;\n\
        \  val unfold = unfold;\n\
        \  val intrs = intrs;\n\
        \  val elims = elims;\n\
        \  val elim = hd elims;\n\
        \  val " ^ (if coind then "co" else "") ^ "induct = induct;\n\
        \  val mk_cases = mk_cases;\n\
        \  val " ^ mk_list (map mk_intr_name ipairs) ^ " = intrs;\n\
        \end;\n\
        \val thy = thy;\nend;\n\
        \val thy = thy\n"
      end
    val ipairs = "intrs" $$-- repeat1 (ident -- !! string)
    fun optlist s = optional (s $$-- list1 name) []
  in
    repeat1 name -- ipairs -- optlist "monos" -- optlist "con_defs"
      >> mk_params
  end;


(** datatype **)

local
  (*** generate string for calling add_datatype ***)
  (*** and bindig theorems to ML identifiers    ***)

  fun mk_bind_thms_string names =
   (case find_first (not o Syntax.is_identifier) names of
      Some id => (warning (id ^ " is not a valid identifier"); "")
    | None =>
        let
          fun mk_dt_struct (s, (id, i)) =
            s ^ "structure " ^ id ^ " =\n\
            \struct\n\
            \  val distinct = nth_elem (" ^ i ^ ", distinct);\n\
            \  val inject = nth_elem (" ^ i ^ ", inject);\n\
            \  val exhaust = nth_elem (" ^ i ^ ", exhaustion);\n\
            \  val cases = nth_elem (" ^ i ^ ", case_thms);\n\
            \  val (split, split_asm) = nth_elem (" ^ i ^ ", split_thms);\n" ^
              (if length names = 1 then
                 "  val induct = induction;\n\
                 \  val recs = rec_thms;\n\
                 \  val simps = simps;\n\
                 \  val size = size;\n"
               else "") ^
            "end;\n";

          val structs = foldl mk_dt_struct
            ("", (names ~~ (map string_of_int (0 upto length names - 1))));

        in
          (if length names > 1 then
             "structure " ^ (space_implode "_" names) ^ " =\n\
             \struct\n\
             \  val induct = induction;\n\
             \  val recs = rec_thms;\n\
             \  val simps = simps;\n\
             \  val size = size;\nend;\n"
           else "") ^ structs
        end);

  fun mk_dt_string dts =
    let
      val names = map (fn ((((alt_name, _), name), _), _) =>
        strip_quotes (if_none alt_name name)) dts;

      val add_datatype_args = brackets (commas (map quote names)) ^ " " ^
        brackets (commas (map (fn ((((_, vs), name), mx), cs) =>
          parens (brackets (commas vs) ^ ", " ^ name ^ ", " ^ mx ^ ", " ^
            brackets (commas cs))) dts));

    in
      ";\nlocal\n\
      \val (thy, {distinct, inject, exhaustion, rec_thms,\n\
      \  case_thms, split_thms, induction, size, simps}) =\n\
      \ DatatypePackage.add_datatype false " ^ add_datatype_args ^ " thy;\n\
      \in\n" ^ mk_bind_thms_string names ^
      "val thy = thy;\nend;\nval thy = thy\n"
    end;

  fun mk_thmss namess = "(map (PureThy.get_thmss thy) " ^ mk_list (map mk_list namess) ^ ")";
  fun mk_thm name = "(PureThy.get_thm thy " ^ name ^ ")";

  fun mk_rep_dt_string (((names, distinct), inject), induct) =
    ";\nlocal\n\
    \val (thy, {distinct, inject, exhaustion, rec_thms,\n\
    \  case_thms, split_thms, induction, size, simps}) =\n\
    \ DatatypePackage.rep_datatype " ^
    (case names of
        Some names => "(Some [" ^ commas_quote names ^ "])\n " ^
          mk_thmss distinct ^ "\n " ^ mk_thmss inject ^
            "\n " ^ mk_thm induct ^ " thy;\nin\n" ^ mk_bind_thms_string names
      | None => "None\n " ^ mk_thmss distinct ^ "\n " ^ mk_thmss inject ^
            "\n " ^ mk_thm induct ^ " thy;\nin\n") ^
    "val thy = thy;\nend;\nval thy = thy\n";

  (*** parsers ***)

  val simple_typ = ident || (type_var >> strip_quotes);

  fun complex_typ toks =
    let val typ = simple_typ || "(" $$-- complex_typ --$$ ")";
        val typ2 = complex_typ || "(" $$-- complex_typ --$$ ")";
    in
     (typ ^^ (repeat ident >> (cat "" o space_implode " ")) ||
      "(" $$-- !! (list1 typ2 >> (parens o commas)) --$$ ")" ^^ !!
        (repeat1 ident >> (cat "" o space_implode " "))) toks
    end;

  val opt_typs = repeat ((string >> strip_quotes) ||
    simple_typ || ("(" $$-- complex_typ --$$ ")"));
  val constructor = name -- opt_typs -- opt_mixfix >> (fn ((n, Ts), mx) =>
    parens (n ^ ", " ^ brackets (commas_quote Ts) ^ ", " ^ mx));
  val opt_name = optional ("(" $$-- name --$$ ")" >> Some) None

  fun optlistlist s = optional (s $$-- enum "and" (list name)) [[]]

in
  val datatype_decl =
    enum1 "and" (opt_name -- type_args -- name -- opt_infix --$$ "=" --
      enum1 "|" constructor) >> mk_dt_string;
  val rep_datatype_decl =
    ((optional ((repeat1 (name >> strip_quotes)) >> Some) None) --
      optlistlist "distinct" -- optlistlist "inject" --
        ("induct" $$-- name)) >> mk_rep_dt_string;
end;


(** primrec **)

fun mk_primrec_decl (alt_name, eqns) =
  let
    val names = map (fn (s, _) => if s = "" then "_" else s) eqns
  in
    ";\nval (thy, " ^ mk_list names ^ ") = PrimrecPackage.add_primrec " ^ alt_name ^ " " ^
    mk_list (map (fn (x, y) => mk_pair (mk_pair (quote x, y), "[]")) eqns) ^
    " " ^ " thy;\n\
    \val thy = thy\n"
  end;

(* either names and axioms or just axioms *)
val primrec_decl = (optional ("(" $$-- name --$$ ")") "\"\"" --
  (repeat1 ((ident -- string) || (string >> pair "")))) >> mk_primrec_decl;


(** rec: interface to Slind's TFL **)


(*fname: name of function being defined; rel: well-founded relation*)
fun mk_rec_decl ((((fname, rel), congs), ss), axms) =
  let val fid = strip_quotes fname
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

val rec_decl = 
    (name -- string -- 
     optional ("congs" $$-- string >> strip_quotes) "[]" -- 
     optional ("simpset" $$-- string >> strip_quotes) "simpset()" -- 
     repeat1 string >> mk_rec_decl) ;



(** augment thy syntax **)

in

val _ = ThySyn.add_syntax
 ["intrs", "monos", "con_defs", "congs", "simpset", "|",
  "and", "distinct", "inject", "induct"]
 [axm_section "typedef" "|> TypedefPackage.add_typedef" typedef_decl,
  section "record" "|> RecordPackage.add_record" record_decl,
  section "inductive" "" (inductive_decl false),
  section "coinductive" "" (inductive_decl true),
  section "datatype" "" datatype_decl,
  section "rep_datatype" "" rep_datatype_decl,
  section "primrec" "" primrec_decl,
  ("recdef", rec_decl)];

end;
