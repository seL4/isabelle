(*  Title:      HOL/thy_syntax.ML
    ID:         $Id$
    Author:     Markus Wenzel and Lawrence C Paulson and Carsten Clasohm

Additional sections for *old-style* theory files in HOL.
*)

local

open ThyParse;


(** typedef **)

fun mk_typedef_decl (((((opt_name, vs), t), mx), rhs), wt) =
  let
    val name' = if_none opt_name t;
    val name = unenclose name';
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
    -- repeat1 ((name --$$ "::" -- !! (typ -- opt_mixfix)) >> mk_triple2)
  >> (fn ((x, y), zs) => cat_lines [x, y, mk_big_list zs]);



(** (co)inductive **)

(*Skipping initial blanks, find the first identifier*)  (* FIXME slightly broken! *)
fun scan_to_id s =
    s |> Symbol.explode
    |> Scan.error (Scan.finite Symbol.stopper
      (Scan.!! (fn _ => "Expected to find an identifier in " ^ s)
        (Scan.any Symbol.is_blank |-- Syntax.scan_id)))
    |> #1;

fun inductive_decl coind =
  let
    val no_atts = map (mk_pair o rpair "[]");
    fun mk_intr_name (s, _) =   (*the "op" cancels any infix status*)
      if Syntax.is_identifier s then "op " ^ s else "_";
    fun mk_params ((recs, ipairs), monos) =
      let val big_rec_name = space_implode "_" (map (scan_to_id o unenclose) recs)
          and srec_tms = mk_list recs
          and sintrs   = mk_big_list (no_atts (map (mk_pair o apfst Library.quote) ipairs))
      in
        ";\n\n\
        \local\n\
        \val (thy, {defs, mono, unfold, intrs, elims, mk_cases, induct, ...}) =\n\
        \  InductivePackage.add_inductive true " ^
        (if coind then "true " else "false ") ^ srec_tms ^
         sintrs ^ " " ^ mk_list (no_atts monos) ^ " thy;\n\
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
  in repeat1 name -- ipairs -- optlist "monos" >> mk_params end;



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
        unenclose (if_none alt_name name)) dts;

      val add_datatype_args = brackets (commas (map Library.quote names)) ^ " " ^
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

  fun mk_thmss namess = mk_list (map (mk_list o map (mk_pair o rpair "[]")) namess);
  fun mk_thm name = mk_pair (name, "[]");

  fun mk_rep_dt_string (((names, distinct), inject), induct) =
    ";\nlocal\n\
    \val (thy, {distinct, inject, exhaustion, rec_thms,\n\
    \  case_thms, split_thms, induction, size, simps}) =\n\
    \ DatatypePackage.rep_datatype " ^
    (case names of
        Some names => "(Some [" ^ Library.commas_quote names ^ "])\n " ^
          mk_thmss distinct ^ "\n " ^ mk_thmss inject ^
            "\n " ^ mk_thm induct ^ " thy;\nin\n" ^ mk_bind_thms_string names
      | None => "None\n " ^ mk_thmss distinct ^ "\n " ^ mk_thmss inject ^
            "\n " ^ mk_thm induct ^ " thy;\nin\n") ^
    "val thy = thy;\nend;\nval thy = thy\n";

  (*** parsers ***)

  val simple_typ = ident || (type_var >> unenclose);

  fun complex_typ toks =
    let val typ = simple_typ || "(" $$-- complex_typ --$$ ")";
        val typ2 = complex_typ || "(" $$-- complex_typ --$$ ")";
    in
     (typ ^^ (repeat ident >> (cat "" o space_implode " ")) ||
      "(" $$-- !! (list1 typ2 >> (parens o commas)) --$$ ")" ^^ !!
        (repeat1 ident >> (cat "" o space_implode " "))) toks
    end;

  val opt_typs = repeat ((string >> unenclose) ||
    simple_typ || ("(" $$-- complex_typ --$$ ")"));
  val constructor = name -- opt_typs -- opt_mixfix >> (fn ((n, Ts), mx) =>
    parens (n ^ ", " ^ brackets (Library.commas_quote Ts) ^ ", " ^ mx));
  val opt_name = optional ("(" $$-- name --$$ ")" >> Some) None

  fun optlistlist s = optional (s $$-- enum "and" (list name)) [[]]

in
  val datatype_decl =
    enum1 "and" (opt_name -- type_args -- name -- opt_infix --$$ "=" --
      enum1 "|" constructor) >> mk_dt_string;
  val rep_datatype_decl =
    ((optional ((repeat1 (name >> unenclose)) >> Some) None) --
      optlistlist "distinct" -- optlistlist "inject" --
        ("induct" $$-- name)) >> mk_rep_dt_string;
end;



(** primrec **)

fun mk_patterns eqns = mk_list (map (fn (s, _) => if s = "" then "_" else s) eqns);
fun mk_eqns eqns = mk_list (map (fn (x, y) => mk_pair (mk_pair (Library.quote x, y), "[]")) eqns);

fun mk_primrec_decl (alt_name, eqns) =
  ";\nval (thy, " ^ mk_patterns eqns ^ ") = PrimrecPackage.add_primrec " ^ alt_name ^ " "
  ^ mk_eqns eqns ^ " " ^ " thy;\n\
  \val thy = thy\n"

(* either names and axioms or just axioms *)
val primrec_decl = optional ("(" $$-- name --$$ ")") "\"\"" --
  repeat1 (ident -- string || (string >> pair "")) >> mk_primrec_decl;


(*** recdef: interface to Slind's TFL ***)

(** TFL with explicit WF relations **)

(*fname: name of function being defined; rel: well-founded relation*)
fun mk_recdef_decl ((((fname, rel), congs), ss), eqns) =
  let val fid = unenclose fname in
    ";\n\n\
    \local\n\
    \fun simpset() = Simplifier.simpset_of thy;\n\
    \val (thy, result) = thy |> RecdefPackage.add_recdef_old " ^ Library.quote fid ^ " " ^ rel ^ "\n" ^
    mk_eqns eqns ^ "\n(" ^ ss ^ ",\n " ^ mk_list congs ^ ");\n\
    \in\n\
    \structure " ^ fid ^ " =\n\
    \struct\n\
    \  val {simps, rules = " ^ mk_patterns eqns ^ ", induct, tcs} = result;\n\
    \end;\n\
    \val thy = thy;\n\
    \end;\n\
    \val thy = thy\n"
  end;

val recdef_decl =
  name -- string --
    optional ("congs" $$-- list1 ident) [] --
    optional ("simpset" $$-- string >> unenclose) "simpset()" --
    repeat1 (ident -- string || (string >> pair "")) >> mk_recdef_decl;


(** TFL with no WF relation supplied **)

(*fname: name of function being defined; rel: well-founded relation*)
fun mk_defer_recdef_decl ((fname, congs), axms) =
  let
    val fid = unenclose fname;
    val congs_text = mk_list (map (fn c => mk_pair (c, "[]")) congs);
    val axms_text = mk_big_list axms;
  in
    ";\n\n\
    \local\n\
    \val (thy, result) = thy |> RecdefPackage.defer_recdef " ^ Library.quote fid ^ "\n" ^
    axms_text ^ "\n" ^ congs_text ^ ";\n\
    \in\n\
    \structure " ^ fid ^ " =\n\
    \struct\n\
    \  val {induct_rules} = result;\n\
    \end;\n\
    \val thy = thy;\n\
    \end;\n\
    \val thy = thy\n"
  end;

val defer_recdef_decl =
  (name --
    optional ("congs" $$-- list1 name) [] --
    repeat1 string >> mk_defer_recdef_decl);



(** augment thy syntax **)

in

val _ = ThySyn.add_syntax
 ["intrs", "monos", "congs", "simpset", "|", "and", "distinct", "inject", "induct"]
 [axm_section "typedef" "|> TypedefPackage.add_typedef_x" typedef_decl,
  section "record" "|> (#1 oooo RecordPackage.add_record)" record_decl,
  section "inductive" 	"" (inductive_decl false),
  section "coinductive"	"" (inductive_decl true),
  section "datatype" 	"" datatype_decl,
  section "rep_datatype" "" rep_datatype_decl,
  section "primrec" 	"" primrec_decl,
  section "recdef" 	"" recdef_decl,
  section "defer_recdef" "" defer_recdef_decl];

end;
