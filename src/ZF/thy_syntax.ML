(*  Title:      ZF/thy_syntax.ML
    ID:         $Id$
    Author:     Lawrence C Paulson
    Copyright   1994  University of Cambridge

Additional sections for *old-style* theory files in ZF.
*)

local

open ThyParse;

fun mk_bind suffix s =
    if ThmDatabase.is_ml_identifier s then
        "op " ^ s ^ suffix  (*the "op" cancels any infix status*)
    else "_";               (*bad name, don't try to bind*)


(*For lists of theorems.  Either a string (an ML list expression) or else
  a list of identifiers.*)
fun optlist s =
    optional (s $$--
              (string >> unenclose
               || list1 (name>>unenclose) >> mk_list))
    "[]";

(*Skipping initial blanks, find the first identifier*)  (* FIXME slightly broken! *)
fun scan_to_id s =
    s |> Symbol.explode
    |> Scan.error (Scan.finite Symbol.stopper
      (Scan.!! (fn _ => "Expected to find an identifier in " ^ s)
        (Scan.any Symbol.is_blank |-- Syntax.scan_id)))
    |> #1;


(* (Co)Inductive definitions *)

fun inductive_decl coind =
  let
    fun mk_params ((((((recs, sdom_sum), ipairs),
                      monos), con_defs), type_intrs), type_elims) =
      let val big_rec_name = space_implode "_"
                           (map (scan_to_id o unenclose) recs)
          and srec_tms = mk_list recs
          and sintrs   =
            mk_big_list (map (fn (x, y) => mk_pair (mk_pair (quote x, y), "[]")) ipairs)
          and inames   = mk_list (map (mk_bind "" o fst) ipairs)
      in
         ";\n\n\
         \local\n\
         \val (thy, {defs, intrs, elim, mk_cases, \
                    \bnd_mono, dom_subset, induct, mutual_induct, ...}) =\n\
         \  " ^
         (if coind then "Co" else "") ^
         "Ind_Package.add_inductive_x (" ^  srec_tms ^ ", " ^ sdom_sum ^ ") " ^ sintrs ^
           " (" ^ monos ^ ", " ^ con_defs ^ ", " ^ type_intrs ^ ", " ^ type_elims ^ ") thy;\n\
         \in\n\
         \structure " ^ big_rec_name ^ " =\n\
         \struct\n\
         \  val defs = defs\n\
         \  val bnd_mono = bnd_mono\n\
         \  val dom_subset = dom_subset\n\
         \  val intrs = intrs\n\
         \  val elim = elim\n\
         \  val " ^ (if coind then "co" else "") ^ "induct = induct\n\
         \  val mutual_induct = mutual_induct\n\
         \  val mk_cases = mk_cases\n\
         \  val " ^ inames ^ " = intrs\n\
         \end;\n\
         \val thy = thy;\nend;\n\
         \val thy = thy\n"
      end
    val domains = "domains" $$-- enum1 "+" string --$$ "<=" -- !! string
    val ipairs  = "intrs"   $$-- repeat1 (ident -- !! string)
  in domains -- ipairs -- optlist "monos" -- optlist "con_defs"
             -- optlist "type_intrs" -- optlist "type_elims"
     >> mk_params
  end;


(* Datatype definitions *)

fun datatype_decl coind =
  let
    fun mk_const ((x, y), z) = mk_triple (x, mk_list y, z);
    val mk_data = mk_list o map mk_const o snd
    val mk_scons = mk_big_list o map mk_data
    fun mk_params ((((sdom, rec_pairs), monos), type_intrs), type_elims) =
      let val rec_names = map (scan_to_id o unenclose o fst) rec_pairs
          val big_rec_name = space_implode "_" rec_names
          and srec_tms = mk_list (map fst rec_pairs)
          and scons    = mk_scons rec_pairs
          val con_names = flat (map (map (unenclose o #1 o #1) o snd)
                                rec_pairs)
          val inames = mk_list (map (mk_bind "_I") con_names)
      in
         ";\n\n\
         \local\n\
         \val (thy,\n\
         \     {defs, intrs, elim, mk_cases, \
                    \bnd_mono, dom_subset, induct, mutual_induct, ...},\n\
         \     {con_defs, case_eqns, recursor_eqns, free_iffs, free_SEs, mk_free, ...}) =\n\
         \  " ^
         (if coind then "Co" else "") ^
         "Data_Package.add_datatype_x (" ^  sdom ^ ", " ^ srec_tms ^ ") " ^ scons ^
           " (" ^ monos ^ ", " ^ type_intrs ^ ", " ^ type_elims ^ ") thy;\n\
         \in\n\
         \structure " ^ big_rec_name ^ " =\n\
         \struct\n\
         \  val defs = defs\n\
         \  val bnd_mono = bnd_mono\n\
         \  val dom_subset = dom_subset\n\
         \  val intrs = intrs\n\
         \  val elim = elim\n\
         \  val " ^ (if coind then "co" else "") ^ "induct = induct\n\
         \  val mutual_induct = mutual_induct\n\
         \  val mk_cases = mk_cases\n\
         \  val con_defs = con_defs\n\
         \  val case_eqns = case_eqns\n\
         \  val recursor_eqns = recursor_eqns\n\
         \  val free_iffs = free_iffs\n\
         \  val free_SEs = free_SEs\n\
         \  val mk_free = mk_free\n\
         \  val " ^ inames ^ " = intrs;\n\
         \end;\n\
         \val thy = thy;\nend;\n\
         \val thy = thy\n"
      end
    val string_list = "(" $$-- list1 string --$$ ")" || ThyParse.empty;
    val construct = name -- string_list -- opt_mixfix;
  in optional ("<=" $$-- string) "\"\"" --
     enum1 "and" (name --$$ "=" -- enum1 "|" construct) --
     optlist "monos" -- optlist "type_intrs" -- optlist "type_elims"
     >> mk_params
end;



(** rep_datatype **)

fun mk_rep_dt_string (((elim, induct), case_eqns), recursor_eqns) =
  "|> DatatypeTactics.rep_datatype_i " ^ elim ^ " " ^ induct ^ "\n    " ^
  mk_list case_eqns ^ " " ^ mk_list recursor_eqns;

val rep_datatype_decl =
  (("elim" $$-- ident) --
   ("induct" $$-- ident) --
   ("case_eqns" $$-- list1 ident) --
   optional ("recursor_eqns" $$-- list1 ident) []) >> mk_rep_dt_string;



(** primrec **)

fun mk_primrec_decl eqns =
  let val binds = map (mk_bind "" o fst) eqns in
    ";\nval (thy, " ^ mk_list binds ^ ") = PrimrecPackage.add_primrec " ^
      mk_list (map (fn p => mk_pair (mk_pair p, "[]")) (map (apfst quote) eqns)) ^ " " ^ " thy;\n\
    \val thy = thy\n"
  end;

(* either names and axioms or just axioms *)
val primrec_decl =
    ((repeat1 ((ident -- string) || (string >> pair "")))) >> mk_primrec_decl;



(** augment thy syntax **)

in

val _ = ThySyn.add_syntax
 ["inductive", "coinductive", "datatype", "codatatype", "and", "|",
  "<=", "domains", "intrs", "monos", "con_defs", "type_intrs", "type_elims",
  (*rep_datatype*)
  "elim", "induct", "case_eqns", "recursor_eqns"]
 [section "inductive"    "" (inductive_decl false),
  section "coinductive"  "" (inductive_decl true),
  section "datatype"     "" (datatype_decl false),
  section "codatatype"   "" (datatype_decl true),
  section "rep_datatype" "" rep_datatype_decl,
  section "primrec"      "" primrec_decl];

end;
