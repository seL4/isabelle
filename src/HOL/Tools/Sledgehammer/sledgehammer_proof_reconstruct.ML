(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML
    Author:     Lawrence C Paulson and Claire Quigley, Cambridge University Computer Laboratory

Transfer of proofs from external provers.
*)

signature SLEDGEHAMMER_PROOF_RECONSTRUCT =
sig
  type minimize_command = string list -> string

  val chained_hint: string
  val invert_const: string -> string
  val invert_type_const: string -> string
  val num_typargs: theory -> string -> int
  val make_tvar: string -> typ
  val strip_prefix: string -> string -> string option
  val is_proof_well_formed: string -> bool
  val metis_line: int -> int -> string list -> string
  val metis_proof_text:
    minimize_command * string * string vector * thm * int
    -> string * string list
  val isar_proof_text:
    bool -> int -> bool -> Proof.context
    -> minimize_command * string * string vector * thm * int
    -> string * string list
  val proof_text:
    bool -> bool -> int -> bool -> Proof.context
    -> minimize_command * string * string vector * thm * int
    -> string * string list
end;

structure Sledgehammer_Proof_Reconstruct : SLEDGEHAMMER_PROOF_RECONSTRUCT =
struct

open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor

type minimize_command = string list -> string

val trace_proof_path = Path.basic "atp_trace";

fun trace_proof_msg f =
  if !trace then File.append (File.tmp_path trace_proof_path) (f ()) else ();

fun string_of_thm ctxt = PrintMode.setmp [] (Display.string_of_thm ctxt);

(**** PARSING OF TSTP FORMAT ****)

(*Syntax trees, either termlist or formulae*)
datatype stree = Int of int | Br of string * stree list;

fun atom x = Br(x,[]);

fun scons (x,y) = Br("cons", [x,y]);
val listof = List.foldl scons (atom "nil");

(*Strings enclosed in single quotes, e.g. filenames*)
val quoted = $$"'" |-- Scan.repeat (~$$"'") --| $$"'" >> implode;

(*Intended for $true and $false*)
fun tf s = "c_" ^ str (Char.toUpper (String.sub(s,0))) ^ String.extract(s,1,NONE);
val truefalse = $$"$" |-- Symbol.scan_id >> (atom o tf);

(*Integer constants, typically proof line numbers*)
fun is_digit s = Char.isDigit (String.sub(s,0));
val integer = Scan.many1 is_digit >> (the o Int.fromString o implode);

(*Generalized FO terms, which include filenames, numbers, etc.*)
fun termlist x = (term ::: Scan.repeat ($$"," |-- term)) x
and term x = (quoted >> atom || integer>>Int || truefalse ||
              Symbol.scan_id -- Scan.optional ($$"(" |-- termlist --| $$")") [] >> Br ||
              $$"(" |-- term --| $$")" ||
              $$"[" |-- Scan.optional termlist [] --| $$"]" >> listof) x;

fun negate t = Br("c_Not", [t]);
fun equate (t1,t2) = Br("c_equal", [t1,t2]);

(*Apply equal or not-equal to a term*)
fun syn_equal (t, NONE) = t
  | syn_equal (t1, SOME (NONE, t2)) = equate (t1,t2)
  | syn_equal (t1, SOME (SOME _, t2)) = negate (equate (t1,t2));

(*Literals can involve negation, = and !=.*)
fun literal x = ($$"~" |-- literal >> negate ||
                 (term -- Scan.option (Scan.option ($$"!") --| $$"=" -- term) >> syn_equal)) x;

val literals = literal ::: Scan.repeat ($$"|" |-- literal);

(*Clause: a list of literals separated by the disjunction sign*)
val clause = $$"(" |-- literals --| $$")" || Scan.single literal;

val annotations = $$"," |-- term -- Scan.option ($$"," |-- termlist);

(*<cnf_annotated> ::= cnf(<name>,<formula_role>,<cnf_formula><annotations>).
  The <name> could be an identifier, but we assume integers.*)
val tstp_line = (Scan.this_string "cnf" -- $$"(") |--
                integer --| $$"," -- Symbol.scan_id --| $$"," --
                clause -- Scan.option annotations --| $$ ")";


(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception STREE of stree;

(*If string s has the prefix s1, return the result of deleting it.*)
fun strip_prefix s1 s =
  if String.isPrefix s1 s
  then SOME (undo_ascii_of (String.extract (s, size s1, NONE)))
  else NONE;

(*Invert the table of translations between Isabelle and ATPs*)
val type_const_trans_table_inv =
      Symtab.make (map swap (Symtab.dest type_const_trans_table));

fun invert_type_const c =
    case Symtab.lookup type_const_trans_table_inv c of
        SOME c' => c'
      | NONE => c;

fun make_tvar s = TVar (("'" ^ s, 0), HOLogic.typeS);
fun make_tparam s = TypeInfer.param 0 (s, HOLogic.typeS)
fun make_var (b,T) = Var((b,0),T);

(*Type variables are given the basic sort, HOL.type. Some will later be constrained
  by information from type literals, or by type inference.*)
fun type_of_stree t =
  case t of
      Int _ => raise STREE t
    | Br (a,ts) =>
        let val Ts = map type_of_stree ts
        in
          case strip_prefix tconst_prefix a of
              SOME b => Type(invert_type_const b, Ts)
            | NONE =>
                if not (null ts) then raise STREE t  (*only tconsts have type arguments*)
                else
                case strip_prefix tfree_prefix a of
                    SOME b => TFree("'" ^ b, HOLogic.typeS)
                  | NONE =>
                case strip_prefix tvar_prefix a of
                    SOME b => make_tvar b
                  | NONE => make_tparam a  (* Variable from the ATP, say "X1" *)
        end;

(*Invert the table of translations between Isabelle and ATPs*)
val const_trans_table_inv =
      Symtab.update ("fequal", "op =")
        (Symtab.make (map swap (Symtab.dest const_trans_table)));

fun invert_const c =
    case Symtab.lookup const_trans_table_inv c of
        SOME c' => c'
      | NONE => c;

(*The number of type arguments of a constant, zero if it's monomorphic*)
fun num_typargs thy s = length (Sign.const_typargs thy (s, Sign.the_const_type thy s));

(*Generates a constant, given its type arguments*)
fun const_of thy (a,Ts) = Const(a, Sign.const_instance thy (a,Ts));

(*First-order translation. No types are known for variables. HOLogic.typeT should allow
  them to be inferred.*)
fun term_of_stree args thy t =
  case t of
      Int _ => raise STREE t
    | Br ("hBOOL",[t]) => term_of_stree [] thy t  (*ignore hBOOL*)
    | Br ("hAPP",[t,u]) => term_of_stree (u::args) thy t
    | Br (a,ts) =>
        case strip_prefix const_prefix a of
            SOME "equal" =>
              list_comb(Const (@{const_name "op ="}, HOLogic.typeT), List.map (term_of_stree [] thy) ts)
          | SOME b =>
              let val c = invert_const b
                  val nterms = length ts - num_typargs thy c
                  val us = List.map (term_of_stree [] thy) (List.take(ts,nterms) @ args)
                  (*Extra args from hAPP come AFTER any arguments given directly to the
                    constant.*)
                  val Ts = List.map type_of_stree (List.drop(ts,nterms))
              in  list_comb(const_of thy (c, Ts), us)  end
          | NONE => (*a variable, not a constant*)
              let val T = HOLogic.typeT
                  val opr = (*a Free variable is typically a Skolem function*)
                    case strip_prefix fixed_var_prefix a of
                        SOME b => Free(b,T)
                      | NONE =>
                    case strip_prefix schematic_var_prefix a of
                        SOME b => make_var (b,T)
                      | NONE => make_var (a,T)    (*Variable from the ATP, say X1*)
              in  list_comb (opr, List.map (term_of_stree [] thy) (ts@args))  end;

(*Type class literal applied to a type. Returns triple of polarity, class, type.*)
fun constraint_of_stree pol (Br("c_Not",[t])) = constraint_of_stree (not pol) t
  | constraint_of_stree pol t = case t of
        Int _ => raise STREE t
      | Br (a,ts) =>
            (case (strip_prefix class_prefix a, map type_of_stree ts) of
                 (SOME b, [T]) => (pol, b, T)
               | _ => raise STREE t);

(** Accumulate type constraints in a clause: negative type literals **)

fun addix (key,z)  = Vartab.map_default (key,[]) (cons z);

fun add_constraint ((false, cl, TFree(a,_)), vt) = addix ((a,~1),cl) vt
  | add_constraint ((false, cl, TVar(ix,_)), vt) = addix (ix,cl) vt
  | add_constraint (_, vt) = vt;

(*False literals (which E includes in its proofs) are deleted*)
val nofalses = filter (not o equal HOLogic.false_const);

(*Final treatment of the list of "real" literals from a clause.*)
fun finish [] = HOLogic.true_const  (*No "real" literals means only type information*)
  | finish lits =
      case nofalses lits of
          [] => HOLogic.false_const  (*The empty clause, since we started with real literals*)
        | xs => foldr1 HOLogic.mk_disj (rev xs);

(*Accumulate sort constraints in vt, with "real" literals in lits.*)
fun lits_of_strees _ (vt, lits) [] = (vt, finish lits)
  | lits_of_strees ctxt (vt, lits) (t::ts) =
      lits_of_strees ctxt (add_constraint (constraint_of_stree true t, vt), lits) ts
      handle STREE _ =>
      lits_of_strees ctxt (vt, term_of_stree [] (ProofContext.theory_of ctxt) t :: lits) ts;

(*Update TVars/TFrees with detected sort constraints.*)
fun fix_sorts vt =
  let fun tysubst (Type (a, Ts)) = Type (a, map tysubst Ts)
        | tysubst (TVar (xi, s)) = TVar (xi, the_default s (Vartab.lookup vt xi))
        | tysubst (TFree (x, s)) = TFree (x, the_default s (Vartab.lookup vt (x, ~1)))
      fun tmsubst (Const (a, T)) = Const (a, tysubst T)
        | tmsubst (Free (a, T)) = Free (a, tysubst T)
        | tmsubst (Var (xi, T)) = Var (xi, tysubst T)
        | tmsubst (t as Bound _) = t
        | tmsubst (Abs (a, T, t)) = Abs (a, tysubst T, tmsubst t)
        | tmsubst (t $ u) = tmsubst t $ tmsubst u;
  in not (Vartab.is_empty vt) ? tmsubst end;

(*Interpret a list of syntax trees as a clause, given by "real" literals and sort constraints.
  vt0 holds the initial sort constraints, from the conjecture clauses.*)
fun clause_of_strees ctxt vt0 ts =
  let val (vt, dt) = lits_of_strees ctxt (vt0,[]) ts in
    singleton (Syntax.check_terms ctxt) (TypeInfer.constrain HOLogic.boolT (fix_sorts vt dt))
  end

fun gen_all_vars t = fold_rev Logic.all (OldTerm.term_vars t) t;

fun ints_of_stree_aux (Int n, ns) = n::ns
  | ints_of_stree_aux (Br(_,ts), ns) = List.foldl ints_of_stree_aux ns ts;

fun ints_of_stree t = ints_of_stree_aux (t, []);

fun decode_tstp vt0 (name, role, ts, annots) ctxt =
  let val deps = case annots of NONE => [] | SOME (source,_) => ints_of_stree source
      val cl = clause_of_strees ctxt vt0 ts
  in  ((name, role, cl, deps), fold Variable.declare_term (OldTerm.term_frees cl) ctxt)  end;

fun dest_tstp ((((name, role), ts), annots), chs) =
  case chs of
          "."::_ => (name, role, ts, annots)
        | _ => error ("TSTP line not terminated by \".\": " ^ implode chs);


(** Global sort constraints on TFrees (from tfree_tcs) are positive unit clauses. **)

fun add_tfree_constraint ((true, cl, TFree(a,_)), vt) = addix ((a,~1),cl) vt
  | add_tfree_constraint (_, vt) = vt;

fun tfree_constraints_of_clauses vt [] = vt
  | tfree_constraints_of_clauses vt ([lit]::tss) =
      (tfree_constraints_of_clauses (add_tfree_constraint (constraint_of_stree true lit, vt)) tss
       handle STREE _ => (*not a positive type constraint: ignore*)
       tfree_constraints_of_clauses vt tss)
  | tfree_constraints_of_clauses vt (_::tss) = tfree_constraints_of_clauses vt tss;


(**** Translation of TSTP files to Isar Proofs ****)

fun decode_tstp_list ctxt tuples =
  let val vt0 = tfree_constraints_of_clauses Vartab.empty (map #3 tuples)
  in  #1 (fold_map (decode_tstp vt0) tuples ctxt) end;

(** Finding a matching assumption. The literals may be permuted, and variable names
    may disagree. We have to try all combinations of literals (quadratic!) and
    match up the variable names consistently. **)

fun strip_alls_aux n (Const(@{const_name all}, _)$Abs(a,T,t))  =
      strip_alls_aux (n+1) (subst_bound (Var ((a,n), T), t))
  | strip_alls_aux _ t  =  t;

val strip_alls = strip_alls_aux 0;

exception MATCH_LITERAL;

(*Ignore types: they are not to be trusted...*)
fun match_literal (t1$u1) (t2$u2) env =
      match_literal t1 t2 (match_literal u1 u2 env)
  | match_literal (Abs (_,_,t1)) (Abs (_,_,t2)) env =
      match_literal t1 t2 env
  | match_literal (Bound i1) (Bound i2) env =
      if i1=i2 then env else raise MATCH_LITERAL
  | match_literal (Const(a1,_)) (Const(a2,_)) env =
      if a1=a2 then env else raise MATCH_LITERAL
  | match_literal (Free(a1,_)) (Free(a2,_)) env =
      if a1=a2 then env else raise MATCH_LITERAL
  | match_literal (Var(ix1,_)) (Var(ix2,_)) env = insert (op =) (ix1,ix2) env
  | match_literal _ _ _ = raise MATCH_LITERAL;

(*Checking that all variable associations are unique. The list env contains no
  repetitions, but does it contain say (x,y) and (y,y)? *)
fun good env =
  let val (xs,ys) = ListPair.unzip env
  in  not (has_duplicates (op=) xs orelse has_duplicates (op=) ys)  end;

(*Match one list of literals against another, ignoring types and the order of
  literals. Sorting is unreliable because we don't have types or variable names.*)
fun matches_aux _ [] [] = true
  | matches_aux env (lit::lits) ts =
      let fun match1 us [] = false
            | match1 us (t::ts) =
                let val env' = match_literal lit t env
                in  (good env' andalso matches_aux env' lits (us@ts)) orelse
                    match1 (t::us) ts
                end
                handle MATCH_LITERAL => match1 (t::us) ts
      in  match1 [] ts  end;

(*Is this length test useful?*)
fun matches (lits1,lits2) =
  length lits1 = length lits2  andalso
  matches_aux [] (map Envir.eta_contract lits1) (map Envir.eta_contract lits2);

fun permuted_clause t =
  let val lits = HOLogic.disjuncts t
      fun perm [] = NONE
        | perm (ctm::ctms) =
            if matches (lits, HOLogic.disjuncts (HOLogic.dest_Trueprop (strip_alls ctm)))
            then SOME ctm else perm ctms
  in perm end;

(*ctms is a list of conjecture clauses as yielded by Isabelle. Those returned by the
  ATP may have their literals reordered.*)
fun isar_proof_body ctxt sorts ctms =
  let
    val _ = trace_proof_msg (K "\n\nisar_proof_body: start\n")
    val string_of_term = 
      PrintMode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                              (print_mode_value ()))
                      (Syntax.string_of_term ctxt)
    fun have_or_show "show" _ = "  show \""
      | have_or_show have lname = "  " ^ have ^ " " ^ lname ^ ": \""
    fun do_line _ (lname, t, []) =
       (* No depedencies: it's a conjecture clause, with no proof. *)
       (case permuted_clause t ctms of
          SOME u => "  assume " ^ lname ^ ": \"" ^ string_of_term u ^ "\"\n"
        | NONE => raise TERM ("Sledgehammer_Proof_Reconstruct.isar_proof_body",
                              [t]))
      | do_line have (lname, t, deps) =
        have_or_show have lname ^
        string_of_term (gen_all_vars (HOLogic.mk_Trueprop t)) ^
        "\"\n    by (metis " ^ space_implode " " deps ^ ")\n"
    fun do_lines [(lname, t, deps)] = [do_line "show" (lname, t, deps)]
      | do_lines ((lname, t, deps) :: lines) =
        do_line "have" (lname, t, deps) :: do_lines lines
  in setmp_CRITICAL show_sorts sorts do_lines end;

fun unequal t (_, t', _) = not (t aconv t');

(*No "real" literals means only type information*)
fun eq_types t = t aconv HOLogic.true_const;

fun replace_dep (old:int, new) dep = if dep=old then new else [dep];

fun replace_deps (old:int, new) (lno, t, deps) =
      (lno, t, List.foldl (uncurry (union (op =))) [] (map (replace_dep (old, new)) deps));

(*Discard axioms; consolidate adjacent lines that prove the same clause, since they differ
  only in type information.*)
fun add_prfline ((lno, "axiom", t, []), lines) =  (*axioms are not proof lines*)
      if eq_types t (*must be clsrel/clsarity: type information, so delete refs to it*)
      then map (replace_deps (lno, [])) lines
      else
       (case take_prefix (unequal t) lines of
           (_,[]) => lines                  (*no repetition of proof line*)
         | (pre, (lno', _, _) :: post) =>   (*repetition: replace later line by earlier one*)
             pre @ map (replace_deps (lno', [lno])) post)
  | add_prfline ((lno, _, t, []), lines) =  (*no deps: conjecture clause*)
      (lno, t, []) :: lines
  | add_prfline ((lno, _, t, deps), lines) =
      if eq_types t then (lno, t, deps) :: lines
      (*Type information will be deleted later; skip repetition test.*)
      else (*FIXME: Doesn't this code risk conflating proofs involving different types??*)
      case take_prefix (unequal t) lines of
         (_,[]) => (lno, t, deps) :: lines  (*no repetition of proof line*)
       | (pre, (lno', t', _) :: post) =>
           (lno, t', deps) ::               (*repetition: replace later line by earlier one*)
           (pre @ map (replace_deps (lno', [lno])) post);

(*Recursively delete empty lines (type information) from the proof.*)
fun add_nonnull_prfline ((lno, t, []), lines) = (*no dependencies, so a conjecture clause*)
     if eq_types t (*must be type information, tfree_tcs, clsrel, clsarity: delete refs to it*)
     then delete_dep lno lines
     else (lno, t, []) :: lines
  | add_nonnull_prfline ((lno, t, deps), lines) = (lno, t, deps) :: lines
and delete_dep lno lines = List.foldr add_nonnull_prfline [] (map (replace_deps (lno, [])) lines);

fun bad_free (Free (a,_)) = String.isPrefix skolem_prefix a
  | bad_free _ = false;

(*TVars are forbidden in goals. Also, we don't want lines with <2 dependencies.
  To further compress proofs, setting modulus:=n deletes every nth line, and nlines
  counts the number of proof lines processed so far.
  Deleted lines are replaced by their own dependencies. Note that the "add_nonnull_prfline"
  phase may delete some dependencies, hence this phase comes later.*)
fun add_wanted_prfline ctxt _ ((lno, t, []), (nlines, lines)) =
      (nlines, (lno, t, []) :: lines)   (*conjecture clauses must be kept*)
  | add_wanted_prfline ctxt modulus ((lno, t, deps), (nlines, lines)) =
      if eq_types t orelse not (null (Term.add_tvars t [])) orelse
         exists_subterm bad_free t orelse
         (not (null lines) andalso   (*final line can't be deleted for these reasons*)
          (length deps < 2 orelse nlines mod modulus <> 0))
      then (nlines+1, map (replace_deps (lno, deps)) lines) (*Delete line*)
      else (nlines+1, (lno, t, deps) :: lines);

(*Replace numeric proof lines by strings, either from thm_names or sequential line numbers*)
fun stringify_deps thm_names deps_map [] = []
  | stringify_deps thm_names deps_map ((lno, t, deps) :: lines) =
      if lno <= Vector.length thm_names  (*axiom*)
      then (Vector.sub(thm_names,lno-1), t, []) :: stringify_deps thm_names deps_map lines
      else let val lname = Int.toString (length deps_map)
               fun fix lno = if lno <= Vector.length thm_names
                             then SOME(Vector.sub(thm_names,lno-1))
                             else AList.lookup op= deps_map lno;
           in  (lname, t, map_filter fix (distinct (op=) deps)) ::
               stringify_deps thm_names ((lno,lname)::deps_map) lines
           end;

fun isar_proof_start i =
  (if i = 1 then "" else "prefer " ^ string_of_int i ^ "\n") ^
  "proof (neg_clausify)\n";
fun isar_fixes [] = ""
  | isar_fixes ts = "  fix " ^ space_implode " " ts ^ "\n";
fun isar_proof_end 1 = "qed"
  | isar_proof_end _ = "next"

fun isar_proof_from_tstp_file cnfs modulus sorts ctxt goal i thm_names =
  let
    val _ = trace_proof_msg (K "\nisar_proof_from_tstp_file: start\n")
    val tuples = map (dest_tstp o tstp_line o explode) cnfs
    val _ = trace_proof_msg (fn () =>
      Int.toString (length tuples) ^ " tuples extracted\n")
    val ctxt = ProofContext.set_mode ProofContext.mode_schematic ctxt
    val raw_lines = List.foldr add_prfline [] (decode_tstp_list ctxt tuples)
    val _ = trace_proof_msg (fn () =>
      Int.toString (length raw_lines) ^ " raw_lines extracted\n")
    val nonnull_lines = List.foldr add_nonnull_prfline [] raw_lines
    val _ = trace_proof_msg (fn () =>
      Int.toString (length nonnull_lines) ^ " nonnull_lines extracted\n")
    val (_, lines) = List.foldr (add_wanted_prfline ctxt modulus) (0,[]) nonnull_lines
    val _ = trace_proof_msg (fn () =>
      Int.toString (length lines) ^ " lines extracted\n")
    val (ccls, fixes) = neg_conjecture_clauses ctxt goal i
    val _ = trace_proof_msg (fn () =>
      Int.toString (length ccls) ^ " conjecture clauses\n")
    val ccls = map forall_intr_vars ccls
    val _ = app (fn th => trace_proof_msg
                              (fn () => "\nccl: " ^ string_of_thm ctxt th)) ccls
    val body = isar_proof_body ctxt sorts (map prop_of ccls)
                               (stringify_deps thm_names [] lines)
    val n = Logic.count_prems (prop_of goal)
    val _ = trace_proof_msg (K "\nisar_proof_from_tstp_file: finishing\n")
  in
    isar_proof_start i ^ isar_fixes (map #1 fixes) ^ implode body ^
    isar_proof_end n ^ "\n"
  end
  handle STREE _ => raise Fail "Cannot parse ATP output";


(*=== EXTRACTING PROOF-TEXT === *)

val begin_proof_strs = ["# SZS output start CNFRefutation.",
  "=========== Refutation ==========",
  "Here is a proof"];

val end_proof_strs = ["# SZS output end CNFRefutation",
  "======= End of refutation =======",
  "Formulae used in the proof"];

fun get_proof_extract proof =
  (* Splits by the first possible of a list of splitters. *)
  case pairself (find_first (fn s => String.isSubstring s proof))
                (begin_proof_strs, end_proof_strs) of
    (SOME begin_string, SOME end_string) =>
    proof |> first_field begin_string |> the |> snd
          |> first_field end_string |> the |> fst
  | _ => raise Fail "Cannot extract proof"

(* ==== CHECK IF PROOF WAS SUCCESSFUL === *)

fun is_proof_well_formed proof =
  forall (exists (fn s => String.isSubstring s proof))
         [begin_proof_strs, end_proof_strs]

(* === EXTRACTING LEMMAS === *)
(* A list consisting of the first number in each line is returned.
   TPTP: Interesting lines have the form "cnf(108, axiom, ...)", where the
   number (108) is extracted.
   DFG: Lines have the form "108[0:Inp] ...", where the first number (108) is
   extracted. *)
fun get_step_nums proof_extract =
  let
    val toks = String.tokens (not o Char.isAlphaNum)
    fun inputno ("cnf" :: ntok :: "axiom" :: _) = Int.fromString ntok
      | inputno ("cnf" :: ntok :: "negated" :: "conjecture" :: _) =
        Int.fromString ntok
      | inputno (ntok::"0"::"Inp"::_) = Int.fromString ntok  (* DFG format *)
      | inputno _ = NONE
    val lines = split_lines proof_extract
  in map_filter (inputno o toks) lines end
  
(*Used to label theorems chained into the sledgehammer call*)
val chained_hint = "CHAINED";
val kill_chained = filter_out (curry (op =) chained_hint)

fun apply_command _ 1 = "by "
  | apply_command 1 _ = "apply "
  | apply_command i _ = "prefer " ^ string_of_int i ^ " apply "
fun metis_command i n [] =
    apply_command i n ^ "metis"
  | metis_command i n xs =
    apply_command i n ^ "(metis " ^ space_implode " " xs ^ ")"
fun metis_line i n xs =
  "Try this command: " ^
  Markup.markup Markup.sendback (metis_command i n xs) ^ ".\n" 
fun minimize_line _ [] = ""
  | minimize_line minimize_command facts =
    case minimize_command facts of
      "" => ""
    | command =>
      "To minimize the number of lemmas, try this command: " ^
      Markup.markup Markup.sendback command ^ ".\n"

fun metis_proof_text (minimize_command, proof, thm_names, goal, i) =
  let
    val lemmas =
      proof |> get_proof_extract
            |> get_step_nums
            |> filter (fn i => i <= Vector.length thm_names)
            |> map (fn i => Vector.sub (thm_names, i - 1))
            |> filter (fn x => x <> "??.unknown")
            |> sort_distinct string_ord
    val n = Logic.count_prems (prop_of goal)
    val xs = kill_chained lemmas
  in
    (metis_line i n xs ^ minimize_line minimize_command xs, kill_chained lemmas)
  end

fun isar_proof_text debug modulus sorts ctxt
                    (minimize_command, proof, thm_names, goal, i) =
  let
    (* We could use "split_lines", but it can return blank lines. *)
    val lines = String.tokens (equal #"\n");
    val kill_spaces =
      String.translate (fn c => if Char.isSpace c then "" else str c)
    val extract = get_proof_extract proof
    val cnfs = filter (String.isPrefix "cnf(") (map kill_spaces (lines extract))
    val (one_line_proof, lemma_names) =
      metis_proof_text (minimize_command, proof, thm_names, goal, i)
    val tokens = String.tokens (fn c => c = #" ") one_line_proof
    fun isar_proof_for () =
      case isar_proof_from_tstp_file cnfs modulus sorts ctxt goal i thm_names of
        "" => ""
      | isar_proof =>
        "\nStructured proof:\n" ^ Markup.markup Markup.sendback isar_proof
    val isar_proof =
      if member (op =) tokens chained_hint then
        ""
      else if debug then
        isar_proof_for ()
      else
        try isar_proof_for ()
        |> the_default "Warning: The Isar proof construction failed.\n"
  in (one_line_proof ^ isar_proof, lemma_names) end

fun proof_text isar_proof debug modulus sorts ctxt =
  if isar_proof then isar_proof_text debug modulus sorts ctxt
  else metis_proof_text

end;
