(*  ID:         $Id$
    Author:     L C Paulson and Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a prover process         *)
(***************************************************************************)
signature RES_RECONSTRUCT =
  sig
    val checkEProofFound:
          TextIO.instream * TextIO.outstream * Posix.Process.pid *
          string * Proof.context * thm * int * string Vector.vector -> bool
    val checkVampProofFound:
          TextIO.instream * TextIO.outstream * Posix.Process.pid *
          string * Proof.context * thm * int * string Vector.vector -> bool
    val checkSpassProofFound:
          TextIO.instream * TextIO.outstream * Posix.Process.pid *
          string * Proof.context * thm * int * string Vector.vector -> bool
    val signal_parent:
          TextIO.outstream * Posix.Process.pid * string * string -> unit

  end;

structure ResReconstruct =
struct

val trace_path = Path.basic "atp_trace";

fun trace s = if !Output.debugging then File.append (File.tmp_path trace_path) s
              else ();

(*Full proof reconstruction wanted*)
val full = ref true;

val recon_sorts = ref true;

val modulus = ref 1;    (*keep every nth proof line*)

(**** PARSING OF TSTP FORMAT ****)

(*Syntax trees, either termlist or formulae*)
datatype stree = Int of int | Br of string * stree list;

fun atom x = Br(x,[]);

fun scons (x,y) = Br("cons", [x,y]);
val listof = foldl scons (atom "nil");

(*Strings enclosed in single quotes, e.g. filenames*)
val quoted = $$"'" |-- Scan.repeat (~$$"'") --| $$"'" >> implode;

(*Intended for $true and $false*)
fun tf s = "c_" ^ str (Char.toUpper (String.sub(s,0))) ^ String.extract(s,1,NONE);
val truefalse = $$"$" |-- Symbol.scan_id >> (atom o tf);

(*Integer constants, typically proof line numbers*)
fun is_digit s = Char.isDigit (String.sub(s,0));
val integer = Scan.many1 is_digit >> (valOf o Int.fromString o implode);

(*Generalized FO terms, which include filenames, numbers, etc.*)
fun termlist x = (term -- Scan.repeat ($$"," |-- term) >> op::) x
and term x = (quoted >> atom || integer>>Int || truefalse ||
              Symbol.scan_id -- Scan.optional ($$"(" |-- termlist --| $$")") [] >> Br ||
              $$"(" |-- term --| $$")" ||
              $$"[" |-- termlist --| $$"]" >> listof) x;

fun negate t = Br("c_Not", [t]);
fun equate (t1,t2) = Br("c_equal", [t1,t2]);

(*Apply equal or not-equal to a term*)
fun syn_equal (t, NONE) = t
  | syn_equal (t1, SOME (NONE, t2)) = equate (t1,t2)
  | syn_equal (t1, SOME (SOME _, t2)) = negate (equate (t1,t2));

(*Literals can involve negation, = and !=.*)
val literal = $$"~" |-- term >> negate ||
              (term -- Scan.option (Scan.option ($$"!") --| $$"=" -- term) >> syn_equal) ;

val literals = literal -- Scan.repeat ($$"|" |-- literal) >> op:: ;

(*Clause: a list of literals separated by the disjunction sign*)
val clause = $$"(" |-- literals --| $$")";

val annotations = $$"," |-- term -- Scan.option ($$"," |-- termlist);

(*<cnf_annotated> ::=Êcnf(<name>,<formula_role>,<cnf_formula><annotations>).
  The <name> could be an identifier, but we assume integers.*)
val tstp_line = (Scan.this_string "cnf" -- $$"(") |--
                integer --| $$"," -- Symbol.scan_id --| $$"," --
                clause -- Scan.option annotations --| $$ ")";


(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception STREE of stree;

(*If string s has the prefix s1, return the result of deleting it.*)
fun strip_prefix s1 s =
  if String.isPrefix s1 s 
  then SOME (ResClause.undo_ascii_of (String.extract (s, size s1, NONE)))
  else NONE;

(*Invert the table of translations between Isabelle and ATPs*)
val type_const_trans_table_inv =
      Symtab.make (map swap (Symtab.dest ResClause.type_const_trans_table));

fun invert_type_const c =
    case Symtab.lookup type_const_trans_table_inv c of
        SOME c' => c'
      | NONE => c;

fun make_tvar b = TVar(("'" ^ b, 0), HOLogic.typeS);
fun make_var (b,T) = Var((b,0),T);

(*Type variables are given the basic sort, HOL.type. Some will later be constrained
  by information from type literals, or by type inference.*)
fun type_of_stree t =
  case t of
      Int _ => raise STREE t
    | Br (a,ts) =>
        let val Ts = map type_of_stree ts
        in
          case strip_prefix ResClause.tconst_prefix a of
              SOME b => Type(invert_type_const b, Ts)
            | NONE =>
                if not (null ts) then raise STREE t  (*only tconsts have type arguments*)
                else
                case strip_prefix ResClause.tfree_prefix a of
                    SOME b => TFree("'" ^ b, HOLogic.typeS)
                  | NONE =>
                case strip_prefix ResClause.tvar_prefix a of
                    SOME b => make_tvar b
                  | NONE => make_tvar a   (*Variable from the ATP, say X1*)
        end;

(*Invert the table of translations between Isabelle and ATPs*)
val const_trans_table_inv =
      Symtab.update ("fequal", "op =")
        (Symtab.make (map swap (Symtab.dest ResClause.const_trans_table)));

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
        case strip_prefix ResClause.const_prefix a of
            SOME "equal" =>
              list_comb(Const ("op =", HOLogic.typeT), List.map (term_of_stree [] thy) ts)
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
                    case strip_prefix ResClause.fixed_var_prefix a of
                        SOME b => Free(b,T)
                      | NONE =>
                    case strip_prefix ResClause.schematic_var_prefix a of
                        SOME b => make_var (b,T)
                      | NONE => make_var (a,T)    (*Variable from the ATP, say X1*)
              in  list_comb (opr, List.map (term_of_stree [] thy) (ts@args))  end;

(*Type class literal applied to a type. Returns triple of polarity, class, type.*)
fun constraint_of_stree pol (Br("c_Not",[t])) = constraint_of_stree (not pol) t
  | constraint_of_stree pol t = case t of
        Int _ => raise STREE t
      | Br (a,ts) =>
            (case (strip_prefix ResClause.class_prefix a, map type_of_stree ts) of
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
fun lits_of_strees ctxt (vt, lits) [] = (vt, finish lits)
  | lits_of_strees ctxt (vt, lits) (t::ts) =
      lits_of_strees ctxt (add_constraint (constraint_of_stree true t, vt), lits) ts
      handle STREE _ =>
      lits_of_strees ctxt (vt, term_of_stree [] (ProofContext.theory_of ctxt) t :: lits) ts;

(*Update TVars/TFrees with detected sort constraints.*)
fun fix_sorts vt =
  let fun tysubst (Type (a, Ts)) = Type (a, map tysubst Ts)
        | tysubst (TVar (xi, s)) = TVar (xi, getOpt (Vartab.lookup vt xi, s))
        | tysubst (TFree (x, s)) = TFree (x, getOpt (Vartab.lookup vt (x,~1), s))
      fun tmsubst (Const (a, T)) = Const (a, tysubst T)
        | tmsubst (Free (a, T)) = Free (a, tysubst T)
        | tmsubst (Var (xi, T)) = Var (xi, tysubst T)
        | tmsubst (t as Bound _) = t
        | tmsubst (Abs (a, T, t)) = Abs (a, tysubst T, tmsubst t)
        | tmsubst (t $ u) = tmsubst t $ tmsubst u;
  in fn t => if Vartab.is_empty vt then t else tmsubst t end;

(*Interpret a list of syntax trees as a clause, given by "real" literals and sort constraints.
  vt0 holds the initial sort constraints, from the conjecture clauses.*)
fun clause_of_strees ctxt vt0 ts =
  let val (vt, dt) = lits_of_strees ctxt (vt0,[]) ts in
    singleton (ProofContext.infer_types ctxt) (TypeInfer.constrain (fix_sorts vt dt) HOLogic.boolT)
  end;

(*Quantification over a list of Vars. FIXME: for term.ML??*)
fun list_all_var ([], t: term) = t
  | list_all_var ((v as Var(ix,T)) :: vars, t) =
      (all T) $ Abs(string_of_indexname ix, T, abstract_over (v, list_all_var (vars,t)));

fun gen_all_vars t = list_all_var (term_vars t, t);

fun ints_of_stree_aux (Int n, ns) = n::ns
  | ints_of_stree_aux (Br(_,ts), ns) = foldl ints_of_stree_aux ns ts;

fun ints_of_stree t = ints_of_stree_aux (t, []);

fun decode_tstp ctxt vt0 (name, role, ts, annots) =
  let val deps = case annots of NONE => [] | SOME (source,_) => ints_of_stree source
  in  (name, role, clause_of_strees ctxt vt0 ts, deps)  end;

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
  in  map (decode_tstp ctxt vt0) tuples  end;

(*FIXME: simmilar function in res_atp. Move to HOLogic?*)
fun dest_disj_aux (Const ("op |", _) $ t $ t') disjs = dest_disj_aux t (dest_disj_aux t' disjs)
  | dest_disj_aux t disjs = t::disjs;

fun dest_disj t = dest_disj_aux t [];

(** Finding a matching assumption. The literals may be permuted, and variable names
    may disagree. We have to try all combinations of literals (quadratic!) and 
    match up the variable names consistently. **)

fun strip_alls_aux n (Const("all",_)$Abs(a,T,t))  =  
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
  | match_literal _ _ env = raise MATCH_LITERAL;

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
  let val lits = dest_disj t
      fun perm [] = NONE
        | perm (ctm::ctms) =
            if matches (lits, dest_disj (HOLogic.dest_Trueprop (strip_alls ctm)))
            then SOME ctm else perm ctms
  in perm end;

fun have_or_show "show " lname = "show \""
  | have_or_show have lname = have ^ lname ^ ": \""

(*ctms is a list of conjecture clauses as yielded by Isabelle. Those returned by the
  ATP may have their literals reordered.*)
fun isar_lines ctxt ctms =
  let val string_of = ProofContext.string_of_term ctxt
      fun doline have (lname, t, []) =  (*No deps: it's a conjecture clause, with no proof.*)
           (case permuted_clause t ctms of
                SOME u => "assume " ^ lname ^ ": \"" ^ string_of u ^ "\"\n"
              | NONE => "assume? " ^ lname ^ ": \"" ^ string_of t ^ "\"\n")  (*no match!!*)
        | doline have (lname, t, deps) =
            have_or_show have lname ^ string_of (gen_all_vars (HOLogic.mk_Trueprop t)) ^
            "\"\n  by (metis " ^ space_implode " " deps ^ ")\n"
      fun dolines [(lname, t, deps)] = [doline "show " (lname, t, deps)]
        | dolines ((lname, t, deps)::lines) = doline "have " (lname, t, deps) :: dolines lines
  in setmp show_sorts (!recon_sorts) dolines end;

fun notequal t (_,t',_) = not (t aconv t');

(*No "real" literals means only type information*)
fun eq_types t = t aconv HOLogic.true_const;

fun replace_dep (old:int, new) dep = if dep=old then new else [dep];

fun replace_deps (old:int, new) (lno, t, deps) =
      (lno, t, foldl (op union_int) [] (map (replace_dep (old, new)) deps));

(*Discard axioms; consolidate adjacent lines that prove the same clause, since they differ
  only in type information.*)
fun add_prfline ((lno, "axiom", t, []), lines) =  (*axioms are not proof lines*)
      if eq_types t (*must be clsrel/clsarity: type information, so delete refs to it*)
      then map (replace_deps (lno, [])) lines
      else
       (case take_prefix (notequal t) lines of
           (_,[]) => lines                  (*no repetition of proof line*)
         | (pre, (lno',t',deps')::post) =>  (*repetition: replace later line by earlier one*)
             pre @ map (replace_deps (lno', [lno])) post)
  | add_prfline ((lno, role, t, []), lines) =  (*no deps: conjecture clause*)
      (lno, t, []) :: lines
  | add_prfline ((lno, role, t, deps), lines) =
      if eq_types t then (lno, t, deps) :: lines
      (*Type information will be deleted later; skip repetition test.*)
      else (*FIXME: Doesn't this code risk conflating proofs involving different types??*)
      case take_prefix (notequal t) lines of
         (_,[]) => (lno, t, deps) :: lines  (*no repetition of proof line*)
       | (pre, (lno',t',deps')::post) =>
           (lno, t', deps) ::               (*repetition: replace later line by earlier one*)
           (pre @ map (replace_deps (lno', [lno])) post);

(*Recursively delete empty lines (type information) from the proof.*)
fun add_nonnull_prfline ((lno, t, []), lines) = (*no dependencies, so a conjecture clause*)
     if eq_types t (*must be type information, tfree_tcs, clsrel, clsarity: delete refs to it*)
     then delete_dep lno lines
     else (lno, t, []) :: lines
  | add_nonnull_prfline ((lno, t, deps), lines) = (lno, t, deps) :: lines
and delete_dep lno lines = foldr add_nonnull_prfline [] (map (replace_deps (lno, [])) lines);

fun bad_free (Free (a,_)) = String.isPrefix "llabs_" a orelse String.isPrefix "sko_" a
  | bad_free _ = false;

(*TVars are forbidden in goals. Also, we don't want lines with <2 dependencies.
  To further compress proofs, setting modulus:=n deletes every nth line, and nlines
  counts the number of proof lines processed so far.
  Deleted lines are replaced by their own dependencies. Note that the "add_nonnull_prfline"
  phase may delete some dependencies, hence this phase comes later.*)
fun add_wanted_prfline ((lno, t, []), (nlines, lines)) =
      (nlines, (lno, t, []) :: lines)   (*conjecture clauses must be kept*)
  | add_wanted_prfline (line, (nlines, [])) = (nlines, [line])   (*final line must be kept*)
  | add_wanted_prfline ((lno, t, deps), (nlines, lines)) =
      if eq_types t orelse not (null (term_tvars t)) orelse
         length deps < 2 orelse nlines mod !modulus <> 0 orelse
         exists bad_free (term_frees t)
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
           in  (lname, t, List.mapPartial fix (distinct (op=) deps)) ::
               stringify_deps thm_names ((lno,lname)::deps_map) lines
           end;

val proofstart = "\nproof (neg_clausify)\n";

fun isar_header [] = proofstart
  | isar_header ts = proofstart ^ "fix " ^ space_implode " " ts ^ "\n";

fun decode_tstp_file cnfs ctxt th sgno thm_names =
  let val tuples = map (dest_tstp o tstp_line o explode) cnfs
      val nonnull_lines =
              foldr add_nonnull_prfline []
                    (foldr add_prfline [] (decode_tstp_list ctxt tuples))
      val (_,lines) = foldr add_wanted_prfline (0,[]) nonnull_lines
      val (ccls,fixes) = ResAxioms.neg_conjecture_clauses th sgno
      val ccls = map forall_intr_vars ccls
  in
    app (fn th => Output.debug (fn () => string_of_thm th)) ccls;
    isar_header (map #1 fixes) ^
    String.concat (isar_lines ctxt (map prop_of ccls) (stringify_deps thm_names [] lines))
  end;

(*Could use split_lines, but it can return blank lines...*)
val lines = String.tokens (equal #"\n");

val nospaces = String.translate (fn c => if Char.isSpace c then "" else str c);

val txt_path = Path.ext "txt" o Path.explode o nospaces;

fun signal_success probfile toParent ppid msg =
  let val _ = trace ("\nReporting Success for " ^ probfile ^ "\n" ^ msg)
  in
    (*We write the proof to a file because sending very long lines may fail...*)
    File.write (txt_path probfile) msg;
    TextIO.output (toParent, "Success.\n");
    TextIO.output (toParent, probfile ^ "\n");
    TextIO.flushOut toParent;
    Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
    (*Give the parent time to respond before possibly sending another signal*)
    OS.Process.sleep (Time.fromMilliseconds 600)
  end;

fun tstp_extract proofextract probfile toParent ppid ctxt th sgno thm_names =
  let val cnfs = filter (String.isPrefix "cnf(") (map nospaces (lines proofextract))
  in
    signal_success probfile toParent ppid
      (decode_tstp_file cnfs ctxt th sgno thm_names)
  end;


(**** retrieve the axioms that were used in the proof ****)

(*Get names of axioms used. Axioms are indexed from 1, while the vector is indexed from 0*)
fun get_axiom_names (thm_names: string vector) step_nums =
    let fun is_axiom n = n <= Vector.length thm_names
        fun index i = Vector.sub(thm_names, i-1)
        val axnums = List.filter is_axiom step_nums
        val axnames = sort_distinct string_ord (map index axnums)
    in
	if length axnums = length step_nums then "UNSOUND!!" :: axnames
	else axnames
    end

 (*String contains multiple lines. We want those of the form
     "253[0:Inp] et cetera..."
  A list consisting of the first number in each line is returned. *)
fun get_spass_linenums proofstr =
  let val toks = String.tokens (not o Char.isAlphaNum)
      fun inputno (ntok::"0"::"Inp"::_) = Int.fromString ntok
        | inputno _ = NONE
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (inputno o toks) lines  end

fun get_axiom_names_spass proofstr thm_names =
   get_axiom_names thm_names (get_spass_linenums proofstr);

fun not_comma c = c <>  #",";

(*A valid TSTP axiom line has the form  cnf(NNN,axiom,...) where NNN is a positive integer.*)
fun parse_tstp_line s =
  let val ss = Substring.full (unprefix "cnf(" (nospaces s))
      val (intf,rest) = Substring.splitl not_comma ss
      val (rolef,rest) = Substring.splitl not_comma (Substring.triml 1 rest)
      (*We only allow negated_conjecture because the line number will be removed in
        get_axiom_names above, while suppressing the UNSOUND warning*)
      val ints = if Substring.string rolef mem_string ["axiom","negated_conjecture"]
                 then Substring.string intf
                 else "error"
  in  Int.fromString ints  end
  handle Fail _ => NONE;

fun get_axiom_names_tstp proofstr thm_names =
   get_axiom_names thm_names (List.mapPartial parse_tstp_line (split_lines proofstr));

 (*String contains multiple lines. We want those of the form
     "*********** [448, input] ***********".
  A list consisting of the first number in each line is returned. *)
fun get_vamp_linenums proofstr =
  let val toks = String.tokens (not o Char.isAlphaNum)
      fun inputno [ntok,"input"] = Int.fromString ntok
        | inputno _ = NONE
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (inputno o toks) lines  end

fun get_axiom_names_vamp proofstr thm_names =
   get_axiom_names thm_names (get_vamp_linenums proofstr);

fun rules_to_metis [] = "metis"
  | rules_to_metis xs = "(metis " ^ space_implode " " xs ^ ")"


(*The signal handler in watcher.ML must be able to read the output of this.*)
fun prover_lemma_list_aux getax proofstr probfile toParent ppid thm_names =
 (trace ("\n\nGetting lemma names. proofstr is " ^ proofstr ^
         " num of clauses is " ^ string_of_int (Vector.length thm_names));
  signal_success probfile toParent ppid
    ("Try this command: \n  apply " ^ rules_to_metis (getax proofstr thm_names))
 )
 handle e => (*FIXME: exn handler is too general!*)
  (trace ("\nprover_lemma_list_aux: In exception handler: " ^ Toplevel.exn_message e);
   TextIO.output (toParent, "Translation failed for the proof: " ^
                  String.toString proofstr ^ "\n");
   TextIO.output (toParent, probfile);
   TextIO.flushOut toParent;
   Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2));

val e_lemma_list = prover_lemma_list_aux get_axiom_names_tstp;

val vamp_lemma_list = prover_lemma_list_aux get_axiom_names_vamp;

val spass_lemma_list = prover_lemma_list_aux get_axiom_names_spass;


(**** Extracting proofs from an ATP's output ****)

(*Return everything in s that comes before the string t*)
fun cut_before t s =
  let val (s1,s2) = Substring.position t (Substring.full s)
  in  if Substring.size s2 = 0 then error "cut_before: string not found"
      else Substring.string s2
  end;

val start_E = "# Proof object starts here."
val end_E   = "# Proof object ends here."
val start_V6 = "%================== Proof: ======================"
val end_V6   = "%==============  End of proof. =================="
val start_V8 = "=========== Refutation =========="
val end_V8 = "======= End of refutation ======="
val end_SPASS = "Formulae used in the proof"

(*********************************************************************************)
(*  Inspect the output of an ATP process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

(*Returns "true" if it successfully returns a lemma list, otherwise "false", but this
  return value is currently never used!*)
fun startTransfer endS (fromChild, toParent, ppid, probfile, ctxt, th, sgno, thm_names) =
 let fun transferInput currentString =
      (case TextIO.inputLine fromChild of
        NONE =>  (*end of file?*)
	  (trace ("\n extraction_failed.  End bracket: " ^ endS ^
	          "\naccumulated text: " ^ currentString);
	   false)
      | SOME thisLine =>
	if String.isPrefix endS thisLine
	then let val proofextract = currentString ^ cut_before endS thisLine
	         val lemma_list = if endS = end_V8 then vamp_lemma_list
			  	  else if endS = end_SPASS then spass_lemma_list
			  	  else e_lemma_list
	     in
	       trace ("\nExtracted proof:\n" ^ proofextract);
	       if !full andalso String.isPrefix "cnf(" proofextract
	       then tstp_extract proofextract probfile toParent ppid ctxt th sgno thm_names
	       else lemma_list proofextract probfile toParent ppid thm_names;
	       true
	     end
	else transferInput (currentString^thisLine))
 in
     transferInput ""
 end


(*The signal handler in watcher.ML must be able to read the output of this.*)
fun signal_parent (toParent, ppid, msg, probfile) =
 (TextIO.output (toParent, msg);
  TextIO.output (toParent, probfile ^ "\n");
  TextIO.flushOut toParent;
  trace ("\nSignalled parent: " ^ msg ^ probfile);
  Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
  (*Give the parent time to respond before possibly sending another signal*)
  OS.Process.sleep (Time.fromMilliseconds 600));

(*FIXME: once TSTP output is produced by all ATPs, these three functions can be combined.*)

(*Called from watcher. Returns true if the Vampire process has returned a verdict.*)
fun checkVampProofFound (arg as (fromChild, toParent, ppid, probfile, ctxt, th, sgno, thm_names)) =
  (case TextIO.inputLine fromChild of
    NONE => (trace "\nNo proof output seen"; false)
  | SOME thisLine =>
     if String.isPrefix start_V8 thisLine
     then startTransfer end_V8 arg
     else if (String.isPrefix "Satisfiability detected" thisLine) orelse
             (String.isPrefix "Refutation not found" thisLine)
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else checkVampProofFound arg);

(*Called from watcher. Returns true if the E process has returned a verdict.*)
fun checkEProofFound (arg as (fromChild, toParent, ppid, probfile, ctxt, th, sgno, thm_names)) =
  (case TextIO.inputLine fromChild of
    NONE => (trace "\nNo proof output seen"; false)
  | SOME thisLine =>
     if String.isPrefix start_E thisLine
     then startTransfer end_E arg
     else if String.isPrefix "# Problem is satisfiable" thisLine
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if String.isPrefix "# Cannot determine problem status within resource limit" thisLine
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else checkEProofFound arg);

(*Called from watcher. Returns true if the SPASS process has returned a verdict.*)
fun checkSpassProofFound (arg as (fromChild, toParent, ppid, probfile, ctxt, th, sgno, thm_names)) =
  (case TextIO.inputLine fromChild of
    NONE => (trace "\nNo proof output seen"; false)
  | SOME thisLine =>
     if String.isPrefix "Here is a proof" thisLine
     then startTransfer end_SPASS arg
     else if thisLine = "SPASS beiseite: Completion found.\n"
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if thisLine = "SPASS beiseite: Ran out of time.\n" orelse
             thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n"
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
    else checkSpassProofFound arg);

end;
