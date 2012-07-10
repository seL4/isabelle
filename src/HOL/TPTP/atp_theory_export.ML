(*  Title:      HOL/TPTP/atp_theory_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2011

Export Isabelle theories as MaSh (Machine-learning for Sledgehammer) or as
first-order TPTP inferences.
*)

signature ATP_THEORY_EXPORT =
sig
  type atp_format = ATP_Problem.atp_format

  val theorems_mentioned_in_proof_term :
    string list option -> thm -> string list
  val generate_mash_accessibility_file_for_theory :
    theory -> bool -> string -> unit
  val generate_mash_feature_file_for_theory : theory -> bool -> string -> unit
  val generate_mash_dependency_file_for_theory :
    theory -> bool -> string -> unit
  val generate_mash_problem_file_for_theory : theory -> string -> unit
  val generate_tptp_inference_file_for_theory :
    Proof.context -> theory -> atp_format -> string -> string -> unit
end;

structure ATP_Theory_Export (* ### : ATP_THEORY_EXPORT *) =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open ATP_Systems
open ATP_Util

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n =
    stringN_of_int (k - 1) (n div 10) ^ string_of_int (n mod 10)

fun escape_meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse
     c = #")" orelse c = #"?" orelse c = #"," then
    String.str c
  else if c = #"'" then
    "~"
  else
    (* fixed width, in case more digits follow *)
    "\\" ^ stringN_of_int 3 (Char.ord c)
val escape_meta = String.translate escape_meta_char

val thy_prefix = "y_"

val fact_name_of = escape_meta
val thy_name_of = prefix thy_prefix o escape_meta
val const_name_of = prefix const_prefix o escape_meta
val type_name_of = prefix type_const_prefix o escape_meta
val class_name_of = prefix class_prefix o escape_meta

val thy_name_of_thm = theory_of_thm #> Context.theory_name

fun has_thy thy th = (Context.theory_name thy = thy_name_of_thm th)

fun facts_of thy =
  let val ctxt = Proof_Context.init_global thy in
    Sledgehammer_Filter.all_facts ctxt false Symtab.empty true [] []
        (Sledgehammer_Filter.clasimpset_rule_table_of ctxt)
    |> filter (curry (op =) @{typ bool} o fastype_of
               o Object_Logic.atomize_term thy o prop_of o snd)
    |> rev
  end

(* FIXME: Similar yet different code in "mirabelle.ML". The code here has a few
   fixes that seem to be missing over there; or maybe the two code portions are
   not doing the same? *)
fun fold_body_thms thm_name f =
  let
    fun app n (PBody {thms, ...}) =
      thms |> fold (fn (_, (name, prop, body)) => fn x =>
        let
          val body' = Future.join body
          val n' =
            n + (if name = "" orelse
                    (* uncommon case where the proved theorem occurs twice
                       (e.g., "Transitive_Closure.trancl_into_trancl") *)
                    (n = 1 andalso name = thm_name) then
                   0
                 else
                   1)
          val x' = x |> n' <= 1 ? app n' body'
        in (x' |> n = 1 ? f (name, prop, body')) end)
  in fold (app 0) end

fun theorems_mentioned_in_proof_term all_names th =
  let
    val is_name_ok =
      case all_names of
        SOME names => member (op =) names
      | NONE => (fn s => s <> "" andalso not (String.isPrefix "Pure." s))
    fun collect (s, _, _) = is_name_ok s ? insert (op =) s
    val names =
      [] |> fold_body_thms (Thm.get_name_hint th) collect [Thm.proof_body_of th]
         |> map fact_name_of
  in names end

fun interesting_terms_types_and_classes thy term_max_depth type_max_depth t =
  let
    val ctxt = Proof_Context.init_global thy
    val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]
    val bad_consts = atp_widely_irrelevant_consts
    val add_classes =
      subtract (op =) @{sort type} #> map class_name_of #> union (op =)
    fun add_type (Type (s, Ts)) =
        (not (member (op =) bad_types s) ? insert (op =) (type_name_of s))
        #> fold add_type Ts
      | add_type (TFree (_, S)) = add_classes S
      | add_type (TVar (_, S)) = add_classes S
    fun mk_app s args =
      if member (op <>) args "?" then s ^ "(" ^ space_implode "," args ^ ")"
      else s
    fun patternify 0 t = "?"
      | patternify depth t =
        case strip_comb t of
          (Const (s, _), args) =>
          mk_app (const_name_of s) (map (patternify (depth - 1)) args)
        | _ => "?"
    fun add_term_patterns depth t =
      if depth < 0 then
        I
      else
        insert (op =) (patternify depth t)
        #> add_term_patterns (depth - 1) t
    val add_term = add_term_patterns term_max_depth
    fun add_patterns t =
      let val (head, args) = strip_comb t in
        (case head of
           Const (s, T) =>
           not (member (op =) bad_consts s) ? (add_term t #> add_type T)
         | Free (_, T) => add_type T
         | Var (_, T) => add_type T
         | Abs (_, T, body) => add_type T #> add_patterns body
         | _ => I)
        #> fold add_patterns args
      end
  in [] |> add_patterns t |> sort string_ord end

fun theory_ord p =
  if Theory.eq_thy p then EQUAL
  else if Theory.subthy p then LESS
  else if Theory.subthy (swap p) then GREATER
  else EQUAL

val thm_ord = theory_ord o pairself theory_of_thm

fun parent_thms thy_ths thy =
  Theory.parents_of thy
  |> map Context.theory_name
  |> map_filter (AList.lookup (op =) thy_ths)
  |> map List.last
  |> map (fact_name_of o Thm.get_name_hint)

val thms_by_thy =
  map (snd #> `thy_name_of_thm)
  #> AList.group (op =)
  #> sort (int_ord
           o pairself (length o Theory.ancestors_of o theory_of_thm o hd o snd))
  #> map (apsnd (sort thm_ord))

fun generate_mash_accessibility_file_for_theory thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_thm th prevs =
      let
        val s = th ^ ": " ^ space_implode " " prevs ^ "\n"
        val _ = File.append path s
      in [th] end
    val thy_ths =
      facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> thms_by_thy
    fun do_thy ths =
      let
        val thy = theory_of_thm (hd ths)
        val parents = parent_thms thy_ths thy
        val ths = ths |> map (fact_name_of o Thm.get_name_hint)
        val _ = fold do_thm ths parents
      in () end
    val _ = List.app (do_thy o snd) thy_ths
  in () end

fun has_bool @{typ bool} = true
  | has_bool (Type (_, Ts)) = exists has_bool Ts
  | has_bool _ = false

fun has_fun (Type (@{type_name fun}, _)) = true
  | has_fun (Type (_, Ts)) = exists has_fun Ts
  | has_fun _ = false

val is_conn = member (op =)
  [@{const_name Trueprop}, @{const_name HOL.conj}, @{const_name HOL.disj},
   @{const_name HOL.implies}, @{const_name Not},
   @{const_name All}, @{const_name Ex}, @{const_name Ball}, @{const_name Bex},
   @{const_name HOL.eq}]

val has_bool_arg_const =
  exists_Const (fn (c, T) =>
                   not (is_conn c) andalso exists has_bool (binder_types T))

fun higher_inst_const thy (c, T) =
  case binder_types T of
    [] => false
  | Ts => length (binder_types (Sign.the_const_type thy c)) <> length Ts

val binders = [@{const_name All}, @{const_name Ex}]

fun is_fo_term thy t =
  let
    val t =
      t |> Envir.beta_eta_contract
        |> transform_elim_prop
        |> Object_Logic.atomize_term thy
  in
    Term.is_first_order binders t andalso
    not (exists_subterm (fn Var (_, T) => has_bool T orelse has_fun T
                          | _ => false) t orelse
         has_bool_arg_const t orelse exists_Const (higher_inst_const thy) t)
  end

val is_abs = String.isSubstring Sledgehammer_Filter.pseudo_abs_name

val max_depth = 1

(* TODO: Add types, subterms *)
fun features_of thy (status, th) =
  let val prop = Thm.prop_of th in
    thy_name_of (thy_name_of_thm th) ::
    interesting_terms_types_and_classes thy max_depth max_depth prop
    (* ### skolem and "abs" *)
    |> not (is_fo_term thy prop) ? cons "ho"
    |> (case status of
          General => I
        | Induction => cons "induction"
        | Intro => cons "intro"
        | Inductive => cons "inductive"
        | Elim => cons "elim"
        | Simp => cons "simp"
        | Def => cons "def")
  end

fun generate_mash_feature_file_for_theory thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = facts_of thy |> not include_thy ? filter_out (has_thy thy o snd)
    fun do_fact ((_, (_, status)), th) =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy (status, th)
        val s = fact_name_of name ^ ": " ^ space_implode " " feats ^ "\n"
      in File.append path s end
    val _ = List.app do_fact facts
  in () end

val dependencies_of = theorems_mentioned_in_proof_term o SOME

val known_tautologies =
  [@{thm All_def}, @{thm Ex_def}, @{thm Ex1_def}, @{thm Ball_def},
   @{thm Bex_def}, @{thm If_def}]

fun is_likely_tautology thy th =
  (member Thm.eq_thm_prop known_tautologies th orelse
   th |> prop_of |> interesting_terms_types_and_classes thy 0 ~1 |> null) andalso
  not (Thm.eq_thm_prop (@{thm ext}, th))

fun generate_mash_dependency_file_for_theory thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val ths =
      facts_of thy |> not include_thy ? filter_out (has_thy thy o snd)
                   |> map snd
    val all_names =
      ths |> filter_out (is_likely_tautology thy) |> map Thm.get_name_hint
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val deps = dependencies_of all_names th
        val s = fact_name_of name ^ ": " ^ space_implode " " deps ^ "\n"
      in File.append path s end
    val _ = List.app do_thm ths
  in () end

fun generate_mash_problem_file_for_theory thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = facts_of thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    val ths = facts |> map snd
    val all_names =
      ths |> filter_out (is_likely_tautology thy) |> map Thm.get_name_hint
    fun do_fact ((_, (_, status)), th) prevs =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy (status, th)
        val deps = dependencies_of all_names th
        val th = fact_name_of name
        val s =
          th ^ ": " ^
          space_implode " " prevs ^ "; " ^
          space_implode " " feats ^ "; " ^
          space_implode " " deps ^ "\n"
        val _ = File.append path s
      in [th] end
    val thy_ths = old_facts |> thms_by_thy
    val parents = parent_thms thy_ths thy
    val _ = fold do_fact new_facts parents
  in () end

fun inference_term [] = NONE
  | inference_term ss =
    ATerm (("inference", []),
           [ATerm (("isabelle", []), []),
            ATerm ((tptp_empty_list, []), []),
            ATerm ((tptp_empty_list, []),
            map (fn s => ATerm ((s, []), [])) ss)])
    |> SOME
fun inference infers ident =
  these (AList.lookup (op =) infers ident) |> inference_term
fun add_inferences_to_problem_line infers
                                   (Formula (ident, Axiom, phi, NONE, tms)) =
    Formula (ident, Lemma, phi, inference infers ident, tms)
  | add_inferences_to_problem_line _ line = line
fun add_inferences_to_problem infers =
  map (apsnd (map (add_inferences_to_problem_line infers)))

fun ident_of_problem_line (Class_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Type_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Sym_Decl (ident, _, _)) = ident
  | ident_of_problem_line (Class_Memb (ident, _, _, _)) = ident
  | ident_of_problem_line (Formula (ident, _, _, _, _)) = ident

fun run_some_atp ctxt format problem =
  let
    val thy = Proof_Context.theory_of ctxt
    val prob_file = File.tmp_path (Path.explode "prob")
    val atp = case format of DFG _ => spassN | _ => eN
    val {exec, arguments, proof_delims, known_failures, ...} =
      get_atp thy atp ()
    val ord = effective_term_order ctxt atp
    val _ = problem |> lines_for_atp_problem format ord (K [])
                    |> File.write_list prob_file
    val path = getenv (List.last (fst exec)) ^ "/" ^ snd exec
    val command =
      File.shell_path (Path.explode path) ^
      " " ^ arguments ctxt false "" (seconds 1.0) (ord, K [], K []) ^ " " ^
      File.shell_path prob_file
  in
    TimeLimit.timeLimit (seconds 0.3) Isabelle_System.bash_output command
    |> fst
    |> extract_tstplike_proof_and_outcome false true proof_delims known_failures
    |> snd
  end
  handle TimeLimit.TimeOut => SOME TimedOut

val tautology_prefixes =
  [@{theory HOL}, @{theory Meson}, @{theory ATP}, @{theory Metis}]
  |> map (fact_name_of o Context.theory_name)

fun is_problem_line_tautology ctxt format (Formula (ident, _, phi, _, _)) =
    exists (fn prefix => String.isPrefix prefix ident)
           tautology_prefixes andalso
    is_none (run_some_atp ctxt format
                 [(factsN, [Formula (ident, Conjecture, phi, NONE, [])])])
  | is_problem_line_tautology _ _ _ = false

fun order_facts ord = sort (ord o pairself ident_of_problem_line)
fun order_problem_facts _ [] = []
  | order_problem_facts ord ((heading, lines) :: problem) =
    if heading = factsN then (heading, order_facts ord lines) :: problem
    else (heading, lines) :: order_problem_facts ord problem

(* A fairly random selection of types used for monomorphizing. *)
val ground_types =
  [@{typ nat}, HOLogic.intT, HOLogic.realT, @{typ "nat => bool"}, @{typ bool},
   @{typ unit}]

fun ground_type_for_tvar _ [] tvar =
    raise TYPE ("ground_type_for_sorts", [TVar tvar], [])
  | ground_type_for_tvar thy (T :: Ts) tvar =
    if can (Sign.typ_match thy (TVar tvar, T)) Vartab.empty then T
    else ground_type_for_tvar thy Ts tvar

fun monomorphize_term ctxt t =
  let val thy = Proof_Context.theory_of ctxt in
    t |> map_types (map_type_tvar (ground_type_for_tvar thy ground_types))
    handle TYPE _ => @{prop True}
  end

fun generate_tptp_inference_file_for_theory ctxt thy format type_enc file_name =
  let
    val type_enc = type_enc |> type_enc_from_string Strict
                            |> adjust_type_enc format
    val mono = not (is_type_enc_polymorphic type_enc)
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = facts_of thy
    val atp_problem =
      facts
      |> map (fn ((_, loc), th) =>
                 ((Thm.get_name_hint th, loc),
                   th |> prop_of |> mono ? monomorphize_term ctxt))
      |> prepare_atp_problem ctxt format Axiom type_enc Exporter combsN false
                             false true [] @{prop False}
      |> #1
    val atp_problem =
      atp_problem
      |> map (apsnd (filter_out (is_problem_line_tautology ctxt format)))
    val ths = facts |> map snd
    val all_names =
      ths |> filter_out (is_likely_tautology thy) |> map Thm.get_name_hint
    val infers =
      facts |> map (fn (_, th) =>
                       (fact_name_of (Thm.get_name_hint th),
                        theorems_mentioned_in_proof_term (SOME all_names) th))
    val all_atp_problem_names =
      atp_problem |> maps (map ident_of_problem_line o snd)
    val infers =
      infers |> filter (member (op =) all_atp_problem_names o fst)
             |> map (apsnd (filter (member (op =) all_atp_problem_names)))
    val ordered_names =
      String_Graph.empty
      |> fold (String_Graph.new_node o rpair ()) all_atp_problem_names
      |> fold (fn (to, froms) =>
                  fold (fn from => String_Graph.add_edge (from, to)) froms)
              infers
      |> String_Graph.topological_order
    val order_tab =
      Symtab.empty
      |> fold (Symtab.insert (op =))
              (ordered_names ~~ (1 upto length ordered_names))
    val name_ord = int_ord o pairself (the o Symtab.lookup order_tab)
    val atp_problem =
      atp_problem
      |> (case format of DFG _ => I | _ => add_inferences_to_problem infers)
      |> order_problem_facts name_ord
    val ord = effective_term_order ctxt eN (* dummy *)
    val ss = lines_for_atp_problem format ord (K []) atp_problem
    val _ = app (File.append path) ss
  in () end

end;
