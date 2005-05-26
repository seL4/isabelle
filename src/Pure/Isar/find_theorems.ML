(*  Title:      Pure/Isar/find_theorems.ML
    ID:         $Id$
    Author:     Rafal Kolanski, NICTA and Tobias Nipkow, TU Muenchen

Retrieve theorems from proof context.
*)

val thms_containing_limit = ref 40;

signature FIND_THEOREMS =
sig
  val find_thms: Proof.context -> FactIndex.spec -> (thmref * thm) list
  datatype 'term criterion =
    Name of string | Intro | Elim | Dest | Simp of 'term | Pattern of 'term
  val print_theorems: Proof.context -> term option -> int option ->
    (bool * string criterion) list -> unit
end;

structure FindTheorems: FIND_THEOREMS =
struct


(* find_thms *)

fun find_thms ctxt spec =
  (PureThy.thms_containing (ProofContext.theory_of ctxt) spec @
    ProofContext.lthms_containing ctxt spec)
  |> map PureThy.selections |> List.concat;



(** search criteria **)

datatype 'term criterion =
  Name of string | Intro | Elim | Dest | Simp of 'term | Pattern of 'term;

fun read_criterion _ (Name name) = Name name
  | read_criterion _ Intro = Intro
  | read_criterion _ Elim = Elim
  | read_criterion _ Dest = Dest
  | read_criterion ctxt (Simp str) = 
      Simp (hd (ProofContext.read_term_pats TypeInfer.logicT ctxt [str]))
  | read_criterion ctxt (Pattern str) =
      Pattern (hd (ProofContext.read_term_pats TypeInfer.logicT ctxt [str]));

fun pretty_criterion ctxt (b, c) =
  let
    fun prfx s = if b then s else "-" ^ s;
  in
    (case c of
      Name name => Pretty.str (prfx "name: " ^ quote name)
    | Intro => Pretty.str (prfx "intro")
    | Elim => Pretty.str (prfx "elim")
    | Dest => Pretty.str (prfx "dest")
    | Simp pat => Pretty.block [Pretty.str (prfx "simp:"), Pretty.brk 1,
        Pretty.quote (ProofContext.pretty_term ctxt (Term.show_dummy_patterns pat))]
    | Pattern pat => Pretty.enclose (prfx " \"") "\""
        [ProofContext.pretty_term ctxt (Term.show_dummy_patterns pat)])
  end;



(** search criterion filters **)


(* matching theorems *)

fun is_matching_thm (extract_thms, extract_term) ctxt po obj thm =
  let
    val sg = ProofContext.sign_of ctxt;
    val tsig = Sign.tsig_of sg;

    val is_nontrivial = is_Const o head_of o ObjectLogic.drop_judgment sg;    

    fun matches pat = 
      is_nontrivial pat andalso 
      Pattern.matches tsig (if po then (pat,obj) else (obj,pat))
      handle Pattern.MATCH => false;

    val match_thm = matches o extract_term o Thm.prop_of
  in       
    List.exists match_thm (extract_thms thm)
  end;


(* filter_name *)

fun is_substring pat str =
  if String.size pat = 0 then true
  else if String.size pat > String.size str then false
  else if String.substring (str, 0, String.size pat) = pat then true
  else is_substring pat (String.extract (str, 1, NONE));

(*filter that just looks for a string in the name,
  substring match only (no regexps are performed)*)
fun filter_name str_pat ((name, _), _) = is_substring str_pat name;


(* filter intro/elim/dest rules *)

local

(*elimination rule: conclusion is a Var which does not appear in the major premise*)
fun is_elim ctxt thm =
  let
    val sg = ProofContext.sign_of ctxt;
    val prop = Thm.prop_of thm;
    val concl = ObjectLogic.drop_judgment sg (Logic.strip_imp_concl prop);
    val major_prem = Library.take (1, Logic.strip_imp_prems prop);
    val prem_vars = Drule.vars_of_terms major_prem;
  in
    not (null major_prem) andalso
    Term.is_Var concl andalso
    not (Term.dest_Var concl mem prem_vars)
  end;

fun filter_elim_dest check_thm ctxt goal (_,thm) =
  let
    val extract_elim =
     (fn thm => if Thm.no_prems thm then [] else [thm],
      hd o Logic.strip_imp_prems);
    val prems = Logic.prems_of_goal goal 1;
  in
    prems |> 
    List.exists (fn prem => 
      is_matching_thm extract_elim ctxt true prem thm
      andalso (check_thm ctxt) thm)
  end;

in

fun filter_intro ctxt goal (_,thm) =
  let
    val extract_intro = (single, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
  in
    is_matching_thm extract_intro ctxt true concl thm
  end;

fun filter_elim ctxt = filter_elim_dest is_elim ctxt;
fun filter_dest ctxt = filter_elim_dest (not oo is_elim) ctxt;

end;


(* filter_simp *)

fun filter_simp ctxt t (_,thm) =
  let
    val (_, {mk_rews = {mk, ...}, ...}) =
      MetaSimplifier.rep_ss (Simplifier.local_simpset_of ctxt);
    val extract_simp = (mk, #1 o Logic.dest_equals o Logic.strip_imp_concl);
  in is_matching_thm extract_simp ctxt false t thm end;


(* filter_pattern *)

fun filter_pattern ctxt pat (_, thm) =
  let val tsig = Sign.tsig_of (ProofContext.sign_of ctxt)
  in Pattern.matches_subterm tsig (pat, Thm.prop_of thm) end;


(* interpret criteria as filters *)

local

fun err_no_goal c =
  error ("Current goal required for " ^ c ^ " search criterion");

fun filter_crit _ _ (Name name) = filter_name name
  | filter_crit _ NONE Intro = err_no_goal "intro"
  | filter_crit _ NONE Elim = err_no_goal "elim"
  | filter_crit _ NONE Dest = err_no_goal "dest"
  | filter_crit ctxt (SOME goal) Intro = filter_intro ctxt goal
  | filter_crit ctxt (SOME goal) Elim = filter_elim ctxt goal
  | filter_crit ctxt (SOME goal) Dest = filter_dest ctxt goal
  | filter_crit ctxt _ (Simp pat) = filter_simp ctxt pat
  | filter_crit ctxt _ (Pattern pat) = filter_pattern ctxt pat;

in

fun filter_criterion ctxt opt_goal (b, c) =
  (if b then I else not) o filter_crit ctxt opt_goal c;

fun all_filters filters = List.filter (fn x => List.all (fn f => f x) filters);

end;


(* print_theorems *)

fun print_theorems ctxt opt_goal opt_limit raw_criteria =
  let
    val criteria = map (apsnd (read_criterion ctxt)) raw_criteria;
    val filters = map (filter_criterion ctxt opt_goal) criteria;

    val matches = all_filters filters (find_thms ctxt ([], []));
    val len = length matches;
    val limit = if_none opt_limit (! thms_containing_limit);

    fun prt_fact (thmref, thm) =
      ProofContext.pretty_fact ctxt (PureThy.string_of_thmref thmref, [thm]);
  in
    Pretty.big_list "searched for:" (map (pretty_criterion ctxt) criteria) :: Pretty.str "" ::
     (if null matches then [Pretty.str "nothing found"]
      else
        [Pretty.str ("found " ^ string_of_int len ^ " theorems" ^
          (if len <= limit then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":"),
         Pretty.str ""] @
        map prt_fact (Library.drop (len - limit, matches)))
    |> Pretty.chunks |> Pretty.writeln
  end;

end;
