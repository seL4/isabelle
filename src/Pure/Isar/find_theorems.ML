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


(* matching theorems *)

local

(*returns all those facts whose subterm extracted by extract can be
  instantiated to obj; the list is sorted according to the number of premises
  and the size of the required substitution*)
fun select_match (extract_thms, extract_term) ctxt obj facts =
  let
    val match = #2 o Pattern.match (Sign.tsig_of (ProofContext.sign_of ctxt));

    fun match_size pat =
      let val subst = match (pat, obj)  (*exception Pattern.MATCH*)
      in SOME (Vartab.foldl (op + o apsnd (Term.size_of_term o #2 o #2)) (0, subst)) end
      handle Pattern.MATCH => NONE;

    fun select (fact as (_, thm)) =
      let
        fun first_match (th :: ths) res =
              (case match_size (extract_term (Thm.prop_of th)) of
                SOME s => ((Thm.nprems_of th, s), fact) :: res
              | NONE => first_match ths res)
          | first_match [] res = res;
      in first_match (extract_thms thm) end;

    fun thm_ord (((p0, s0), _), ((p1, s1), _)) =
      prod_ord (int_ord o pairself (fn 0 => 0 | x => 1)) int_ord ((p0, s0), (p1, s1));
  in
    fold select facts []
    |> Library.sort thm_ord |> map #2
  end;

(*speed up retrieval by checking head symbol*)
fun index_head ctxt prop =
  (case Term.head_of (ObjectLogic.drop_judgment (ProofContext.sign_of ctxt) prop) of
    Const (c, _) => ([c], [])
  | Free (x, _) => if ProofContext.is_known ctxt x then ([], [x]) else ([], [])
  | _ => ([], []));

in

fun find_matching_thms extract ctxt prop =
  find_thms ctxt (index_head ctxt prop)
  |> select_match extract ctxt prop;

fun is_matching_thm extract ctxt prop fact =
  not (null (select_match extract ctxt prop [fact]));

end;



(** search criteria **)

datatype 'term criterion =
  Name of string | Intro | Elim | Dest | Simp of 'term | Pattern of 'term;

fun read_criterion _ (Name name) = Name name
  | read_criterion _ Intro = Intro
  | read_criterion _ Elim = Elim
  | read_criterion _ Dest = Dest
  | read_criterion ctxt (Simp str) = Simp (ProofContext.read_term ctxt str)
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
    | Simp t => Pretty.block [Pretty.str (prfx "simp:"), Pretty.brk 1,
        Pretty.quote (ProofContext.pretty_term ctxt t)]
    | Pattern pat => Pretty.enclose (prfx " \"") "\""
        [ProofContext.pretty_term ctxt (Term.show_dummy_patterns pat)])
  end;



(** search criterion filters **)

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

fun filter_elim_dest check_thm ctxt goal =
  let
    val extract_elim =
     (fn thm => if Thm.no_prems thm then [] else [thm],
      hd o Logic.strip_imp_prems);
    val prems = Logic.prems_of_goal goal 1;
  in
    fn fact => prems |> List.exists (fn prem =>
      is_matching_thm extract_elim ctxt prem fact
      andalso (check_thm ctxt) (#2 fact))
  end;

in

fun filter_intro ctxt goal =
  let
    val extract_intro = (single, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
  in
    fn fact => is_matching_thm extract_intro ctxt concl fact
      andalso not (is_elim ctxt (#2 fact))
  end;

fun filter_elim ctxt = filter_elim_dest is_elim ctxt;
fun filter_dest ctxt = filter_elim_dest (not oo is_elim) ctxt;

end;


(* filter_simp *)

fun filter_simp ctxt t =
  let
    val (_, {mk_rews = {mk, ...}, ...}) =
      MetaSimplifier.rep_ss (Simplifier.local_simpset_of ctxt);
    val extract_simp = (mk, #1 o Logic.dest_equals o Logic.strip_imp_concl);
  in is_matching_thm extract_simp ctxt t end;


(* filter_pattern *)

fun filter_pattern ctxt pat =
  let val tsig = Sign.tsig_of (ProofContext.sign_of ctxt)
  in fn (_, thm) => Pattern.matches_subterm tsig (pat, Thm.prop_of thm) end;


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
  | filter_crit ctxt _ (Simp str) = filter_simp ctxt str
  | filter_crit ctxt _ (Pattern str) = filter_pattern ctxt str;

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
