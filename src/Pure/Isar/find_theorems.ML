(*  Title:      Pure/Isar/find_theorems.ML
    ID:         $Id$
    Author:     Rafal Kolanski, NICTA and Tobias Nipkow, TU Muenchen

Retrieve theorems from proof context.
*)

val thms_containing_limit = ref 40;

signature FIND_THEOREMS =
sig
  val find_thms: Proof.context -> FactIndex.spec -> (thmref * thm) list
  val find_intros: Proof.context -> term -> (thmref * thm) list
  val find_intros_goal: Proof.context -> thm -> int -> (thmref * thm) list
  val find_elims: Proof.context -> term -> (thmref * thm) list
  datatype search_criterion =
    Name of string | Intro | Elim | Dest | Rewrite of string | Pattern of string
  val print_theorems: Proof.context -> term option -> int option ->
    (bool * search_criterion) list -> unit
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


(* intro/elim rules *)

(*match statement against conclusion of some rule*)
val find_intros =
  find_matching_thms (single, Logic.strip_imp_concl);

(*match conclusion of subgoal i against conclusion of some rule*)
fun find_intros_goal ctxt st i =
  find_intros ctxt (Logic.concl_of_goal (Thm.prop_of st) i);

(*match statement against major premise of some rule*)
val find_elims = find_matching_thms
  (fn thm => if Thm.no_prems thm then [] else [thm],
   hd o Logic.strip_imp_prems);



(** search criteria **)

datatype search_criterion =
  Name of string | Intro | Elim | Dest | Rewrite of string | Pattern of string;

fun string_of_crit (Name name) = "name: " ^ quote name
  | string_of_crit Intro = "intro"
  | string_of_crit Elim = "elim"
  | string_of_crit Dest = "dest"
  | string_of_crit (Rewrite s) = "rewrite: " ^ quote s
  | string_of_crit (Pattern s) = quote s;

fun string_of_criterion (b, c) = (if b then "" else "-") ^ string_of_crit c;



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


(* filter_intro *)

(*checking conclusion of theorem against conclusion of goal*)
fun filter_intro ctxt goal =
  let
    val extract_intro = (single, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
  in is_matching_thm extract_intro ctxt concl end;


(* filter_elim_dest *)

(*for elimination and destruction rules, we must check if the major
  premise matches with one of the assumptions in the top subgoal, but
  we must additionally make sure that we tell elim/dest apart, using
  check_thm (cf. is_elim_rule below)*)
fun filter_elim_dest check_thm ctxt goal =
  let
    val extract_elim =
     (fn thm => if Thm.no_prems thm then [] else [thm],
      hd o Logic.strip_imp_prems);

    val prems = Logic.prems_of_goal goal 1;
  in
    fn fact => List.exists (fn prem =>
      is_matching_thm extract_elim ctxt prem fact andalso check_thm (#2 fact)) prems
  end;

(*elimination rule: conclusion is a Var which does not appears in the
  major premise*)
fun is_elim_rule thm =
  let
    val prop = Thm.prop_of thm;
    val concl = ObjectLogic.drop_judgment (Thm.sign_of_thm thm) (Logic.strip_imp_concl prop);
    val major_prem = hd (Logic.strip_imp_prems prop);
    val prem_vars = Drule.vars_of_terms [major_prem];
  in
    Term.is_Var concl andalso not (Term.dest_Var concl mem prem_vars)
  end;


(* filter_rewrite *)

fun filter_rewrite ctxt str =
  let
    val (_, {mk_rews = {mk, ...}, ...}) =
      MetaSimplifier.rep_ss (Simplifier.local_simpset_of ctxt);
    val extract_rewrite = (mk, #1 o Logic.dest_equals o Logic.strip_imp_concl);
  in is_matching_thm extract_rewrite ctxt (ProofContext.read_term ctxt str) end;


(* filter_pattern *)

(*subterm pattern supplied as raw string*)
fun filter_pattern ctxt str =
  let
    val tsig = Sign.tsig_of (ProofContext.sign_of ctxt);
    val [pat] = ProofContext.read_term_pats TypeInfer.logicT ctxt [str];
  in fn (_, thm) => Pattern.matches_subterm tsig (pat, Thm.prop_of thm) end;


(* interpret criteria as filters *)

fun filter_crit _ _ (Name name) = filter_name name
  | filter_crit ctxt _ (Rewrite str) = filter_rewrite ctxt str
  | filter_crit ctxt _ (Pattern str) = filter_pattern ctxt str
  (*beyond this point, only criteria requiring a goal!*)
  | filter_crit _ NONE c =
      error ("Need to have a current goal to use " ^ string_of_crit c)
  | filter_crit ctxt (SOME goal) Intro = filter_intro ctxt goal
  | filter_crit ctxt (SOME goal) Elim = filter_elim_dest is_elim_rule ctxt goal
  | filter_crit ctxt (SOME goal) Dest =
      filter_elim_dest (not o is_elim_rule) ctxt goal;
      (*in this case all that is not elim is dest*)

fun filter_criterion ctxt opt_goal (b, c) =
  (if b then I else not) o filter_crit ctxt opt_goal c;

fun all_filters filters = List.filter (fn x => List.all (fn f => f x) filters);


(* print_theorems *)

fun print_theorems ctxt opt_goal opt_limit criteria =
  let
    fun prt_fact (thmref, thm) =
      ProofContext.pretty_fact ctxt (PureThy.string_of_thmref thmref, [thm]);
    val prt_crit = Pretty.str o string_of_criterion;

    val all_facts = find_thms ctxt ([], []);
    val filters = map (filter_criterion ctxt opt_goal) criteria;
    val matches = all_filters filters all_facts;

    val len = length matches;
    val limit = if_none opt_limit (! thms_containing_limit);
    val count = Int.min (limit, len);

    val pruned = len <= limit;
    val found = "found " ^ string_of_int len ^ " theorems" ^
      (if pruned then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":";
  in
    Pretty.big_list "searched for:" (map prt_crit criteria) ::
     (if null matches then [Pretty.str "nothing found"]
      else
       [Pretty.str "", Pretty.str found] @
       (if pruned then [] else [Pretty.str "..."]) @
       map prt_fact (Library.drop (len - limit, matches)))
    |> Pretty.chunks |> Pretty.writeln
  end;

end;
