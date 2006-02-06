(*  Title:      Pure/Isar/find_theorems.ML
    ID:         $Id$
    Author:     Rafal Kolanski, NICTA and Tobias Nipkow, TU Muenchen

Retrieve theorems from proof context.
*)

val thms_containing_limit = ref 40;

signature FIND_THEOREMS =
sig
  datatype 'term criterion =
    Name of string | Intro | Elim | Dest | Simp of 'term | Pattern of 'term
  val print_theorems: Proof.context -> term option -> int option ->
    (bool * string criterion) list -> unit
end;

structure FindTheorems: FIND_THEOREMS =
struct

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

(*generated filters are to be of the form
  input: (thmref * thm)
  output: (p:int, s:int) option, where
    NONE indicates no match
    p is the primary sorting criterion
      (eg. number of assumptions in the theorem)
    s is the secondary sorting criterion
      (eg. size of the substitution for intro, elim and dest)
  when applying a set of filters to a thm, fold results in:
    (biggest p, sum of all s)
  currently p and s only matter for intro, elim, dest and simp filters,
  otherwise the default ordering is used.
*)


(* matching theorems *)

fun is_nontrivial thy = Term.is_Const o Term.head_of o ObjectLogic.drop_judgment thy;

(*extract terms from term_src, refine them to the parts that concern us,
  if po try match them against obj else vice versa.
  trivial matches are ignored.
  returns: smallest substitution size*)
fun is_matching_thm (extract_terms, refine_term) ctxt po obj term_src =
  let
    val thy = ProofContext.theory_of ctxt;

    fun matches pat =
      is_nontrivial thy pat andalso
      Pattern.matches thy (if po then (pat, obj) else (obj, pat));

    fun substsize pat =
      let val (_, subst) =
        Pattern.match thy (if po then (pat, obj) else (obj, pat)) (Vartab.empty, Vartab.empty)
      in Vartab.fold (fn (_, (_, t)) => fn n => size_of_term t + n) subst 0 end;

    fun bestmatch [] = NONE
     |  bestmatch xs = SOME (foldr1 Int.min xs);

    val match_thm = matches o refine_term;
  in
    map (substsize o refine_term)
        (List.filter match_thm (extract_terms term_src)) |> bestmatch
  end;


(* filter_name *)

fun match_string pat str =
  let
    fun match [] _ = true
      | match (p :: ps) s =
          size p <= size s andalso
            (case try (unprefix p) s of
              SOME s' => match ps s'
            | NONE => match (p :: ps) (String.substring (s, 1, size s - 1)));
  in match (space_explode "*" pat) str end;

fun filter_name str_pat (thmref, _) =
  if match_string str_pat (PureThy.name_of_thmref thmref)
  then SOME (0, 0) else NONE;


(* filter intro/elim/dest rules *)

fun filter_dest ctxt goal (_, thm) =
  let
    val extract_dest =
     (fn thm => if Thm.no_prems thm then [] else [Thm.full_prop_of thm],
      hd o Logic.strip_imp_prems);
    val prems = Logic.prems_of_goal goal 1;

    fun try_subst prem = is_matching_thm extract_dest ctxt true prem thm;
    val successful = prems |> List.mapPartial try_subst;
  in
    (*if possible, keep best substitution (one with smallest size)*)
    (*dest rules always have assumptions, so a dest with one
      assumption is as good as an intro rule with none*)
    if not (null successful)
    then SOME (Thm.nprems_of thm - 1, foldr1 Int.min successful) else NONE
  end;

fun filter_intro ctxt goal (_, thm) =
  let
    val extract_intro = (single o Thm.full_prop_of, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
    val ss = is_matching_thm extract_intro ctxt true concl thm;
  in
    if is_some ss then SOME (Thm.nprems_of thm, the ss) else NONE
  end;

fun filter_elim ctxt goal (_, thm) =
  if not (Thm.no_prems thm) then
    let
      val rule = Thm.full_prop_of thm;
      val prems = Logic.prems_of_goal goal 1;
      val goal_concl = Logic.concl_of_goal goal 1;
      val rule_mp = (hd o Logic.strip_imp_prems) rule;
      val rule_concl = Logic.strip_imp_concl rule;
      fun combine t1 t2 = Const ("combine", dummyT --> dummyT) $ (t1 $ t2);
      val rule_tree = combine rule_mp rule_concl;
      fun goal_tree prem = (combine prem goal_concl);
      fun try_subst prem =
        is_matching_thm (single, I) ctxt true (goal_tree prem) rule_tree;
      val successful = prems |> List.mapPartial try_subst;
    in
    (*elim rules always have assumptions, so an elim with one
      assumption is as good as an intro rule with none*)
      if is_nontrivial (ProofContext.theory_of ctxt) (Thm.major_prem_of thm)
        andalso not (null successful)
      then SOME (Thm.nprems_of thm - 1, foldr1 Int.min successful) else NONE
    end
  else NONE


(* filter_simp *)

fun filter_simp ctxt t (_, thm) =
  let
    val (_, {mk_rews = {mk, ...}, ...}) =
      MetaSimplifier.rep_ss (Simplifier.local_simpset_of ctxt);
    val extract_simp =
      (map Thm.full_prop_of o mk, #1 o Logic.dest_equals o Logic.strip_imp_concl);
    val ss = is_matching_thm extract_simp ctxt false t thm
  in
    if is_some ss then SOME (Thm.nprems_of thm, the ss) else NONE
  end;


(* filter_pattern *)

fun filter_pattern ctxt pat (_, thm) =
  if Pattern.matches_subterm (ProofContext.theory_of ctxt) (pat, Thm.full_prop_of thm)
  then SOME (0, 0) else NONE;


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

fun opt_not x = if isSome x then NONE else SOME (0, 0);

fun opt_add (SOME (a, x)) (SOME (b, y)) = SOME (Int.max (a, b), x + y : int)
 |  opt_add _ _ = NONE;

in

fun filter_criterion ctxt opt_goal (b, c) =
  (if b then I else opt_not) o filter_crit ctxt opt_goal c;

fun all_filters filters thms =
  let
    fun eval_filters filters thm =
      fold opt_add (map (fn f => f thm) filters) (SOME (0, 0));

    (*filters return: (number of assumptions, substitution size) option, so
      sort (desc. in both cases) according to number of assumptions first,
      then by the substitution size*)
    fun thm_ord (((p0, s0), _), ((p1, s1), _)) =
      prod_ord int_ord int_ord ((p1, s1), (p0, s0));
  in
    map (`(eval_filters filters)) thms
    |> List.mapPartial (fn (SOME x, y) => SOME (x, y) | (NONE, _) => NONE)
    |> sort thm_ord |> map #2
  end;

end;


(* print_theorems *)

fun find_thms ctxt spec =
  (PureThy.thms_containing (ProofContext.theory_of ctxt) spec
    |> map PureThy.selections
    |> List.concat) @
  (ProofContext.lthms_containing ctxt spec
    |> map PureThy.selections
    |> List.concat
    |> gen_distinct (fn ((r1, th1), (r2, th2)) =>
        r1 = r2 andalso Drule.eq_thm_prop (th1, th2)));

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
