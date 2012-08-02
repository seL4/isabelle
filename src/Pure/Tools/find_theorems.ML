(*  Title:      Pure/Tools/find_theorems.ML
    Author:     Rafal Kolanski and Gerwin Klein, NICTA
    Author:     Lars Noschinski and Alexander Krauss, TU Muenchen

Retrieve theorems from proof context.
*)

signature FIND_THEOREMS =
sig
  datatype 'term criterion =
    Name of string | Intro | Elim | Dest | Solves | Simp of 'term | Pattern of 'term

  datatype theorem =
    Internal of Facts.ref * thm | External of Facts.ref * term

  type 'term query = {
    goal: thm option,
    limit: int option,
    rem_dups: bool,
    criteria: (bool * 'term criterion) list
  }

  val tac_limit: int Unsynchronized.ref
  val limit: int Unsynchronized.ref

  val read_criterion: Proof.context -> string criterion -> term criterion
  val query_parser: (bool * string criterion) list parser

  val xml_of_query: term query -> XML.tree
  val query_of_xml: XML.tree -> term query
  val xml_of_result: int option * theorem list -> XML.tree
  val result_of_xml: XML.tree -> int option * theorem list

  val find_theorems: Proof.context -> thm option -> int option -> bool ->
    (bool * term criterion) list -> int option * (Facts.ref * thm) list
  val find_theorems_cmd: Proof.context -> thm option -> int option -> bool ->
    (bool * string criterion) list -> int option * (Facts.ref * thm) list

  val filter_theorems: Proof.context -> theorem list -> term query ->
    int option * theorem list
  val filter_theorems_cmd: Proof.context -> theorem list -> string query ->
    int option * theorem list

  val pretty_theorem: Proof.context -> theorem -> Pretty.T
  val pretty_thm: Proof.context -> Facts.ref * thm -> Pretty.T

end;

structure Find_Theorems: FIND_THEOREMS =
struct

(** search criteria **)

datatype 'term criterion =
  Name of string | Intro | Elim | Dest | Solves | Simp of 'term | Pattern of 'term;

fun apply_dummies tm =
  let
    val (xs, _) = Term.strip_abs tm;
    val tm' = Term.betapplys (tm, map (Term.dummy_pattern o #2) xs);
  in #1 (Term.replace_dummy_patterns tm' 1) end;

fun parse_pattern ctxt nm =
  let
    val consts = Proof_Context.consts_of ctxt;
    val nm' =
      (case Syntax.parse_term ctxt nm of
        Const (c, _) => c
      | _ => Consts.intern consts nm);
  in
    (case try (Consts.the_abbreviation consts) nm' of
      SOME (_, rhs) => apply_dummies (Proof_Context.expand_abbrevs ctxt rhs)
    | NONE => Proof_Context.read_term_pattern ctxt nm)
  end;

fun read_criterion _ (Name name) = Name name
  | read_criterion _ Intro = Intro
  | read_criterion _ Elim = Elim
  | read_criterion _ Dest = Dest
  | read_criterion _ Solves = Solves
  | read_criterion ctxt (Simp str) = Simp (Proof_Context.read_term_pattern ctxt str)
  | read_criterion ctxt (Pattern str) = Pattern (parse_pattern ctxt str);

fun pretty_criterion ctxt (b, c) =
  let
    fun prfx s = if b then s else "-" ^ s;
  in
    (case c of
      Name name => Pretty.str (prfx "name: " ^ quote name)
    | Intro => Pretty.str (prfx "intro")
    | Elim => Pretty.str (prfx "elim")
    | Dest => Pretty.str (prfx "dest")
    | Solves => Pretty.str (prfx "solves")
    | Simp pat => Pretty.block [Pretty.str (prfx "simp:"), Pretty.brk 1,
        Pretty.quote (Syntax.pretty_term ctxt (Term.show_dummy_patterns pat))]
    | Pattern pat => Pretty.enclose (prfx " \"") "\""
        [Syntax.pretty_term ctxt (Term.show_dummy_patterns pat)])
  end;



(** queries **)

type 'term query = {
  goal: thm option,
  limit: int option,
  rem_dups: bool,
  criteria: (bool * 'term criterion) list
};

fun map_criteria f {goal, limit, rem_dups, criteria} =
  {goal = goal, limit = limit, rem_dups = rem_dups, criteria = f criteria};

fun xml_of_criterion (Name name) = XML.Elem (("Name", [("val", name)]), [])
  | xml_of_criterion Intro = XML.Elem (("Intro", []) , [])
  | xml_of_criterion Elim = XML.Elem (("Elim", []) , [])
  | xml_of_criterion Dest = XML.Elem (("Dest", []) , [])
  | xml_of_criterion Solves = XML.Elem (("Solves", []) , [])
  | xml_of_criterion (Simp pat) = XML.Elem (("Simp", []) , [XML_Syntax.xml_of_term pat])
  | xml_of_criterion (Pattern pat) = XML.Elem (("Pattern", []) , [XML_Syntax.xml_of_term pat]);

fun criterion_of_xml (XML.Elem (("Name", [("val", name)]), [])) = Name name
  | criterion_of_xml (XML.Elem (("Intro", []) , [])) = Intro
  | criterion_of_xml (XML.Elem (("Elim", []) , [])) = Elim
  | criterion_of_xml (XML.Elem (("Dest", []) , [])) = Dest
  | criterion_of_xml (XML.Elem (("Solves", []) , [])) = Solves
  | criterion_of_xml (XML.Elem (("Simp", []) , [tree])) = Simp (XML_Syntax.term_of_xml tree)
  | criterion_of_xml (XML.Elem (("Pattern", []) , [tree])) = Pattern (XML_Syntax.term_of_xml tree)
  | criterion_of_xml tree = raise XML_Syntax.XML ("criterion_of_xml: bad tree", tree);

fun xml_of_query {goal = NONE, limit, rem_dups, criteria} =
      let
        val properties = []
          |> (if rem_dups then cons ("rem_dups", "") else I)
          |> (if is_some limit then cons ("limit", Markup.print_int (the limit)) else I);
      in
        XML.Elem (("Query", properties), XML.Encode.list
          (XML.Encode.pair XML.Encode.bool (single o xml_of_criterion)) criteria)
      end
  | xml_of_query _ = raise Fail "cannot serialize goal";

fun query_of_xml (XML.Elem (("Query", properties), body)) =
      let
        val rem_dups = Properties.defined properties "rem_dups";
        val limit = Properties.get properties "limit" |> Option.map Markup.parse_int;
        val criteria =
          XML.Decode.list (XML.Decode.pair XML.Decode.bool
            (criterion_of_xml o the_single)) body;
      in
        {goal = NONE, limit = limit, rem_dups = rem_dups, criteria = criteria}
      end
  | query_of_xml tree = raise XML_Syntax.XML ("query_of_xml: bad tree", tree);



(** theorems, either internal or external (without proof) **)

datatype theorem =
  Internal of Facts.ref * thm |
  External of Facts.ref * term; (* FIXME: Facts.ref not appropriate *)

fun fact_ref_markup (Facts.Named ((name, pos), SOME [Facts.Single i])) =
      Position.markup pos o Markup.properties [("name", name), ("index", Markup.print_int i)]
  | fact_ref_markup (Facts.Named ((name, pos), NONE)) =
      Position.markup pos o Markup.properties [("name", name)]
  | fact_ref_markup fact_ref = raise Fail "bad fact ref";

fun xml_of_theorem (Internal _) = raise Fail "xml_of_theorem: Internal"
  | xml_of_theorem (External (fact_ref, prop)) =
      XML.Elem (fact_ref_markup fact_ref ("External", []), [XML_Syntax.xml_of_term prop]);

fun theorem_of_xml (XML.Elem (("External", properties), [tree])) =
      let
        val name = the (Properties.get properties "name");
        val pos = Position.of_properties properties;
        val intvs_opt =
          Option.map (single o Facts.Single o Markup.parse_int)
            (Properties.get properties "index");
      in
        External (Facts.Named ((name, pos), intvs_opt), XML_Syntax.term_of_xml tree)
      end
  | theorem_of_xml tree = raise XML_Syntax.XML ("theorem_of_xml: bad tree", tree);

fun xml_of_result (opt_found, theorems) =
  let
    val properties =
      if is_some opt_found then [("found", Markup.print_int (the opt_found))] else [];
  in
    XML.Elem (("Result", properties), XML.Encode.list (single o xml_of_theorem) theorems)
  end;

fun result_of_xml (XML.Elem (("Result", properties), body)) =
      (Properties.get properties "found" |> Option.map Markup.parse_int,
       XML.Decode.list (theorem_of_xml o the_single) body)
  | result_of_xml tree = raise XML_Syntax.XML ("result_of_xml: bad tree", tree);

fun prop_of (Internal (_, thm)) = Thm.full_prop_of thm
  | prop_of (External (_, prop)) = prop;

fun nprems_of (Internal (_, thm)) = Thm.nprems_of thm
  | nprems_of (External (_, prop)) = Logic.count_prems prop;

fun major_prem_of (Internal (_, thm)) = Thm.major_prem_of thm
  | major_prem_of (External (_, prop)) =
      Logic.strip_assums_concl (hd (Logic.strip_imp_prems prop));

fun fact_ref_of (Internal (fact_ref, _)) = fact_ref
  | fact_ref_of (External (fact_ref, _)) = fact_ref;



(** search criterion filters **)

(*generated filters are to be of the form
  input: theorem
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

fun is_nontrivial thy = Term.is_Const o Term.head_of o Object_Logic.drop_judgment thy;

(*extract terms from term_src, refine them to the parts that concern us,
  if po try match them against obj else vice versa.
  trivial matches are ignored.
  returns: smallest substitution size*)
fun is_matching_thm (extract_terms, refine_term) ctxt po obj term_src =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun matches pat =
      is_nontrivial thy pat andalso
      Pattern.matches thy (if po then (pat, obj) else (obj, pat));

    fun substsize pat =
      let val (_, subst) =
        Pattern.match thy (if po then (pat, obj) else (obj, pat)) (Vartab.empty, Vartab.empty)
      in Vartab.fold (fn (_, (_, t)) => fn n => size_of_term t + n) subst 0 end;

    fun bestmatch [] = NONE
      | bestmatch xs = SOME (foldl1 Int.min xs);

    val match_thm = matches o refine_term;
  in
    map (substsize o refine_term) (filter match_thm (extract_terms term_src))
    |> bestmatch
  end;


(* filter_name *)

fun filter_name str_pat theorem =
  if match_string str_pat (Facts.name_of_ref (fact_ref_of theorem))
  then SOME (0, 0) else NONE;


(* filter intro/elim/dest/solves rules *)

fun filter_dest ctxt goal theorem =
  let
    val extract_dest =
     (fn theorem => if nprems_of theorem = 0 then [] else [prop_of theorem],
      hd o Logic.strip_imp_prems);
    val prems = Logic.prems_of_goal goal 1;

    fun try_subst prem = is_matching_thm extract_dest ctxt true prem theorem;
    val successful = prems |> map_filter try_subst;
  in
    (*if possible, keep best substitution (one with smallest size)*)
    (*dest rules always have assumptions, so a dest with one
      assumption is as good as an intro rule with none*)
    if not (null successful)
    then SOME (nprems_of theorem - 1, foldl1 Int.min successful) else NONE
  end;

fun filter_intro ctxt goal theorem =
  let
    val extract_intro = (single o prop_of, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
    val ss = is_matching_thm extract_intro ctxt true concl theorem;
  in
    if is_some ss then SOME (nprems_of theorem, the ss) else NONE
  end;

fun filter_elim ctxt goal theorem =
  if nprems_of theorem > 0 then
    let
      val rule = prop_of theorem;
      val prems = Logic.prems_of_goal goal 1;
      val goal_concl = Logic.concl_of_goal goal 1;
      val rule_mp = hd (Logic.strip_imp_prems rule);
      val rule_concl = Logic.strip_imp_concl rule;
      fun combine t1 t2 = Const ("*combine*", dummyT --> dummyT) $ (t1 $ t2);
      val rule_tree = combine rule_mp rule_concl;
      fun goal_tree prem = combine prem goal_concl;
      fun try_subst prem = is_matching_thm (single, I) ctxt true (goal_tree prem) rule_tree;
      val successful = prems |> map_filter try_subst;
    in
      (*elim rules always have assumptions, so an elim with one
        assumption is as good as an intro rule with none*)
      if is_nontrivial (Proof_Context.theory_of ctxt) (major_prem_of theorem)
        andalso not (null successful)
      then SOME (nprems_of theorem - 1, foldl1 Int.min successful) else NONE
    end
  else NONE;

val tac_limit = Unsynchronized.ref 5;

fun filter_solves ctxt goal =
  let
    fun etacn thm i = Seq.take (! tac_limit) o etac thm i;
    fun try_thm thm =
      if Thm.no_prems thm then rtac thm 1 goal
      else (etacn thm THEN_ALL_NEW (Goal.norm_hhf_tac THEN' Method.assm_tac ctxt)) 1 goal;
  in
    fn Internal (_, thm) =>
        if is_some (Seq.pull (try_thm thm))
        then SOME (Thm.nprems_of thm, 0) else NONE
     | External _ => NONE
  end;


(* filter_simp *)

fun filter_simp ctxt t (Internal (_, thm)) =
      let
        val mksimps = Simplifier.mksimps (simpset_of ctxt);
        val extract_simp =
          (map Thm.full_prop_of o mksimps, #1 o Logic.dest_equals o Logic.strip_imp_concl);
        val ss = is_matching_thm extract_simp ctxt false t thm;
      in
        if is_some ss then SOME (Thm.nprems_of thm, the ss) else NONE
      end
  | filter_simp _ _ (External _) = NONE;


(* filter_pattern *)

fun get_names t = Term.add_const_names t (Term.add_free_names t []);

(*Including all constants and frees is only sound because
  matching uses higher-order patterns. If full matching
  were used, then constants that may be subject to
  beta-reduction after substitution of frees should
  not be included for LHS set because they could be
  thrown away by the substituted function.
  e.g. for (?F 1 2) do not include 1 or 2, if it were
       possible for ?F to be (% x y. 3)
  The largest possible set should always be included on
  the RHS.*)

fun filter_pattern ctxt pat =
  let
    val pat_consts = get_names pat;

    fun check (theorem, NONE) = check (theorem, SOME (get_names (prop_of theorem)))
      | check (theorem, c as SOME thm_consts) =
         (if subset (op =) (pat_consts, thm_consts) andalso
            Pattern.matches_subterm (Proof_Context.theory_of ctxt) (pat, prop_of theorem)
          then SOME (0, 0) else NONE, c);
  in check end;


(* interpret criteria as filters *)

local

fun err_no_goal c =
  error ("Current goal required for " ^ c ^ " search criterion");

val fix_goal = Thm.prop_of;

fun filter_crit _ _ (Name name) = apfst (filter_name name)
  | filter_crit _ NONE Intro = err_no_goal "intro"
  | filter_crit _ NONE Elim = err_no_goal "elim"
  | filter_crit _ NONE Dest = err_no_goal "dest"
  | filter_crit _ NONE Solves = err_no_goal "solves"
  | filter_crit ctxt (SOME goal) Intro = apfst (filter_intro ctxt (fix_goal goal))
  | filter_crit ctxt (SOME goal) Elim = apfst (filter_elim ctxt (fix_goal goal))
  | filter_crit ctxt (SOME goal) Dest = apfst (filter_dest ctxt (fix_goal goal))
  | filter_crit ctxt (SOME goal) Solves = apfst (filter_solves ctxt goal)
  | filter_crit ctxt _ (Simp pat) = apfst (filter_simp ctxt pat)
  | filter_crit ctxt _ (Pattern pat) = filter_pattern ctxt pat;

fun opt_not x = if is_some x then NONE else SOME (0, 0);

fun opt_add (SOME (a, x)) (SOME (b, y)) = SOME (Int.max (a, b), x + y : int)
  | opt_add _ _ = NONE;

fun app_filters thm =
  let
    fun app (NONE, _, _) = NONE
      | app (SOME v, _, []) = SOME (v, thm)
      | app (r, consts, f :: fs) =
          let val (r', consts') = f (thm, consts)
          in app (opt_add r r', consts', fs) end;
  in app end;

in

fun filter_criterion ctxt opt_goal (b, c) =
  (if b then I else (apfst opt_not)) o filter_crit ctxt opt_goal c;

fun sorted_filter filters theorems =
  let
    fun eval_filters theorem = app_filters theorem (SOME (0, 0), NONE, filters);

    (*filters return: (number of assumptions, substitution size) option, so
      sort (desc. in both cases) according to number of assumptions first,
      then by the substitution size*)
    fun result_ord (((p0, s0), _), ((p1, s1), _)) =
      prod_ord int_ord int_ord ((p1, s1), (p0, s0));
  in
    grouped 100 Par_List.map eval_filters theorems
    |> map_filter I |> sort result_ord |> map #2
  end;

fun lazy_filter filters =
  let
    fun lazy_match thms = Seq.make (fn () => first_match thms)
    and first_match [] = NONE
      | first_match (thm :: thms) =
          (case app_filters thm (SOME (0, 0), NONE, filters) of
            NONE => first_match thms
          | SOME (_, t) => SOME (t, lazy_match thms));
  in lazy_match end;

end;


(* removing duplicates, preferring nicer names, roughly n log n *)

local

val index_ord = option_ord (K EQUAL);
val hidden_ord = bool_ord o pairself Name_Space.is_hidden;
val qual_ord = int_ord o pairself (length o Long_Name.explode);
val txt_ord = int_ord o pairself size;

fun nicer_name (x, i) (y, j) =
  (case hidden_ord (x, y) of EQUAL =>
    (case index_ord (i, j) of EQUAL =>
      (case qual_ord (x, y) of EQUAL => txt_ord (x, y) | ord => ord)
    | ord => ord)
  | ord => ord) <> GREATER;

fun rem_cdups nicer xs =
  let
    fun rem_c rev_seen [] = rev rev_seen
      | rem_c rev_seen [x] = rem_c (x :: rev_seen) []
      | rem_c rev_seen ((x as (t, _)) :: (y as (t', _)) :: xs) =
          if (prop_of t) aconv (prop_of t')
          then rem_c rev_seen ((if nicer (fact_ref_of t) (fact_ref_of t') then x else y) :: xs)
          else rem_c (x :: rev_seen) (y :: xs)
  in rem_c [] xs end;

in

fun nicer_shortest ctxt =
  let
    (* FIXME Why global name space!?? *)
    val space = Facts.space_of (Global_Theory.facts_of (Proof_Context.theory_of ctxt));

    val shorten =
      Name_Space.extern
        (ctxt
          |> Config.put Name_Space.names_long false
          |> Config.put Name_Space.names_short false
          |> Config.put Name_Space.names_unique false) space;

    fun nicer (Facts.Named ((x, _), i)) (Facts.Named ((y, _), j)) =
          nicer_name (shorten x, i) (shorten y, j)
      | nicer (Facts.Fact _) (Facts.Named _) = true
      | nicer (Facts.Named _) (Facts.Fact _) = false;
  in nicer end;

fun rem_thm_dups nicer xs =
  xs ~~ (1 upto length xs)
  |> sort (Term_Ord.fast_term_ord o pairself (prop_of o #1))
  |> rem_cdups nicer
  |> sort (int_ord o pairself #2)
  |> map #1;

end;


(* print_theorems *)

fun all_facts_of ctxt =
  let
    fun visible_facts facts =
      Facts.dest_static [] facts
      |> filter_out (Facts.is_concealed facts o #1);
  in
    maps Facts.selections
     (visible_facts (Global_Theory.facts_of (Proof_Context.theory_of ctxt)) @
      visible_facts (Proof_Context.facts_of ctxt))
  end;

val limit = Unsynchronized.ref 40;

fun filter_theorems ctxt theorems query =
  let
    val {goal = opt_goal, limit = opt_limit, rem_dups, criteria} = query;
    val filters = map (filter_criterion ctxt opt_goal) criteria;

    fun find_all theorems =
      let
        val raw_matches = sorted_filter filters theorems;

        val matches =
          if rem_dups
          then rem_thm_dups (nicer_shortest ctxt) raw_matches
          else raw_matches;

        val len = length matches;
        val lim = the_default (! limit) opt_limit;
      in (SOME len, drop (Int.max (len - lim, 0)) matches) end;

    val find =
      if rem_dups orelse is_none opt_limit
      then find_all
      else pair NONE o Seq.list_of o Seq.take (the opt_limit) o lazy_filter filters;

  in find theorems end;

fun filter_theorems_cmd ctxt theorems raw_query =
  filter_theorems ctxt theorems (map_criteria
    (map (apsnd (read_criterion ctxt))) raw_query);

fun gen_find_theorems filter ctxt opt_goal opt_limit rem_dups raw_criteria =
  let
    val assms =
      Proof_Context.get_fact ctxt (Facts.named "local.assms")
        handle ERROR _ => [];
    val add_prems = Seq.hd o TRY (Method.insert_tac assms 1);
    val opt_goal' = Option.map add_prems opt_goal;
  in
    filter ctxt (map Internal (all_facts_of ctxt))
      {goal = opt_goal', limit = opt_limit, rem_dups = rem_dups, criteria = raw_criteria}
    |> apsnd (map (fn Internal f => f))
  end;

val find_theorems = gen_find_theorems filter_theorems;
val find_theorems_cmd = gen_find_theorems filter_theorems_cmd;

fun pretty_theorem ctxt (Internal (thmref, thm)) = Pretty.block
      [Pretty.str (Facts.string_of_ref thmref), Pretty.str ":", Pretty.brk 1,
        Display.pretty_thm ctxt thm]
  | pretty_theorem ctxt (External (thmref, prop)) = Pretty.block
      [Pretty.str (Facts.string_of_ref thmref), Pretty.str ":", Pretty.brk 1,
        Syntax.unparse_term ctxt prop];

fun pretty_thm ctxt (thmref, thm) = pretty_theorem ctxt (Internal (thmref, thm));

fun gen_print_theorems find ctxt opt_goal opt_limit rem_dups raw_criteria =
  let
    val criteria = map (apsnd (read_criterion ctxt)) raw_criteria;
    val (foundo, theorems) = find
      {goal = opt_goal, limit = opt_limit, rem_dups = rem_dups, criteria = criteria};
    val returned = length theorems;

    val tally_msg =
      (case foundo of
        NONE => "displaying " ^ string_of_int returned ^ " theorem(s)"
      | SOME found =>
          "found " ^ string_of_int found ^ " theorem(s)" ^
            (if returned < found
             then " (" ^ string_of_int returned ^ " displayed)"
             else ""));
  in
    Pretty.big_list "searched for:" (map (pretty_criterion ctxt) criteria) ::
    Pretty.str "" ::
    (if null theorems then [Pretty.str "nothing found"]
     else
      [Pretty.str (tally_msg ^ ":"), Pretty.str ""] @
        grouped 10 Par_List.map (pretty_theorem ctxt) theorems)
  end |> Pretty.chunks |> Pretty.writeln;

fun print_theorems ctxt =
  gen_print_theorems (filter_theorems ctxt (map Internal (all_facts_of ctxt))) ctxt;



(** command syntax **)

local

val criterion =
  Parse.reserved "name" |-- Parse.!!! (Parse.$$$ ":" |-- Parse.xname) >> Name ||
  Parse.reserved "intro" >> K Intro ||
  Parse.reserved "elim" >> K Elim ||
  Parse.reserved "dest" >> K Dest ||
  Parse.reserved "solves" >> K Solves ||
  Parse.reserved "simp" |-- Parse.!!! (Parse.$$$ ":" |-- Parse.term) >> Simp ||
  Parse.term >> Pattern;

val options =
  Scan.optional
    (Parse.$$$ "(" |--
      Parse.!!! (Scan.option Parse.nat -- Scan.optional (Parse.reserved "with_dups" >> K false) true
        --| Parse.$$$ ")")) (NONE, true);
in

val query_parser = Scan.repeat (((Scan.option Parse.minus >> is_none) -- criterion));

val _ =
  Outer_Syntax.improper_command @{command_spec "find_theorems"}
    "print theorems meeting specified criteria"
    (options -- query_parser
      >> (fn ((opt_lim, rem_dups), spec) =>
        Toplevel.no_timing o
        Toplevel.keep (fn state =>
          let
            val ctxt = Toplevel.context_of state;
            val opt_goal = try (Proof.simple_goal o Toplevel.proof_of) state |> Option.map #goal;
          in print_theorems ctxt opt_goal opt_lim rem_dups spec end)));

end;

end;
