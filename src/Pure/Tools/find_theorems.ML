(*  Title:      Pure/Tools/find_theorems.ML
    Author:     Rafal Kolanski and Gerwin Klein, NICTA

Retrieve theorems from proof context.
*)

signature FIND_THEOREMS =
sig
  datatype 'term criterion =
    Name of string | Intro | IntroIff | Elim | Dest | Solves | Simp of 'term |
    Pattern of 'term
  val tac_limit: int ref
  val limit: int ref
  val find_theorems: Proof.context -> thm option -> int option -> bool ->
    (bool * string criterion) list -> int option * (Facts.ref * thm) list
  val pretty_thm: Proof.context -> Facts.ref * thm -> Pretty.T
  val print_theorems: Proof.context -> thm option -> int option -> bool ->
    (bool * string criterion) list -> unit
end;

structure FindTheorems: FIND_THEOREMS =
struct

(** search criteria **)

datatype 'term criterion =
  Name of string | Intro | IntroIff | Elim | Dest | Solves | Simp of 'term |
  Pattern of 'term;

fun read_criterion _ (Name name) = Name name
  | read_criterion _ Intro = Intro
  | read_criterion _ IntroIff = IntroIff
  | read_criterion _ Elim = Elim
  | read_criterion _ Dest = Dest
  | read_criterion _ Solves = Solves
  | read_criterion ctxt (Simp str) = Simp (ProofContext.read_term_pattern ctxt str)
  | read_criterion ctxt (Pattern str) = Pattern (ProofContext.read_term_pattern ctxt str);

fun pretty_criterion ctxt (b, c) =
  let
    fun prfx s = if b then s else "-" ^ s;
  in
    (case c of
      Name name => Pretty.str (prfx "name: " ^ quote name)
    | Intro => Pretty.str (prfx "intro")
    | IntroIff => Pretty.str (prfx "introiff")
    | Elim => Pretty.str (prfx "elim")
    | Dest => Pretty.str (prfx "dest")
    | Solves => Pretty.str (prfx "solves")
    | Simp pat => Pretty.block [Pretty.str (prfx "simp:"), Pretty.brk 1,
        Pretty.quote (Syntax.pretty_term ctxt (Term.show_dummy_patterns pat))]
    | Pattern pat => Pretty.enclose (prfx " \"") "\""
        [Syntax.pretty_term ctxt (Term.show_dummy_patterns pat)])
  end;



(** search criterion filters **)

(*generated filters are to be of the form
  input: (Facts.ref * thm)
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

(* Note: ("op =" : "bool --> bool --> bool") does not exist in Pure. *)
fun is_Iff c =
  (case dest_Const c of
     ("op =", ty) =>
       (ty
        |> strip_type
        |> swap
        |> (op ::)
        |> map (fst o dest_Type)
        |> forall (curry (op =) "bool")
        handle TYPE _ => false)
   | _ => false);

(*extract terms from term_src, refine them to the parts that concern us,
  if po try match them against obj else vice versa.
  trivial matches are ignored.
  returns: smallest substitution size*)
fun is_matching_thm doiff (extract_terms, refine_term) ctxt po obj term_src =
  let
    val thy = ProofContext.theory_of ctxt;

    val chkmatch = obj |> (if po then rpair else pair) #> Pattern.matches thy;
    fun matches pat =
      let
        val jpat = ObjectLogic.drop_judgment thy pat;
        val c = Term.head_of jpat;
        val pats =
          if Term.is_Const c
          then if doiff andalso is_Iff c
               then pat :: map (ObjectLogic.ensure_propT thy) ((snd o strip_comb) jpat)
                    |> filter (is_nontrivial thy)
               else [pat]
          else [];
      in filter chkmatch pats end;

    fun substsize pat =
      let val (_, subst) =
        Pattern.match thy (if po then (pat, obj) else (obj, pat)) (Vartab.empty, Vartab.empty)
      in Vartab.fold (fn (_, (_, t)) => fn n => size_of_term t + n) subst 0 end;

    fun bestmatch [] = NONE
     |  bestmatch xs = SOME (foldr1 Int.min xs);

    val match_thm = matches o refine_term;
  in
    map match_thm (extract_terms term_src)
    |> flat
    |> map substsize
    |> bestmatch
  end;


(* filter_name *)

fun filter_name str_pat (thmref, _) =
  if match_string str_pat (Facts.name_of_ref thmref)
  then SOME (0, 0) else NONE;


(* filter intro/elim/dest/solves rules *)

fun filter_dest ctxt goal (_, thm) =
  let
    val extract_dest =
     (fn thm => if Thm.no_prems thm then [] else [Thm.full_prop_of thm],
      hd o Logic.strip_imp_prems);
    val prems = Logic.prems_of_goal goal 1;

    fun try_subst prem = is_matching_thm false extract_dest ctxt true prem thm;
    val successful = prems |> map_filter try_subst;
  in
    (*if possible, keep best substitution (one with smallest size)*)
    (*dest rules always have assumptions, so a dest with one
      assumption is as good as an intro rule with none*)
    if not (null successful)
    then SOME (Thm.nprems_of thm - 1, foldr1 Int.min successful) else NONE
  end;

fun filter_intro doiff ctxt goal (_, thm) =
  let
    val extract_intro = (single o Thm.full_prop_of, Logic.strip_imp_concl);
    val concl = Logic.concl_of_goal goal 1;
    val ss = is_matching_thm doiff extract_intro ctxt true concl thm;
  in
    if is_some ss then SOME (Thm.nprems_of thm, the ss) else NONE
  end;

fun filter_elim ctxt goal (_, thm) =
  if not (Thm.no_prems thm) then
    let
      val rule = Thm.full_prop_of thm;
      val prems = Logic.prems_of_goal goal 1;
      val goal_concl = Logic.concl_of_goal goal 1;
      val rule_mp = hd (Logic.strip_imp_prems rule);
      val rule_concl = Logic.strip_imp_concl rule;
      fun combine t1 t2 = Const ("*combine*", dummyT --> dummyT) $ (t1 $ t2);
      val rule_tree = combine rule_mp rule_concl;
      fun goal_tree prem = combine prem goal_concl;
      fun try_subst prem =
        is_matching_thm false (single, I) ctxt true (goal_tree prem) rule_tree;
      val successful = prems |> map_filter try_subst;
    in
    (*elim rules always have assumptions, so an elim with one
      assumption is as good as an intro rule with none*)
      if is_nontrivial (ProofContext.theory_of ctxt) (Thm.major_prem_of thm)
        andalso not (null successful)
      then SOME (Thm.nprems_of thm - 1, foldr1 Int.min successful) else NONE
    end
  else NONE

val tac_limit = ref 5;

fun filter_solves ctxt goal =
  let
    val baregoal = Logic.get_goal (Thm.prop_of goal) 1;

    fun etacn thm i = Seq.take (! tac_limit) o etac thm i;
    fun try_thm thm =
      if Thm.no_prems thm then rtac thm 1 goal
      else (etacn thm THEN_ALL_NEW (Goal.norm_hhf_tac THEN' Method.assm_tac ctxt)) 1 goal;
  in
    fn (_, thm) =>
      if (is_some o Seq.pull o try_thm) thm
      then SOME (Thm.nprems_of thm, 0) else NONE
  end;


(* filter_simp *)

fun filter_simp ctxt t (_, thm) =
  let
    val mksimps = Simplifier.mksimps (Simplifier.local_simpset_of ctxt);
    val extract_simp =
      (map Thm.full_prop_of o mksimps, #1 o Logic.dest_equals o Logic.strip_imp_concl);
    val ss = is_matching_thm false extract_simp ctxt false t thm;
  in
    if is_some ss then SOME (Thm.nprems_of thm, the ss) else NONE
  end;


(* filter_pattern *)

fun get_names t = (Term.add_const_names t []) union (Term.add_free_names t []);
fun get_thm_names (_, thm) = get_names (Thm.full_prop_of thm);

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

    fun check (t, NONE) = check (t, SOME (get_thm_names t))
      | check ((_, thm), c as SOME thm_consts) =
          (if pat_consts subset_string thm_consts
              andalso (Pattern.matches_subterm (ProofContext.theory_of ctxt)
                                               (pat, Thm.full_prop_of thm))
           then SOME (0, 0) else NONE, c);
  in check end;


(* interpret criteria as filters *)

local

fun err_no_goal c =
  error ("Current goal required for " ^ c ^ " search criterion");

val fix_goal = Thm.prop_of;
val fix_goalo = Option.map fix_goal;

fun filter_crit _ _ (Name name) = apfst (filter_name name)
  | filter_crit _ NONE Intro = err_no_goal "intro"
  | filter_crit _ NONE Elim = err_no_goal "elim"
  | filter_crit _ NONE Dest = err_no_goal "dest"
  | filter_crit _ NONE Solves = err_no_goal "solves"
  | filter_crit ctxt (SOME goal) Intro = apfst (filter_intro false ctxt (fix_goal goal))
  | filter_crit ctxt (SOME goal) IntroIff = apfst (filter_intro true ctxt (fix_goal goal))
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
      | app (SOME v, consts, []) = SOME (v, thm)
      | app (r, consts, f :: fs) =
          let val (r', consts') = f (thm, consts)
          in app (opt_add r r', consts', fs) end;
  in app end;


in

fun filter_criterion ctxt opt_goal (b, c) =
  (if b then I else (apfst opt_not)) o filter_crit ctxt opt_goal c;

fun sorted_filter filters thms =
  let
    fun eval_filters thm = app_filters thm (SOME (0, 0), NONE, filters);

    (*filters return: (number of assumptions, substitution size) option, so
      sort (desc. in both cases) according to number of assumptions first,
      then by the substitution size*)
    fun thm_ord (((p0, s0), _), ((p1, s1), _)) =
      prod_ord int_ord int_ord ((p1, s1), (p0, s0));
  in map_filter eval_filters thms |> sort thm_ord |> map #2 end;

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
val hidden_ord = bool_ord o pairself NameSpace.is_hidden;
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
      | rem_c rev_seen ((x as ((n, t), _)) :: (y as ((n', t'), _)) :: xs) =
          if Thm.eq_thm_prop (t, t')
          then rem_c rev_seen ((if nicer n n' then x else y) :: xs)
          else rem_c (x :: rev_seen) (y :: xs)
  in rem_c [] xs end;

in

fun nicer_shortest ctxt =
  let
    (* FIXME global name space!? *)
    val space = Facts.space_of (PureThy.facts_of (ProofContext.theory_of ctxt));

    val shorten =
      NameSpace.extern_flags {long_names = false, short_names = false, unique_names = false} space;

    fun nicer (Facts.Named ((x, _), i)) (Facts.Named ((y, _), j)) =
          nicer_name (shorten x, i) (shorten y, j)
      | nicer (Facts.Fact _) (Facts.Named _) = true
      | nicer (Facts.Named _) (Facts.Fact _) = false;
  in nicer end;

fun rem_thm_dups nicer xs =
  xs ~~ (1 upto length xs)
  |> sort (TermOrd.fast_term_ord o pairself (Thm.prop_of o #2 o #1))
  |> rem_cdups nicer
  |> sort (int_ord o pairself #2)
  |> map #1;

end;


(* print_theorems *)

fun all_facts_of ctxt =
  maps Facts.selections
   (Facts.dest_static [] (PureThy.facts_of (ProofContext.theory_of ctxt)) @
    Facts.dest_static [] (ProofContext.facts_of ctxt));

val limit = ref 40;

fun find_theorems ctxt opt_goal opt_limit rem_dups raw_criteria =
  let
    val assms =
      ProofContext.get_fact ctxt (Facts.named "local.assms")
        handle ERROR _ => [];
    val add_prems = Seq.hd o TRY (Method.insert_tac assms 1);
    val opt_goal' = Option.map add_prems opt_goal;

    val criteria = map (apsnd (read_criterion ctxt)) raw_criteria;
    val filters = map (filter_criterion ctxt opt_goal') criteria;

    fun find_all facts =
      let
        val raw_matches = sorted_filter filters facts;

        val matches =
          if rem_dups
          then rem_thm_dups (nicer_shortest ctxt) raw_matches
          else raw_matches;

        val len = length matches;
        val lim = the_default (! limit) opt_limit;
      in (SOME len, Library.drop (len - lim, matches)) end;

    val find =
      if rem_dups orelse is_none opt_limit
      then find_all
      else pair NONE o Seq.list_of o Seq.take (the opt_limit) o lazy_filter filters;

  in find (all_facts_of ctxt) end;


fun pretty_thm ctxt (thmref, thm) = Pretty.block
  [Pretty.str (Facts.string_of_ref thmref), Pretty.str ":", Pretty.brk 1,
    ProofContext.pretty_thm ctxt thm];

fun print_theorems ctxt opt_goal opt_limit rem_dups raw_criteria =
  let
    val start = start_timing ();

    val criteria = map (apsnd (read_criterion ctxt)) raw_criteria;
    val (foundo, thms) = find_theorems ctxt opt_goal opt_limit rem_dups raw_criteria;
    val returned = length thms;

    val tally_msg =
      (case foundo of
        NONE => "displaying " ^ string_of_int returned ^ " theorems"
      | SOME found =>
          "found " ^ string_of_int found ^ " theorems" ^
            (if returned < found
             then " (" ^ string_of_int returned ^ " displayed)"
             else ""));

    val end_msg = " in " ^ Time.toString (#cpu (end_timing start)) ^ " secs";
  in
    Pretty.big_list "searched for:" (map (pretty_criterion ctxt) criteria)
        :: Pretty.str "" ::
     (if null thms then [Pretty.str ("nothing found" ^ end_msg)]
      else
        [Pretty.str (tally_msg ^ end_msg ^ ":"), Pretty.str ""] @
        map (pretty_thm ctxt) thms)
    |> Pretty.chunks |> Pretty.writeln
  end;


(** command syntax **)

fun find_theorems_cmd ((opt_lim, rem_dups), spec) =
  Toplevel.unknown_theory o Toplevel.keep (fn state =>
    let
      val proof_state = Toplevel.enter_proof_body state;
      val ctxt = Proof.context_of proof_state;
      val opt_goal = try Proof.get_goal proof_state |> Option.map (#2 o #2);
    in print_theorems ctxt opt_goal opt_lim rem_dups spec end);

local

structure P = OuterParse and K = OuterKeyword;

val criterion =
  P.reserved "name" |-- P.!!! (P.$$$ ":" |-- P.xname) >> Name ||
  P.reserved "intro" >> K Intro ||
  P.reserved "introiff" >> K IntroIff ||
  P.reserved "elim" >> K Elim ||
  P.reserved "dest" >> K Dest ||
  P.reserved "solves" >> K Solves ||
  P.reserved "simp" |-- P.!!! (P.$$$ ":" |-- P.term) >> Simp ||
  P.term >> Pattern;

val options =
  Scan.optional
    (P.$$$ "(" |--
      P.!!! (Scan.option P.nat -- Scan.optional (P.reserved "with_dups" >> K false) true
        --| P.$$$ ")")) (NONE, true);
in

val _ =
  OuterSyntax.improper_command "find_theorems" "print theorems meeting specified criteria" K.diag
    (options -- Scan.repeat (((Scan.option P.minus >> is_none) -- criterion))
      >> (Toplevel.no_timing oo find_theorems_cmd));

end;

end;
