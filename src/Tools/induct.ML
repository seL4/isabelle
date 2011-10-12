(*  Title:      Tools/induct.ML
    Author:     Markus Wenzel, TU Muenchen

Proof by cases, induction, and coinduction.
*)

signature INDUCT_ARGS =
sig
  val cases_default: thm
  val atomize: thm list
  val rulify: thm list
  val rulify_fallback: thm list
  val equal_def: thm
  val dest_def: term -> (term * term) option
  val trivial_tac: int -> tactic
end;

signature INDUCT =
sig
  (*rule declarations*)
  val vars_of: term -> term list
  val dest_rules: Proof.context ->
    {type_cases: (string * thm) list, pred_cases: (string * thm) list,
      type_induct: (string * thm) list, pred_induct: (string * thm) list,
      type_coinduct: (string * thm) list, pred_coinduct: (string * thm) list}
  val print_rules: Proof.context -> unit
  val lookup_casesT: Proof.context -> string -> thm option
  val lookup_casesP: Proof.context -> string -> thm option
  val lookup_inductT: Proof.context -> string -> thm option
  val lookup_inductP: Proof.context -> string -> thm option
  val lookup_coinductT: Proof.context -> string -> thm option
  val lookup_coinductP: Proof.context -> string -> thm option
  val find_casesT: Proof.context -> typ -> thm list
  val find_casesP: Proof.context -> term -> thm list
  val find_inductT: Proof.context -> typ -> thm list
  val find_inductP: Proof.context -> term -> thm list
  val find_coinductT: Proof.context -> typ -> thm list
  val find_coinductP: Proof.context -> term -> thm list
  val cases_type: string -> attribute
  val cases_pred: string -> attribute
  val cases_del: attribute
  val induct_type: string -> attribute
  val induct_pred: string -> attribute
  val induct_del: attribute
  val coinduct_type: string -> attribute
  val coinduct_pred: string -> attribute
  val coinduct_del: attribute
  val map_simpset: (simpset -> simpset) -> Context.generic -> Context.generic
  val induct_simp_add: attribute
  val induct_simp_del: attribute
  val no_simpN: string
  val casesN: string
  val inductN: string
  val coinductN: string
  val typeN: string
  val predN: string
  val setN: string
  (*proof methods*)
  val fix_tac: Proof.context -> int -> (string * typ) list -> int -> tactic
  val add_defs: (binding option * (term * bool)) option list -> Proof.context ->
    (term option list * thm list) * Proof.context
  val atomize_term: theory -> term -> term
  val atomize_cterm: conv
  val atomize_tac: int -> tactic
  val inner_atomize_tac: int -> tactic
  val rulified_term: thm -> theory * term
  val rulify_tac: int -> tactic
  val simplified_rule: Proof.context -> thm -> thm
  val simplify_tac: Proof.context -> int -> tactic
  val trivial_tac: int -> tactic
  val rotate_tac: int -> int -> int -> tactic
  val internalize: int -> thm -> thm
  val guess_instance: Proof.context -> thm -> int -> thm -> thm Seq.seq
  val cases_tac: Proof.context -> bool -> term option list list -> thm option ->
    thm list -> int -> cases_tactic
  val get_inductT: Proof.context -> term option list list -> thm list list
  type case_data = (((string * string list) * string list) list * int) (* FIXME -> rule_cases.ML *)
  val gen_induct_tac: (theory -> case_data * thm -> case_data * thm) ->
    Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> cases_tactic
  val induct_tac: Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> cases_tactic
  val coinduct_tac: Proof.context -> term option list -> term option list -> thm option ->
    thm list -> int -> cases_tactic
  val gen_induct_setup: binding ->
   (Proof.context -> bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> cases_tactic) ->
   theory -> theory
  val setup: theory -> theory
end;

functor Induct(Induct_Args: INDUCT_ARGS): INDUCT =
struct

(** variables -- ordered left-to-right, preferring right **)

fun vars_of tm =
  rev (distinct (op =) (Term.fold_aterms (fn (t as Var _) => cons t | _ => I) tm []));

local

val mk_var = Net.encode_type o #2 o Term.dest_Var;

fun concl_var which thm = mk_var (which (vars_of (Thm.concl_of thm))) handle Empty =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

in

fun left_var_prem thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle Empty =>
  raise THM ("No variables in major premise of rule", 0, [thm]);

val left_var_concl = concl_var hd;
val right_var_concl = concl_var List.last;

end;



(** constraint simplification **)

(* rearrange parameters and premises to allow application of one-point-rules *)

fun swap_params_conv ctxt i j cv =
  let
    fun conv1 0 ctxt = Conv.forall_conv (cv o snd) ctxt
      | conv1 k ctxt =
          Conv.rewr_conv @{thm swap_params} then_conv
          Conv.forall_conv (conv1 (k - 1) o snd) ctxt
    fun conv2 0 ctxt = conv1 j ctxt
      | conv2 k ctxt = Conv.forall_conv (conv2 (k - 1) o snd) ctxt
  in conv2 i ctxt end;

fun swap_prems_conv 0 = Conv.all_conv
  | swap_prems_conv i =
      Conv.implies_concl_conv (swap_prems_conv (i - 1)) then_conv
      Conv.rewr_conv Drule.swap_prems_eq

fun drop_judgment ctxt = Object_Logic.drop_judgment (Proof_Context.theory_of ctxt);

fun find_eq ctxt t =
  let
    val l = length (Logic.strip_params t);
    val Hs = Logic.strip_assums_hyp t;
    fun find (i, t) =
      (case Induct_Args.dest_def (drop_judgment ctxt t) of
        SOME (Bound j, _) => SOME (i, j)
      | SOME (_, Bound j) => SOME (i, j)
      | _ => NONE);
  in
    (case get_first find (map_index I Hs) of
      NONE => NONE
    | SOME (0, 0) => NONE
    | SOME (i, j) => SOME (i, l - j - 1, j))
  end;

fun mk_swap_rrule ctxt ct =
  (case find_eq ctxt (term_of ct) of
    NONE => NONE
  | SOME (i, k, j) => SOME (swap_params_conv ctxt k j (K (swap_prems_conv i)) ct));

val rearrange_eqs_simproc =
  Simplifier.simproc_global
    (Thm.theory_of_thm Drule.swap_prems_eq) "rearrange_eqs" ["all t"]
    (fn thy => fn ss => fn t =>
      mk_swap_rrule (Simplifier.the_context ss) (cterm_of thy t));


(* rotate k premises to the left by j, skipping over first j premises *)

fun rotate_conv 0 j 0 = Conv.all_conv
  | rotate_conv 0 j k = swap_prems_conv j then_conv rotate_conv 1 j (k - 1)
  | rotate_conv i j k = Conv.implies_concl_conv (rotate_conv (i - 1) j k);

fun rotate_tac j 0 = K all_tac
  | rotate_tac j k = SUBGOAL (fn (goal, i) =>
      CONVERSION (rotate_conv
        j (length (Logic.strip_assums_hyp goal) - j - k) k) i);


(* rulify operators around definition *)

fun rulify_defs_conv ctxt ct =
  if exists_subterm (is_some o Induct_Args.dest_def) (term_of ct) andalso
    not (is_some (Induct_Args.dest_def (drop_judgment ctxt (term_of ct))))
  then
    (Conv.forall_conv (rulify_defs_conv o snd) ctxt else_conv
     Conv.implies_conv (Conv.try_conv (rulify_defs_conv ctxt))
       (Conv.try_conv (rulify_defs_conv ctxt)) else_conv
     Conv.first_conv (map Conv.rewr_conv Induct_Args.rulify) then_conv
       Conv.try_conv (rulify_defs_conv ctxt)) ct
  else Conv.no_conv ct;



(** induct data **)

(* rules *)

type rules = (string * thm) Item_Net.T;

fun init_rules index : rules =
  Item_Net.init
    (fn ((s1, th1), (s2, th2)) => s1 = s2 andalso Thm.eq_thm_prop (th1, th2))
    (single o index);

fun filter_rules (rs: rules) th =
  filter (fn (_, th') => Thm.eq_thm_prop (th, th')) (Item_Net.content rs);

fun lookup_rule (rs: rules) = AList.lookup (op =) (Item_Net.content rs);

fun pretty_rules ctxt kind rs =
  let val thms = map snd (Item_Net.content rs)
  in Pretty.big_list kind (map (Display.pretty_thm ctxt) thms) end;


(* context data *)

structure Data = Generic_Data
(
  type T = (rules * rules) * (rules * rules) * (rules * rules) * simpset;
  val empty =
    ((init_rules (left_var_prem o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (right_var_concl o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (left_var_concl o #2), init_rules (Thm.concl_of o #2)),
     empty_ss addsimprocs [rearrange_eqs_simproc] addsimps [Drule.norm_hhf_eq]);
  val extend = I;
  fun merge (((casesT1, casesP1), (inductT1, inductP1), (coinductT1, coinductP1), simpset1),
      ((casesT2, casesP2), (inductT2, inductP2), (coinductT2, coinductP2), simpset2)) =
    ((Item_Net.merge (casesT1, casesT2), Item_Net.merge (casesP1, casesP2)),
     (Item_Net.merge (inductT1, inductT2), Item_Net.merge (inductP1, inductP2)),
     (Item_Net.merge (coinductT1, coinductT2), Item_Net.merge (coinductP1, coinductP2)),
     merge_ss (simpset1, simpset2));
);

val get_local = Data.get o Context.Proof;

fun dest_rules ctxt =
  let val ((casesT, casesP), (inductT, inductP), (coinductT, coinductP), _) = get_local ctxt in
    {type_cases = Item_Net.content casesT,
     pred_cases = Item_Net.content casesP,
     type_induct = Item_Net.content inductT,
     pred_induct = Item_Net.content inductP,
     type_coinduct = Item_Net.content coinductT,
     pred_coinduct = Item_Net.content coinductP}
  end;

fun print_rules ctxt =
  let val ((casesT, casesP), (inductT, inductP), (coinductT, coinductP), _) = get_local ctxt in
   [pretty_rules ctxt "coinduct type:" coinductT,
    pretty_rules ctxt "coinduct pred:" coinductP,
    pretty_rules ctxt "induct type:" inductT,
    pretty_rules ctxt "induct pred:" inductP,
    pretty_rules ctxt "cases type:" casesT,
    pretty_rules ctxt "cases pred:" casesP]
    |> Pretty.chunks |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.improper_command "print_induct_rules" "print induction and cases rules"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (print_rules o Toplevel.context_of)));


(* access rules *)

val lookup_casesT = lookup_rule o #1 o #1 o get_local;
val lookup_casesP = lookup_rule o #2 o #1 o get_local;
val lookup_inductT = lookup_rule o #1 o #2 o get_local;
val lookup_inductP = lookup_rule o #2 o #2 o get_local;
val lookup_coinductT = lookup_rule o #1 o #3 o get_local;
val lookup_coinductP = lookup_rule o #2 o #3 o get_local;


fun find_rules which how ctxt x =
  map snd (Item_Net.retrieve (which (get_local ctxt)) (how x));

val find_casesT = find_rules (#1 o #1) Net.encode_type;
val find_casesP = find_rules (#2 o #1) I;
val find_inductT = find_rules (#1 o #2) Net.encode_type;
val find_inductP = find_rules (#2 o #2) I;
val find_coinductT = find_rules (#1 o #3) Net.encode_type;
val find_coinductP = find_rules (#2 o #3) I;



(** attributes **)

local

fun mk_att f g name arg =
  let val (x, thm) = g arg in (Data.map (f (name, thm)) x, thm) end;

fun del_att which =
  Thm.declaration_attribute (fn th => Data.map (which (pairself (fn rs =>
    fold Item_Net.remove (filter_rules rs th) rs))));

fun map1 f (x, y, z, s) = (f x, y, z, s);
fun map2 f (x, y, z, s) = (x, f y, z, s);
fun map3 f (x, y, z, s) = (x, y, f z, s);
fun map4 f (x, y, z, s) = (x, y, z, f s);

fun add_casesT rule x = map1 (apfst (Item_Net.update rule)) x;
fun add_casesP rule x = map1 (apsnd (Item_Net.update rule)) x;
fun add_inductT rule x = map2 (apfst (Item_Net.update rule)) x;
fun add_inductP rule x = map2 (apsnd (Item_Net.update rule)) x;
fun add_coinductT rule x = map3 (apfst (Item_Net.update rule)) x;
fun add_coinductP rule x = map3 (apsnd (Item_Net.update rule)) x;

val consumes0 = Rule_Cases.consumes_default 0;
val consumes1 = Rule_Cases.consumes_default 1;

in

val cases_type = mk_att add_casesT consumes0;
val cases_pred = mk_att add_casesP consumes1;
val cases_del = del_att map1;

val induct_type = mk_att add_inductT consumes0;
val induct_pred = mk_att add_inductP consumes1;
val induct_del = del_att map2;

val coinduct_type = mk_att add_coinductT consumes0;
val coinduct_pred = mk_att add_coinductP consumes1;
val coinduct_del = del_att map3;

fun map_simpset f = Data.map (map4 f);

fun induct_simp f =
  Thm.declaration_attribute (fn thm => fn context =>
      map_simpset
        (Simplifier.with_context (Context.proof_of context) (fn ss => f (ss, [thm]))) context);

val induct_simp_add = induct_simp (op addsimps);
val induct_simp_del = induct_simp (op delsimps);

end;



(** attribute syntax **)

val no_simpN = "no_simp";
val casesN = "cases";
val inductN = "induct";
val coinductN = "coinduct";

val typeN = "type";
val predN = "pred";
val setN = "set";

local

fun spec k arg =
  Scan.lift (Args.$$$ k -- Args.colon) |-- arg ||
  Scan.lift (Args.$$$ k) >> K "";

fun attrib add_type add_pred del =
  spec typeN (Args.type_name false) >> add_type ||
  spec predN (Args.const false) >> add_pred ||
  spec setN (Args.const false) >> add_pred ||
  Scan.lift Args.del >> K del;

in

val attrib_setup =
  Attrib.setup @{binding cases} (attrib cases_type cases_pred cases_del)
    "declaration of cases rule" #>
  Attrib.setup @{binding induct} (attrib induct_type induct_pred induct_del)
    "declaration of induction rule" #>
  Attrib.setup @{binding coinduct} (attrib coinduct_type coinduct_pred coinduct_del)
    "declaration of coinduction rule" #>
  Attrib.setup @{binding induct_simp} (Attrib.add_del induct_simp_add induct_simp_del)
    "declaration of rules for simplifying induction or cases rules";

end;



(** method utils **)

(* alignment *)

fun align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (take n xs ~~ ys) end;

fun align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (drop (m - n) xs ~~ ys) end;


(* prep_inst *)

fun prep_inst ctxt align tune (tm, ts) =
  let
    val cert = Thm.cterm_of (Proof_Context.theory_of ctxt);
    fun prep_var (x, SOME t) =
          let
            val cx = cert x;
            val xT = #T (Thm.rep_cterm cx);
            val ct = cert (tune t);
            val tT = #T (Thm.rep_cterm ct);
          in
            if Type.could_unify (tT, xT) then SOME (cx, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Syntax.pretty_term ctxt (Thm.term_of ct), Pretty.str " ::", Pretty.brk 1,
              Syntax.pretty_typ ctxt tT]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end;


(* trace_rules *)

fun trace_rules _ kind [] = error ("Unable to figure out " ^ kind ^ " rule")
  | trace_rules ctxt _ rules = Method.trace ctxt rules;


(* mark equality constraints in cases rule *)

val equal_def' = Thm.symmetric Induct_Args.equal_def;

fun mark_constraints n ctxt = Conv.fconv_rule
  (Conv.prems_conv ~1 (Conv.params_conv ~1 (K (Conv.prems_conv n
     (Raw_Simplifier.rewrite false [equal_def']))) ctxt));

val unmark_constraints = Conv.fconv_rule
  (Raw_Simplifier.rewrite true [Induct_Args.equal_def]);


(* simplify *)

fun simplify_conv' ctxt =
  Simplifier.full_rewrite (Simplifier.context ctxt (#4 (get_local ctxt)));

fun simplify_conv ctxt ct =
  if exists_subterm (is_some o Induct_Args.dest_def) (term_of ct) then
    (Conv.try_conv (rulify_defs_conv ctxt) then_conv simplify_conv' ctxt) ct
  else Conv.all_conv ct;

fun gen_simplified_rule cv ctxt =
  Conv.fconv_rule (Conv.prems_conv ~1 (cv ctxt));

val simplified_rule' = gen_simplified_rule simplify_conv';
val simplified_rule = gen_simplified_rule simplify_conv;

fun simplify_tac ctxt = CONVERSION (simplify_conv ctxt);

val trivial_tac = Induct_Args.trivial_tac;



(** cases method **)

(*
  rule selection scheme:
          cases         - default case split
    `A t` cases ...     - predicate/set cases
          cases t       - type cases
    ...   cases ... r   - explicit rule
*)

local

fun get_casesT ctxt ((SOME t :: _) :: _) = find_casesT ctxt (Term.fastype_of t)
  | get_casesT _ _ = [];

fun get_casesP ctxt (fact :: _) = find_casesP ctxt (Thm.concl_of fact)
  | get_casesP _ _ = [];

in

fun cases_tac ctxt simp insts opt_rule facts =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun inst_rule r =
      (if null insts then r
       else (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
         |> maps (prep_inst ctxt align_left I)
         |> Drule.cterm_instantiate) r) |>
      (if simp then mark_constraints (Rule_Cases.get_constraints r) ctxt else I) |>
      pair (Rule_Cases.get r);

    val ruleq =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_casesP ctxt facts @ get_casesT ctxt insts @ [Induct_Args.cases_default])
          |> tap (trace_rules ctxt casesN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    fn i => fn st =>
      ruleq
      |> Seq.maps (Rule_Cases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        let val rule' =
          (if simp then simplified_rule' ctxt #> unmark_constraints else I) rule
        in
          CASES (Rule_Cases.make_common (thy,
              Thm.prop_of (Rule_Cases.internalize_params rule')) cases)
            ((Method.insert_tac more_facts THEN' rtac rule' THEN_ALL_NEW
                (if simp then TRY o trivial_tac else K all_tac)) i) st
        end)
  end;

end;



(** induct method **)

val conjunction_congs = [@{thm Pure.all_conjunction}, @{thm imp_conjunction}];


(* atomize *)

fun atomize_term thy =
  Raw_Simplifier.rewrite_term thy Induct_Args.atomize []
  #> Object_Logic.drop_judgment thy;

val atomize_cterm = Raw_Simplifier.rewrite true Induct_Args.atomize;

val atomize_tac = Simplifier.rewrite_goal_tac Induct_Args.atomize;

val inner_atomize_tac =
  Simplifier.rewrite_goal_tac (map Thm.symmetric conjunction_congs) THEN' atomize_tac;


(* rulify *)

fun rulify_term thy =
  Raw_Simplifier.rewrite_term thy (Induct_Args.rulify @ conjunction_congs) [] #>
  Raw_Simplifier.rewrite_term thy Induct_Args.rulify_fallback [];

fun rulified_term thm =
  let
    val thy = Thm.theory_of_thm thm;
    val rulify = rulify_term thy;
    val (As, B) = Logic.strip_horn (Thm.prop_of thm);
  in (thy, Logic.list_implies (map rulify As, rulify B)) end;

val rulify_tac =
  Simplifier.rewrite_goal_tac (Induct_Args.rulify @ conjunction_congs) THEN'
  Simplifier.rewrite_goal_tac Induct_Args.rulify_fallback THEN'
  Goal.conjunction_tac THEN_ALL_NEW
  (Simplifier.rewrite_goal_tac [@{thm Pure.conjunction_imp}] THEN' Goal.norm_hhf_tac);


(* prepare rule *)

fun rule_instance ctxt inst rule =
  Drule.cterm_instantiate (prep_inst ctxt align_left I (Thm.prop_of rule, inst)) rule;

fun internalize k th =
  th |> Thm.permute_prems 0 k
  |> Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th - k) atomize_cterm);


(* guess rule instantiation -- cannot handle pending goal parameters *)

local

fun dest_env thy env =
  let
    val cert = Thm.cterm_of thy;
    val certT = Thm.ctyp_of thy;
    val pairs = Vartab.dest (Envir.term_env env);
    val types = Vartab.dest (Envir.type_env env);
    val ts = map (cert o Envir.norm_term env o #2 o #2) pairs;
    val xs = map2 (curry (cert o Var)) (map #1 pairs) (map (#T o Thm.rep_cterm) ts);
  in (map (fn (xi, (S, T)) => (certT (TVar (xi, S)), certT T)) types, xs ~~ ts) end;

in

fun guess_instance ctxt rule i st =
  let
    val thy = Proof_Context.theory_of ctxt;
    val maxidx = Thm.maxidx_of st;
    val goal = Thm.term_of (Thm.cprem_of st i);  (*exception Subscript*)
    val params = rev (Term.rename_wrt_term goal (Logic.strip_params goal));
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas_quote (map (Syntax.string_of_term ctxt o Syntax_Trans.mark_boundT) params));
      Seq.single rule)
    else
      let
        val rule' = Thm.incr_indexes (maxidx + 1) rule;
        val concl = Logic.strip_assums_concl goal;
      in
        Unify.smash_unifiers thy [(Thm.concl_of rule', concl)] (Envir.empty (Thm.maxidx_of rule'))
        |> Seq.map (fn env => Drule.instantiate_normalize (dest_env thy env) rule')
      end
  end
  handle General.Subscript => Seq.empty;

end;


(* special renaming of rule parameters *)

fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (Variable.revert_fixed ctxt z);
        fun index i [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys;
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys;
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A);
            val xs' =
              (case filter (fn x' => x' = x) xs of
                [] => xs | [_] => xs | _ => index 1 xs);
          in Logic.list_rename_params (xs', A) end;
        fun rename_prop p =
          let val (As, C) = Logic.strip_horn p
          in Logic.list_implies (map rename_asm As, C) end;
        val cp' = cterm_fun rename_prop (Thm.cprop_of thm);
        val thm' = Thm.equal_elim (Thm.reflexive cp') thm;
      in [Rule_Cases.save thm thm'] end
  | special_rename_params _ _ ths = ths;


(* fix_tac *)

local

fun goal_prefix k ((c as Const ("all", _)) $ Abs (a, T, B)) = c $ Abs (a, T, goal_prefix k B)
  | goal_prefix 0 _ = Term.dummy_pattern propT
  | goal_prefix k ((c as Const ("==>", _)) $ A $ B) = c $ A $ goal_prefix (k - 1) B
  | goal_prefix _ _ = Term.dummy_pattern propT;

fun goal_params k (Const ("all", _) $ Abs (_, _, B)) = goal_params k B + 1
  | goal_params 0 _ = 0
  | goal_params k (Const ("==>", _) $ _ $ B) = goal_params (k - 1) B
  | goal_params _ _ = 0;

fun meta_spec_tac ctxt n (x, T) = SUBGOAL (fn (goal, i) =>
  let
    val thy = Proof_Context.theory_of ctxt;
    val cert = Thm.cterm_of thy;

    val v = Free (x, T);
    fun spec_rule prfx (xs, body) =
      @{thm Pure.meta_spec}
      |> Thm.rename_params_rule ([Name.clean (Variable.revert_fixed ctxt x)], 1)
      |> Thm.lift_rule (cert prfx)
      |> `(Thm.prop_of #> Logic.strip_assums_concl)
      |-> (fn pred $ arg =>
        Drule.cterm_instantiate
          [(cert (Term.head_of pred), cert (Logic.rlist_abs (xs, body))),
           (cert (Term.head_of arg), cert (Logic.rlist_abs (xs, v)))]);

    fun goal_concl k xs (Const ("all", _) $ Abs (a, T, B)) = goal_concl k ((a, T) :: xs) B
      | goal_concl 0 xs B =
          if not (Term.exists_subterm (fn t => t aconv v) B) then NONE
          else SOME (xs, absfree (x, T) (Term.incr_boundvars 1 B))
      | goal_concl k xs (Const ("==>", _) $ _ $ B) = goal_concl (k - 1) xs B
      | goal_concl _ _ _ = NONE;
  in
    (case goal_concl n [] goal of
      SOME concl =>
        (compose_tac (false, spec_rule (goal_prefix n goal) concl, 1) THEN' rtac asm_rl) i
    | NONE => all_tac)
  end);

fun miniscope_tac p = CONVERSION o
  Conv.params_conv p (K (Raw_Simplifier.rewrite true [Thm.symmetric Drule.norm_hhf_eq]));

in

fun fix_tac _ _ [] = K all_tac
  | fix_tac ctxt n xs = SUBGOAL (fn (goal, i) =>
     (EVERY' (map (meta_spec_tac ctxt n) xs) THEN'
      (miniscope_tac (goal_params n goal) ctxt)) i);

end;


(* add_defs *)

fun add_defs def_insts =
  let
    fun add (SOME (_, (t, true))) ctxt = ((SOME t, []), ctxt)
      | add (SOME (SOME x, (t, _))) ctxt =
          let val ([(lhs, (_, th))], ctxt') =
            Local_Defs.add_defs [((x, NoSyn), (Thm.empty_binding, t))] ctxt
          in ((SOME lhs, [th]), ctxt') end
      | add (SOME (NONE, (t as Free _, _))) ctxt = ((SOME t, []), ctxt)
      | add (SOME (NONE, (t, _))) ctxt =
          let
            val (s, _) = Name.variant "x" (Variable.names_of ctxt);
            val ([(lhs, (_, th))], ctxt') =
              Local_Defs.add_defs [((Binding.name s, NoSyn),
                (Thm.empty_binding, t))] ctxt
          in ((SOME lhs, [th]), ctxt') end
      | add NONE ctxt = ((NONE, []), ctxt);
  in fold_map add def_insts #> apfst (split_list #> apsnd flat) end;


(* induct_tac *)

(*
  rule selection scheme:
    `A x` induct ...     - predicate/set induction
          induct x       - type induction
    ...   induct ... r   - explicit rule
*)

fun get_inductT ctxt insts =
  fold_rev (map_product cons) (insts |> map
      ((fn [] => NONE | ts => List.last ts) #>
        (fn NONE => TVar (("'a", 0), []) | SOME t => Term.fastype_of t) #>
        find_inductT ctxt)) [[]]
  |> filter_out (forall Rule_Cases.is_inner_rule);

fun get_inductP ctxt (fact :: _) = map single (find_inductP ctxt (Thm.concl_of fact))
  | get_inductP _ _ = [];

type case_data = (((string * string list) * string list) list * int);

fun gen_induct_tac mod_cases ctxt simp def_insts arbitrary taking opt_rule facts =
  let
    val thy = Proof_Context.theory_of ctxt;

    val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;
    val atomized_defs = map (map (Conv.fconv_rule atomize_cterm)) defs;

    fun inst_rule (concls, r) =
      (if null insts then `Rule_Cases.get r
       else (align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> maps (prep_inst ctxt align_right (atomize_term thy))
        |> Drule.cterm_instantiate) r |> pair (Rule_Cases.get r))
      |> mod_cases thy
      |> (fn ((cases, consumes), th) => (((cases, concls), consumes), th));

    val ruleq =
      (case opt_rule of
        SOME rs => Seq.single (inst_rule (Rule_Cases.strict_mutual_rule ctxt rs))
      | NONE =>
          (get_inductP ctxt facts @
            map (special_rename_params defs_ctxt insts) (get_inductT ctxt insts))
          |> map_filter (Rule_Cases.mutual_rule ctxt)
          |> tap (trace_rules ctxt inductN o map #2)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));

    fun rule_cases ctxt rule cases =
      let
        val rule' = Rule_Cases.internalize_params rule;
        val rule'' = (if simp then simplified_rule ctxt else I) rule';
        val nonames = map (fn ((cn, _), cls) => ((cn, []), cls));
        val cases' = if Thm.eq_thm_prop (rule', rule'') then cases else nonames cases;
      in Rule_Cases.make_nested (Thm.prop_of rule'') (rulified_term rule'') cases' end;
  in
    (fn i => fn st =>
      ruleq
      |> Seq.maps (Rule_Cases.consume (flat defs) facts)
      |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
        (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
          (CONJUNCTS (ALLGOALS
            let
              val adefs = nth_list atomized_defs (j - 1);
              val frees = fold (Term.add_frees o Thm.prop_of) adefs [];
              val xs = nth_list arbitrary (j - 1);
              val k = nth concls (j - 1) + more_consumes
            in
              Method.insert_tac (more_facts @ adefs) THEN'
                (if simp then
                   rotate_tac k (length adefs) THEN'
                   fix_tac defs_ctxt k (List.partition (member op = frees) xs |> op @)
                 else
                   fix_tac defs_ctxt k xs)
             end)
          THEN' inner_atomize_tac) j))
        THEN' atomize_tac) i st |> Seq.maps (fn st' =>
            guess_instance ctxt (internalize more_consumes rule) i st'
            |> Seq.map (rule_instance ctxt (burrow_options (Variable.polymorphic ctxt) taking))
            |> Seq.maps (fn rule' =>
              CASES (rule_cases ctxt rule' cases)
                (rtac rule' i THEN
                  PRIMITIVE (singleton (Proof_Context.export defs_ctxt ctxt))) st'))))
    THEN_ALL_NEW_CASES
      ((if simp then simplify_tac ctxt THEN' (TRY o trivial_tac)
        else K all_tac)
       THEN_ALL_NEW rulify_tac)
  end;

val induct_tac = gen_induct_tac (K I);



(** coinduct method **)

(*
  rule selection scheme:
    goal "A x" coinduct ...   - predicate/set coinduction
               coinduct x     - type coinduction
               coinduct ... r - explicit rule
*)

local

fun get_coinductT ctxt (SOME t :: _) = find_coinductT ctxt (Term.fastype_of t)
  | get_coinductT _ _ = [];

fun get_coinductP ctxt goal = find_coinductP ctxt (Logic.strip_assums_concl goal);

fun main_prop_of th =
  if Rule_Cases.get_consumes th > 0 then Thm.major_prem_of th else Thm.concl_of th;

in

fun coinduct_tac ctxt inst taking opt_rule facts =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun inst_rule r =
      if null inst then `Rule_Cases.get r
      else Drule.cterm_instantiate (prep_inst ctxt align_right I (main_prop_of r, inst)) r
        |> pair (Rule_Cases.get r);

    fun ruleq goal =
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_coinductP ctxt goal @ get_coinductT ctxt inst)
          |> tap (trace_rules ctxt coinductN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
  in
    SUBGOAL_CASES (fn (goal, i) => fn st =>
      ruleq goal
      |> Seq.maps (Rule_Cases.consume [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        guess_instance ctxt rule i st
        |> Seq.map (rule_instance ctxt (burrow_options (Variable.polymorphic ctxt) taking))
        |> Seq.maps (fn rule' =>
          CASES (Rule_Cases.make_common (thy,
              Thm.prop_of (Rule_Cases.internalize_params rule')) cases)
            (Method.insert_tac more_facts i THEN rtac rule' i) st)))
  end;

end;



(** concrete syntax **)

val arbitraryN = "arbitrary";
val takingN = "taking";
val ruleN = "rule";

local

fun single_rule [rule] = rule
  | single_rule _ = error "Single rule expected";

fun named_rule k arg get =
  Scan.lift (Args.$$$ k -- Args.colon) |-- Scan.repeat arg :|--
    (fn names => Scan.peek (fn context => Scan.succeed (names |> map (fn name =>
      (case get (Context.proof_of context) name of SOME x => x
      | NONE => error ("No rule for " ^ k ^ " " ^ quote name))))));

fun rule get_type get_pred =
  named_rule typeN (Args.type_name false) get_type ||
  named_rule predN (Args.const false) get_pred ||
  named_rule setN (Args.const false) get_pred ||
  Scan.lift (Args.$$$ ruleN -- Args.colon) |-- Attrib.thms;

val cases_rule = rule lookup_casesT lookup_casesP >> single_rule;
val induct_rule = rule lookup_inductT lookup_inductP;
val coinduct_rule = rule lookup_coinductT lookup_coinductP >> single_rule;

val inst = Scan.lift (Args.$$$ "_") >> K NONE || Args.term >> SOME;

val inst' = Scan.lift (Args.$$$ "_") >> K NONE ||
  Args.term >> (SOME o rpair false) ||
  Scan.lift (Args.$$$ "(") |-- (Args.term >> (SOME o rpair true)) --|
    Scan.lift (Args.$$$ ")");

val def_inst =
  ((Scan.lift (Args.binding --| (Args.$$$ "\<equiv>" || Args.$$$ "==")) >> SOME)
      -- (Args.term >> rpair false)) >> SOME ||
    inst' >> Option.map (pair NONE);

val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
  error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));

fun unless_more_args scan = Scan.unless (Scan.lift
  ((Args.$$$ arbitraryN || Args.$$$ takingN || Args.$$$ typeN ||
    Args.$$$ predN || Args.$$$ setN || Args.$$$ ruleN) -- Args.colon)) scan;

val arbitrary = Scan.optional (Scan.lift (Args.$$$ arbitraryN -- Args.colon) |--
  Parse.and_list1' (Scan.repeat (unless_more_args free))) [];

val taking = Scan.optional (Scan.lift (Args.$$$ takingN -- Args.colon) |--
  Scan.repeat1 (unless_more_args inst)) [];

in

val cases_setup =
  Method.setup @{binding cases}
    (Args.mode no_simpN --
      (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule) >>
      (fn (no_simp, (insts, opt_rule)) => fn ctxt =>
        METHOD_CASES (fn facts => Seq.DETERM (HEADGOAL
          (cases_tac ctxt (not no_simp) insts opt_rule facts)))))
    "case analysis on types or predicates/sets";

fun gen_induct_setup binding itac =
  Method.setup binding
    (Args.mode no_simpN -- (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
      (arbitrary -- taking -- Scan.option induct_rule)) >>
      (fn (no_simp, (insts, ((arbitrary, taking), opt_rule))) => fn ctxt =>
        RAW_METHOD_CASES (fn facts =>
          Seq.DETERM
            (HEADGOAL (itac ctxt (not no_simp) insts arbitrary taking opt_rule facts)))))
    "induction on types or predicates/sets";

val induct_setup = gen_induct_setup @{binding induct} induct_tac;

val coinduct_setup =
  Method.setup @{binding coinduct}
    (Scan.repeat (unless_more_args inst) -- taking -- Scan.option coinduct_rule >>
      (fn ((insts, taking), opt_rule) => fn ctxt =>
        RAW_METHOD_CASES (fn facts =>
          Seq.DETERM (HEADGOAL (coinduct_tac ctxt insts taking opt_rule facts)))))
    "coinduction on types or predicates/sets";

end;



(** theory setup **)

val setup = attrib_setup #> cases_setup  #> induct_setup #> coinduct_setup;

end;
