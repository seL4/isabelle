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
  val trivial_tac: Proof.context -> int -> tactic
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
  val map_simpset: (Proof.context -> Proof.context) -> Context.generic -> Context.generic
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
  val arbitrary_tac: Proof.context -> int -> (string * typ) list -> int -> tactic
  val add_defs: (binding option * (term * bool)) option list -> Proof.context ->
    (term option list * thm list) * Proof.context
  val atomize_term: Proof.context -> term -> term
  val atomize_cterm: Proof.context -> conv
  val atomize_tac: Proof.context -> int -> tactic
  val inner_atomize_tac: Proof.context -> int -> tactic
  val rulified_term: Proof.context -> thm -> term
  val rulify_tac: Proof.context -> int -> tactic
  val simplified_rule: Proof.context -> thm -> thm
  val simplify_tac: Proof.context -> int -> tactic
  val trivial_tac: Proof.context -> int -> tactic
  val rotate_tac: int -> int -> int -> tactic
  val internalize: Proof.context -> int -> thm -> thm
  val guess_instance: Proof.context -> thm -> int -> thm -> thm Seq.seq
  val cases_context_tactic: bool -> term option list list -> thm option ->
    thm list -> int -> context_tactic
  val cases_tac: Proof.context -> bool -> term option list list -> thm option ->
    thm list -> int -> tactic
  val get_inductT: Proof.context -> term option list list -> thm list list
  val gen_induct_context_tactic: ((Rule_Cases.info * int) * thm -> (Rule_Cases.info * int) * thm) ->
    bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic
  val gen_induct_tac: Proof.context ->
    ((Rule_Cases.info * int) * thm -> (Rule_Cases.info * int) * thm) ->
    bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> tactic
  val induct_context_tactic: bool ->
    (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic
  val induct_tac: Proof.context -> bool ->
    (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> tactic
  val coinduct_context_tactic: term option list -> term option list -> thm option ->
    thm list -> int -> context_tactic
  val coinduct_tac: Proof.context -> term option list -> term option list -> thm option ->
    thm list -> int -> tactic
  val gen_induct_setup: binding ->
   (bool -> (binding option * (term * bool)) option list list ->
    (string * typ) list list -> term option list -> thm list option ->
    thm list -> int -> context_tactic) -> local_theory -> local_theory
end;

functor Induct(Induct_Args: INDUCT_ARGS): INDUCT =
struct

(** variables -- ordered left-to-right, preferring right **)

fun vars_of tm =
  rev (distinct (op =) (Term.fold_aterms (fn t as Var _ => cons t | _ => I) tm []));

local

val mk_var = Net.encode_type o #2 o Term.dest_Var;

fun concl_var which thm = mk_var (which (vars_of (Thm.concl_of thm))) handle List.Empty =>
  raise THM ("No variables in conclusion of rule", 0, [thm]);

in

fun left_var_prem thm = mk_var (hd (vars_of (hd (Thm.prems_of thm)))) handle List.Empty =>
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
          Conv.forall_conv (conv1 (k - 1) o snd) ctxt;
    fun conv2 0 ctxt = conv1 j ctxt
      | conv2 k ctxt = Conv.forall_conv (conv2 (k - 1) o snd) ctxt;
  in conv2 i ctxt end;

fun swap_prems_conv 0 = Conv.all_conv
  | swap_prems_conv i =
      Conv.implies_concl_conv (swap_prems_conv (i - 1)) then_conv
      Conv.rewr_conv Drule.swap_prems_eq;

fun find_eq ctxt t =
  let
    val l = length (Logic.strip_params t);
    val Hs = Logic.strip_assums_hyp t;
    fun find (i, t) =
      (case Induct_Args.dest_def (Object_Logic.drop_judgment ctxt t) of
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
  (case find_eq ctxt (Thm.term_of ct) of
    NONE => NONE
  | SOME (i, k, j) => SOME (swap_params_conv ctxt k j (K (swap_prems_conv i)) ct));

val rearrange_eqs_simproc =
  Simplifier.make_simproc \<^context> "rearrange_eqs"
   {lhss = [\<^term>\<open>Pure.all (t :: 'a::{} \<Rightarrow> prop)\<close>],
    proc = fn _ => fn ctxt => fn ct => mk_swap_rrule ctxt ct};


(* rotate k premises to the left by j, skipping over first j premises *)

fun rotate_conv 0 _ 0 = Conv.all_conv
  | rotate_conv 0 j k = swap_prems_conv j then_conv rotate_conv 1 j (k - 1)
  | rotate_conv i j k = Conv.implies_concl_conv (rotate_conv (i - 1) j k);

fun rotate_tac _ 0 = K all_tac
  | rotate_tac j k = SUBGOAL (fn (goal, i) =>
      CONVERSION (rotate_conv
        j (length (Logic.strip_assums_hyp goal) - j - k) k) i);


(* rulify operators around definition *)

fun rulify_defs_conv ctxt ct =
  if exists_subterm (is_some o Induct_Args.dest_def) (Thm.term_of ct) andalso
    not (is_some (Induct_Args.dest_def (Object_Logic.drop_judgment ctxt (Thm.term_of ct))))
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

fun pretty_rules ctxt kind rs =
  let val thms = map snd (Item_Net.content rs)
  in Pretty.big_list kind (map (Thm.pretty_thm_item ctxt) thms) end;


(* context data *)

structure Data = Generic_Data
(
  type T = (rules * rules) * (rules * rules) * (rules * rules) * simpset;
  val empty =
    ((init_rules (left_var_prem o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (right_var_concl o #2), init_rules (Thm.major_prem_of o #2)),
     (init_rules (left_var_concl o #2), init_rules (Thm.concl_of o #2)),
     simpset_of (empty_simpset \<^context>
      addsimprocs [rearrange_eqs_simproc] addsimps [Drule.norm_hhf_eq]));
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
    |> Pretty.writeln_chunks
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_induct_rules\<close>
    "print induction and cases rules"
    (Scan.succeed (Toplevel.keep (print_rules o Toplevel.context_of)));


(* access rules *)

local

fun lookup_rule which ctxt =
  AList.lookup (op =) (Item_Net.content (which (get_local ctxt)))
  #> Option.map (Thm.transfer' ctxt);

fun find_rules which how ctxt x =
  Item_Net.retrieve (which (get_local ctxt)) (how x)
  |> map (Thm.transfer' ctxt o snd);

in

val lookup_casesT = lookup_rule (#1 o #1);
val lookup_casesP = lookup_rule (#2 o #1);
val lookup_inductT = lookup_rule (#1 o #2);
val lookup_inductP = lookup_rule (#2 o #2);
val lookup_coinductT = lookup_rule (#1 o #3);
val lookup_coinductP = lookup_rule (#2 o #3);

val find_casesT = find_rules (#1 o #1) Net.encode_type;
val find_casesP = find_rules (#2 o #1) I;
val find_inductT = find_rules (#1 o #2) Net.encode_type;
val find_inductP = find_rules (#2 o #2) I;
val find_coinductT = find_rules (#1 o #3) Net.encode_type;
val find_coinductP = find_rules (#2 o #3) I;

end;



(** attributes **)

local

fun mk_att f g name =
  Thm.mixed_attribute (fn (context, thm) =>
    let
      val thm' = g thm;
      val context' =
        if Thm.is_free_dummy thm then context
        else Data.map (f (name, Thm.trim_context thm')) context;
    in (context', thm') end);

fun del_att which =
  Thm.declaration_attribute (fn th => Data.map (which (apply2 (fn rs =>
    fold Item_Net.remove (filter_rules rs th) rs))));

fun add_casesT rule x = @{apply 4(1)} (apfst (Item_Net.update rule)) x;
fun add_casesP rule x = @{apply 4(1)} (apsnd (Item_Net.update rule)) x;
fun add_inductT rule x = @{apply 4(2)} (apfst (Item_Net.update rule)) x;
fun add_inductP rule x = @{apply 4(2)} (apsnd (Item_Net.update rule)) x;
fun add_coinductT rule x = @{apply 4(3)} (apfst (Item_Net.update rule)) x;
fun add_coinductP rule x = @{apply 4(3)} (apsnd (Item_Net.update rule)) x;

val consumes0 = Rule_Cases.default_consumes 0;
val consumes1 = Rule_Cases.default_consumes 1;

in

val cases_type = mk_att add_casesT consumes0;
val cases_pred = mk_att add_casesP consumes1;
val cases_del = del_att @{apply 4(1)};

val induct_type = mk_att add_inductT consumes0;
val induct_pred = mk_att add_inductP consumes1;
val induct_del = del_att @{apply 4(2)};

val coinduct_type = mk_att add_coinductT consumes0;
val coinduct_pred = mk_att add_coinductP consumes1;
val coinduct_del = del_att @{apply 4(3)};

fun map_simpset f context =
  context |> (Data.map o @{apply 4(4)} o Simplifier.simpset_map (Context.proof_of context)) f;

fun induct_simp f =
  Thm.declaration_attribute (fn thm => map_simpset (fn ctxt => f (ctxt, [thm])));

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
  spec typeN (Args.type_name {proper = false, strict = false}) >> add_type ||
  spec predN (Args.const {proper = false, strict = false}) >> add_pred ||
  spec setN (Args.const {proper = false, strict = false}) >> add_pred ||
  Scan.lift Args.del >> K del;

in

val _ =
  Theory.local_setup
   (Attrib.local_setup \<^binding>\<open>cases\<close> (attrib cases_type cases_pred cases_del)
      "declaration of cases rule" #>
    Attrib.local_setup \<^binding>\<open>induct\<close> (attrib induct_type induct_pred induct_del)
      "declaration of induction rule" #>
    Attrib.local_setup \<^binding>\<open>coinduct\<close> (attrib coinduct_type coinduct_pred coinduct_del)
      "declaration of coinduction rule" #>
    Attrib.local_setup \<^binding>\<open>induct_simp\<close> (Attrib.add_del induct_simp_add induct_simp_del)
      "declaration of rules for simplifying induction or cases rules");

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
    fun prep_var (Var (x, xT), SOME t) =
          let
            val ct = Thm.cterm_of ctxt (tune t);
            val tT = Thm.typ_of_cterm ct;
          in
            if Type.could_unify (tT, xT) then SOME (x, ct)
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
     (Raw_Simplifier.rewrite ctxt false [equal_def']))) ctxt));

fun unmark_constraints ctxt =
  Conv.fconv_rule (Raw_Simplifier.rewrite ctxt true [Induct_Args.equal_def]);


(* simplify *)

fun simplify_conv' ctxt =
  Simplifier.full_rewrite (put_simpset (#4 (get_local ctxt)) ctxt);

fun simplify_conv ctxt ct =
  if exists_subterm (is_some o Induct_Args.dest_def) (Thm.term_of ct) then
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

fun cases_context_tactic simp insts opt_rule facts i : context_tactic =
  fn (ctxt, st) =>
    let
      fun inst_rule r =
        (if null insts then r
         else
           (align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
             |> maps (prep_inst ctxt align_left I)
             |> infer_instantiate ctxt) r)
        |> simp ? mark_constraints (Rule_Cases.get_constraints r) ctxt
        |> pair (Rule_Cases.get r);
  
      val (opt_rule', facts') =
        (case (opt_rule, facts) of
          (NONE, th :: ths) =>
            if is_some (Object_Logic.elim_concl ctxt th) then (SOME th, ths)
            else (opt_rule, facts)
        | _ => (opt_rule, facts));
  
      val ruleq =
        (case opt_rule' of
          SOME r => Seq.single (inst_rule r)
        | NONE =>
            (get_casesP ctxt facts' @ get_casesT ctxt insts @ [Induct_Args.cases_default])
            |> tap (trace_rules ctxt casesN)
            |> Seq.of_list |> Seq.maps (Seq.try inst_rule));
    in
      ruleq
      |> Seq.maps (Rule_Cases.consume ctxt [] facts')
      |> Seq.maps (fn ((cases, (_, facts'')), rule) =>
        let
          val rule' = rule
            |> simp ? (simplified_rule' ctxt #> unmark_constraints ctxt);
        in
          CONTEXT_CASES (Rule_Cases.make_common ctxt
              (Thm.prop_of (Rule_Cases.internalize_params rule')) cases)
            ((Method.insert_tac ctxt facts'' THEN' resolve_tac ctxt [rule'] THEN_ALL_NEW
                (if simp then TRY o trivial_tac ctxt else K all_tac)) i) (ctxt, st)
        end)
    end;

fun cases_tac ctxt x1 x2 x3 x4 x5 =
  NO_CONTEXT_TACTIC ctxt (cases_context_tactic x1 x2 x3 x4 x5);

end;



(** induct method **)

val conjunction_congs = @{thms Pure.all_conjunction imp_conjunction};


(* atomize *)

fun atomize_term ctxt =
  Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) Induct_Args.atomize []
  #> Object_Logic.drop_judgment ctxt;

fun atomize_cterm ctxt = Raw_Simplifier.rewrite ctxt true Induct_Args.atomize;

fun atomize_tac ctxt = rewrite_goal_tac ctxt Induct_Args.atomize;

fun inner_atomize_tac ctxt =
  rewrite_goal_tac ctxt (map Thm.symmetric conjunction_congs) THEN' atomize_tac ctxt;


(* rulify *)

fun rulify_term thy =
  Raw_Simplifier.rewrite_term thy (Induct_Args.rulify @ conjunction_congs) [] #>
  Raw_Simplifier.rewrite_term thy Induct_Args.rulify_fallback [];

fun rulified_term ctxt thm =
  let
    val rulify = rulify_term (Proof_Context.theory_of ctxt);
    val (As, B) = Logic.strip_horn (Thm.prop_of thm);
  in Logic.list_implies (map rulify As, rulify B) end;

fun rulify_tac ctxt =
  rewrite_goal_tac ctxt (Induct_Args.rulify @ conjunction_congs) THEN'
  rewrite_goal_tac ctxt Induct_Args.rulify_fallback THEN'
  Goal.conjunction_tac THEN_ALL_NEW
  (rewrite_goal_tac ctxt @{thms Pure.conjunction_imp} THEN' Goal.norm_hhf_tac ctxt);


(* prepare rule *)

fun rule_instance ctxt inst rule =
  infer_instantiate ctxt (prep_inst ctxt align_left I (Thm.prop_of rule, inst)) rule;

fun internalize ctxt k th =
  th |> Thm.permute_prems 0 k
  |> Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of th - k) (atomize_cterm ctxt));


(* guess rule instantiation -- cannot handle pending goal parameters *)

local

fun insts_env ctxt env =
  let
    val pairs = Vartab.dest (Envir.term_env env);
    val types = Vartab.dest (Envir.type_env env);
    val ts = map (Thm.cterm_of ctxt o Envir.norm_term env o #2 o #2) pairs;
    val xs = map #1 pairs ~~ map Thm.typ_of_cterm ts;
    val instT =
      TVars.build (types |> fold (fn (ai, (S, T)) => TVars.add ((ai, S), Thm.ctyp_of ctxt T)));
    val inst = Vars.build (fold2 (fn x => fn t => Vars.add (x, t)) xs ts);
  in (instT, inst) end;

in

fun guess_instance ctxt rule i st =
  let
    val maxidx = Thm.maxidx_of st;
    val goal = Thm.term_of (Thm.cprem_of st i);  (*exception Subscript*)
    val params = rev (Term.rename_wrt_term goal (Logic.strip_params goal));
  in
    if not (null params) then
      (warning ("Cannot determine rule instantiation due to pending parameter(s): " ^
        commas_quote (map (Syntax.string_of_term ctxt o Syntax_Trans.mark_bound_abs) params));
      Seq.single rule)
    else
      let
        val rule' = Thm.incr_indexes (maxidx + 1) rule;
        val concl = Logic.strip_assums_concl goal;
      in
        Unify.smash_unifiers (Context.Proof ctxt)
          [(Thm.concl_of rule', concl)] (Envir.empty (Thm.maxidx_of rule'))
        |> Seq.map (fn env => Drule.instantiate_normalize (insts_env ctxt env) rule')
      end
  end
  handle General.Subscript => Seq.empty;

end;


(* special renaming of rule parameters *)

fun special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (Variable.revert_fixed ctxt z);
        fun index _ [] = []
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
                [] => xs
              | [_] => xs
              | _ => index 1 xs);
          in Logic.list_rename_params xs' A end;
        fun rename_prop prop =
          let val (As, C) = Logic.strip_horn prop
          in Logic.list_implies (map rename_asm As, C) end;
        val thm' = Thm.renamed_prop (rename_prop (Thm.prop_of thm)) thm;
      in [Rule_Cases.save thm thm'] end
  | special_rename_params _ _ ths = ths;


(* arbitrary_tac *)

local

fun goal_prefix k ((c as Const (\<^const_name>\<open>Pure.all\<close>, _)) $ Abs (a, T, B)) =
      c $ Abs (a, T, goal_prefix k B)
  | goal_prefix 0 _ = Term.dummy_prop
  | goal_prefix k ((c as Const (\<^const_name>\<open>Pure.imp\<close>, _)) $ A $ B) =
      c $ A $ goal_prefix (k - 1) B
  | goal_prefix _ _ = Term.dummy_prop;

fun goal_params k (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, B)) = goal_params k B + 1
  | goal_params 0 _ = 0
  | goal_params k (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ B) = goal_params (k - 1) B
  | goal_params _ _ = 0;

fun meta_spec_tac ctxt n (x, T) = SUBGOAL (fn (goal, i) =>
  let
    val v = Free (x, T);
    fun spec_rule prfx (xs, body) =
      @{thm Pure.meta_spec}
      |> Thm.rename_params_rule ([Name.clean (Variable.revert_fixed ctxt x)], 1)
      |> Thm.lift_rule (Thm.cterm_of ctxt prfx)
      |> `(Thm.prop_of #> Logic.strip_assums_concl)
      |-> (fn pred $ arg =>
        infer_instantiate ctxt
          [(#1 (dest_Var (head_of pred)), Thm.cterm_of ctxt (Logic.rlist_abs (xs, body))),
           (#1 (dest_Var (head_of arg)), Thm.cterm_of ctxt (Logic.rlist_abs (xs, v)))]);

    fun goal_concl k xs (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (a, T, B)) =
          goal_concl k ((a, T) :: xs) B
      | goal_concl 0 xs B =
          if not (Term.exists_subterm (fn t => t aconv v) B) then NONE
          else SOME (xs, absfree (x, T) (Term.incr_boundvars 1 B))
      | goal_concl k xs (Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ B) =
          goal_concl (k - 1) xs B
      | goal_concl _ _ _ = NONE;
  in
    (case goal_concl n [] goal of
      SOME concl =>
        (compose_tac ctxt (false, spec_rule (goal_prefix n goal) concl, 1) THEN'
          resolve_tac ctxt [asm_rl]) i
    | NONE => all_tac)
  end);

fun miniscope_tac p =
  CONVERSION o
    Conv.params_conv p (fn ctxt =>
      Raw_Simplifier.rewrite ctxt true [Thm.symmetric Drule.norm_hhf_eq]);

in

fun arbitrary_tac _ _ [] = K all_tac
  | arbitrary_tac ctxt n xs = SUBGOAL (fn (goal, i) =>
     (EVERY' (map (meta_spec_tac ctxt n) xs) THEN'
      (miniscope_tac (goal_params n goal) ctxt)) i);

end;


(* add_defs *)

fun add_defs def_insts =
  let
    fun add (SOME (_, (t, true))) ctxt = ((SOME t, []), ctxt)
      | add (SOME (SOME x, (t, _))) ctxt =
          let val ([(lhs, (_, th))], ctxt') =
            Local_Defs.define [((x, NoSyn), ((Thm.def_binding x, []), t))] ctxt
          in ((SOME lhs, [th]), ctxt') end
      | add (SOME (NONE, (t as Free _, _))) ctxt = ((SOME t, []), ctxt)
      | add (SOME (NONE, (t, _))) ctxt =
          let
            val (s, _) = Name.variant "x" (Variable.names_of ctxt);
            val x = Binding.name s;
            val ([(lhs, (_, th))], ctxt') = ctxt
              |> Local_Defs.define [((x, NoSyn), ((Thm.def_binding x, []), t))];
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

fun gen_induct_context_tactic mod_cases simp def_insts arbitrary taking opt_rule facts =
  CONTEXT_SUBGOAL (fn (_, i) => fn (ctxt, st) =>
    let
      val ((insts, defs), defs_ctxt) = fold_map add_defs def_insts ctxt |>> split_list;
      val atomized_defs = map (map (Conv.fconv_rule (atomize_cterm defs_ctxt))) defs;

      fun inst_rule (concls, r) =
        (if null insts then `Rule_Cases.get r
         else (align_left "Rule has fewer conclusions than arguments given"
            (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
          |> maps (prep_inst ctxt align_right (atomize_term ctxt))
          |> infer_instantiate ctxt) r |> pair (Rule_Cases.get r))
        |> mod_cases
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
          val rule'' = rule' |> simp ? simplified_rule ctxt;
          val nonames = map (fn ((cn, _), cls) => ((cn, []), cls));
          val cases' = if Thm.eq_thm_prop (rule', rule'') then cases else nonames cases;
        in Rule_Cases.make_nested ctxt (Thm.prop_of rule'') (rulified_term ctxt rule'') cases' end;

      fun context_tac _ _ =
        ruleq
        |> Seq.maps (Rule_Cases.consume defs_ctxt (flat defs) facts)
        |> Seq.maps (fn (((cases, concls), (more_consumes, more_facts)), rule) =>
          (PRECISE_CONJUNCTS (length concls) (ALLGOALS (fn j =>
            (CONJUNCTS (ALLGOALS
              let
                val adefs = nth_list atomized_defs (j - 1);
                val frees = fold (Term.add_frees o Thm.prop_of) adefs [];
                val xs = nth_list arbitrary (j - 1);
                val k = nth concls (j - 1) + more_consumes;
              in
                Method.insert_tac defs_ctxt (more_facts @ adefs) THEN'
                  (if simp then
                     rotate_tac k (length adefs) THEN'
                     arbitrary_tac defs_ctxt k (List.partition (member op = frees) xs |> op @)
                   else
                     arbitrary_tac defs_ctxt k xs)
               end)
            THEN' inner_atomize_tac defs_ctxt) j))
          THEN' atomize_tac defs_ctxt) i st
        |> Seq.maps (fn st' =>
              guess_instance ctxt (internalize ctxt more_consumes rule) i st'
              |> Seq.map (rule_instance ctxt (burrow_options (Variable.polymorphic ctxt) taking))
              |> Seq.maps (fn rule' =>
                CONTEXT_CASES (rule_cases ctxt rule' cases)
                  (resolve_tac ctxt [rule'] i THEN
                    PRIMITIVE (singleton (Proof_Context.export defs_ctxt ctxt))) (ctxt, st'))));
    in
      (context_tac CONTEXT_THEN_ALL_NEW
        ((if simp then simplify_tac ctxt THEN' (TRY o trivial_tac ctxt) else K all_tac)
         THEN_ALL_NEW rulify_tac ctxt)) i (ctxt, st)
    end)

val induct_context_tactic = gen_induct_context_tactic I;

fun gen_induct_tac ctxt x1 x2 x3 x4 x5 x6 x7 x8 =
  NO_CONTEXT_TACTIC ctxt (gen_induct_context_tactic x1 x2 x3 x4 x5 x6 x7 x8);

fun induct_tac ctxt x1 x2 x3 x4 x5 x6 x7 =
  NO_CONTEXT_TACTIC ctxt (induct_context_tactic x1 x2 x3 x4 x5 x6 x7);



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

fun coinduct_context_tactic inst taking opt_rule facts =
  CONTEXT_SUBGOAL (fn (goal, i) => fn (ctxt, st) =>
    let
      fun inst_rule r =
        if null inst then `Rule_Cases.get r
        else
          infer_instantiate ctxt (prep_inst ctxt align_right I (main_prop_of r, inst)) r
          |> pair (Rule_Cases.get r);
    in
      (case opt_rule of
        SOME r => Seq.single (inst_rule r)
      | NONE =>
          (get_coinductP ctxt goal @ get_coinductT ctxt inst)
          |> tap (trace_rules ctxt coinductN)
          |> Seq.of_list |> Seq.maps (Seq.try inst_rule))
      |> Seq.maps (Rule_Cases.consume ctxt [] facts)
      |> Seq.maps (fn ((cases, (_, more_facts)), rule) =>
        guess_instance ctxt rule i st
        |> Seq.map (rule_instance ctxt (burrow_options (Variable.polymorphic ctxt) taking))
        |> Seq.maps (fn rule' =>
          CONTEXT_CASES (Rule_Cases.make_common ctxt
              (Thm.prop_of (Rule_Cases.internalize_params rule')) cases)
            (Method.insert_tac ctxt more_facts i THEN resolve_tac ctxt [rule'] i) (ctxt, st)))
    end);

fun coinduct_tac ctxt x1 x2 x3 x4 x5 =
  NO_CONTEXT_TACTIC ctxt (coinduct_context_tactic x1 x2 x3 x4 x5);

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
  named_rule typeN (Args.type_name {proper = false, strict = false}) get_type ||
  named_rule predN (Args.const {proper = false, strict = false}) get_pred ||
  named_rule setN (Args.const {proper = false, strict = false}) get_pred ||
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

fun gen_induct_setup binding tac =
  Method.local_setup binding
    (Scan.lift (Args.mode no_simpN) --
      (Parse.and_list' (Scan.repeat (unless_more_args def_inst)) --
        (arbitrary -- taking -- Scan.option induct_rule)) >>
      (fn (no_simp, (insts, ((arbitrary, taking), opt_rule))) => fn _ => fn facts =>
        Seq.DETERM (tac (not no_simp) insts arbitrary taking opt_rule facts 1)))
    "induction on types or predicates/sets";

val _ =
  Theory.local_setup
    (Method.local_setup \<^binding>\<open>cases\<close>
      (Scan.lift (Args.mode no_simpN) --
        (Parse.and_list' (Scan.repeat (unless_more_args inst)) -- Scan.option cases_rule) >>
        (fn (no_simp, (insts, opt_rule)) => fn _ =>
          CONTEXT_METHOD (fn facts =>
            Seq.DETERM (cases_context_tactic (not no_simp) insts opt_rule facts 1))))
      "case analysis on types or predicates/sets" #>
    gen_induct_setup \<^binding>\<open>induct\<close> induct_context_tactic #>
     Method.local_setup \<^binding>\<open>coinduct\<close>
      (Scan.repeat (unless_more_args inst) -- taking -- Scan.option coinduct_rule >>
        (fn ((insts, taking), opt_rule) => fn _ => fn facts =>
          Seq.DETERM (coinduct_context_tactic insts taking opt_rule facts 1)))
      "coinduction on types or predicates/sets");

end;

end;
