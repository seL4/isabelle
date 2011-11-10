(*  Title:      HOL/Tools/transfer.ML
    Author:     Amine Chaieb, University of Cambridge, 2009
                Jeremy Avigad, Carnegie Mellon University
                Florian Haftmann, TU Muenchen

Simple transfer principle on theorems.
*)

signature TRANSFER =
sig
  datatype selection = Direction of term * term | Hints of string list | Prop
  val transfer: Context.generic -> selection -> string list -> thm -> thm list
  type entry
  val add: thm -> bool -> entry -> Context.generic -> Context.generic
  val del: thm -> entry -> Context.generic -> Context.generic
  val drop: thm -> Context.generic -> Context.generic
  val setup: theory -> theory
end;

structure Transfer : TRANSFER =
struct

(* data administration *)

val direction_of = Thm.dest_binop o Thm.dest_arg o cprop_of;

val transfer_morphism_key = Drule.strip_imp_concl (Thm.cprop_of @{thm transfer_morphismI});

fun check_morphism_key ctxt key =
  let
    val _ = Thm.match (transfer_morphism_key, Thm.cprop_of key)
      handle Pattern.MATCH => error ("Transfer: expected theorem of the form "
        ^ quote (Syntax.string_of_term ctxt (Thm.term_of transfer_morphism_key)));
  in direction_of key end;

type entry = { inj : thm list, embed : thm list, return : thm list, cong : thm list,
  hints : string list };

val empty_entry = { inj = [], embed = [], return = [], cong = [], hints = [] };
fun merge_entry ({ inj = inj1, embed = embed1, return = return1, cong = cong1, hints = hints1 } : entry,
  { inj = inj2, embed = embed2, return = return2, cong = cong2, hints = hints2 } : entry) =
    { inj = merge Thm.eq_thm (inj1, inj2), embed = merge Thm.eq_thm (embed1, embed2),
      return = merge Thm.eq_thm (return1, return2), cong = merge Thm.eq_thm (cong1, cong2),
      hints = merge (op =) (hints1, hints2) };

structure Data = Generic_Data
(
  type T = (thm * entry) list;
  val empty = [];
  val extend = I;
  val merge = AList.join Thm.eq_thm (K merge_entry);
);


(* data lookup *)

fun transfer_rules_of ({ inj, embed, return, cong, ... } : entry) =
  (inj, embed, return, cong);

fun get_by_direction context (a, D) =
  let
    val ctxt = Context.proof_of context;
    val certify = Thm.cterm_of (Context.theory_of context);
    val a0 = certify a;
    val D0 = certify D;
    fun eq_direction ((a, D), thm') =
      let
        val (a', D') = direction_of thm';
      in a aconvc a' andalso D aconvc D' end;
  in case AList.lookup eq_direction (Data.get context) (a0, D0) of
      SOME e => ((a0, D0), transfer_rules_of e)
    | NONE => error ("Transfer: no such instance: ("
        ^ Syntax.string_of_term ctxt a ^ ", " ^ Syntax.string_of_term ctxt D ^ ")")
  end;

fun get_by_hints context hints =
  let
    val insts = map_filter (fn (k, e) => if exists (member (op =) (#hints e)) hints
      then SOME (direction_of k, transfer_rules_of e) else NONE) (Data.get context);
    val _ = if null insts then error ("Transfer: no such labels: " ^ commas_quote hints) else ();
  in insts end;

fun splits P [] = []
  | splits P (xs as (x :: _)) =
      let
        val (pss, qss) = List.partition (P x) xs;
      in if null pss then [qss] else if null qss then [pss] else pss :: splits P qss end;

fun get_by_prop context t =
  let
    val tys = map snd (Term.add_vars t []);
    val _ = if null tys then error "Transfer: unable to guess instance" else ();
    val tyss = splits (curry Type.could_unify) tys;
    val get_ty = typ_of o ctyp_of_term o fst o direction_of;
    val insts = map_filter (fn tys => get_first (fn (k, e) =>
      if Type.could_unify (hd tys, range_type (get_ty k))
      then SOME (direction_of k, transfer_rules_of e)
      else NONE) (Data.get context)) tyss;
    val _ = if null insts then
      error "Transfer: no instances, provide direction or hints explicitly" else ();
  in insts end;


(* applying transfer data *)

fun transfer_thm ((raw_a, raw_D), (inj, embed, return, cong)) leave ctxt1 thm =
  let
    (* identify morphism function *)
    val ([a, D], ctxt2) = ctxt1
      |> Variable.import true (map Drule.mk_term [raw_a, raw_D])
      |>> map Drule.dest_term o snd;
    val transform = Thm.capply @{cterm "Trueprop"} o Thm.capply D;
    val T = Thm.typ_of (Thm.ctyp_of_term a);
    val (aT, bT) = (Term.range_type T, Term.domain_type T);
    
    (* determine variables to transfer *)
    val ctxt3 = ctxt2
      |> Variable.declare_thm thm
      |> Variable.declare_term (term_of a)
      |> Variable.declare_term (term_of D);
    val certify = Thm.cterm_of (Proof_Context.theory_of ctxt3);
    val vars = filter (fn ((v, _), T) => Type.could_unify (T, aT) andalso
      not (member (op =) leave v)) (Term.add_vars (Thm.prop_of thm) []);
    val c_vars = map (certify o Var) vars;
    val (vs', ctxt4) = Variable.variant_fixes (map (fst o fst) vars) ctxt3;
    val c_vars' = map (certify o (fn v => Free (v, bT))) vs';
    val c_exprs' = map (Thm.capply a) c_vars';

    (* transfer *)
    val (hyps, ctxt5) = ctxt4
      |> Assumption.add_assumes (map transform c_vars');
    val simpset = Simplifier.context ctxt5 HOL_ss
      addsimps (inj @ embed @ return) addcongs cong;
    val thm' = thm
      |> Drule.cterm_instantiate (c_vars ~~ c_exprs')
      |> fold_rev Thm.implies_intr (map cprop_of hyps)
      |> Simplifier.asm_full_simplify simpset
  in singleton (Variable.export ctxt5 ctxt1) thm' end;

fun transfer_thm_multiple insts leave ctxt thm =
  map (fn inst => transfer_thm inst leave ctxt thm) insts;

datatype selection = Direction of term * term | Hints of string list | Prop;

fun insts_for context thm (Direction direction) = [get_by_direction context direction]
  | insts_for context thm (Hints hints) = get_by_hints context hints
  | insts_for context thm Prop = get_by_prop context (Thm.prop_of thm);

fun transfer context selection leave thm =
  transfer_thm_multiple (insts_for context thm selection) leave (Context.proof_of context) thm;


(* maintaining transfer data *)

fun extend_entry ctxt (a, D) guess
    { inj = inj1, embed = embed1, return = return1, cong = cong1, hints = hints1 }
    { inj = inj2, embed = embed2, return = return2, cong = cong2, hints = hints2 } =
  let
    fun add_del eq del add = union eq add #> subtract eq del;
    val guessed = if guess
      then map (fn thm => transfer_thm
        ((a, D), (if null inj1 then inj2 else inj1, [], [], cong1)) [] ctxt thm RS sym) embed1
      else [];
  in
    { inj = union Thm.eq_thm inj1 inj2, embed = union Thm.eq_thm embed1 embed2,
      return = union Thm.eq_thm guessed (union Thm.eq_thm return1 return2),
      cong = union Thm.eq_thm cong1 cong2, hints = union (op =) hints1 hints2 }
  end;

fun diminish_entry 
    { inj = inj0, embed = embed0, return = return0, cong = cong0, hints = hints0 }
    { inj = inj2, embed = embed2, return = return2, cong = cong2, hints = hints2 } =
  { inj = subtract Thm.eq_thm inj0 inj2, embed = subtract Thm.eq_thm embed0 embed2,
    return = subtract Thm.eq_thm return0 return2, cong = subtract Thm.eq_thm cong0 cong2,
    hints = subtract (op =) hints0 hints2 };

fun add key guess entry context =
  let
    val ctxt = Context.proof_of context;
    val a_D = check_morphism_key ctxt key;
  in
    context
    |> Data.map (AList.map_default Thm.eq_thm
         (key, empty_entry) (extend_entry ctxt a_D guess entry))
  end;

fun del key entry = Data.map (AList.map_entry Thm.eq_thm key (diminish_entry entry));

fun drop key = Data.map (AList.delete Thm.eq_thm key);


(* syntax *)

local

fun these scan = Scan.optional scan [];
fun these_pair scan = Scan.optional scan ([], []);

fun keyword k = Scan.lift (Args.$$$ k) >> K ();
fun keyword_colon k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val addN = "add";
val delN = "del";
val keyN = "key";
val modeN = "mode";
val automaticN = "automatic";
val manualN = "manual";
val injN = "inj";
val embedN = "embed";
val returnN = "return";
val congN = "cong";
val labelsN = "labels";

val leavingN = "leaving";
val directionN = "direction";

val any_keyword = keyword_colon addN || keyword_colon delN || keyword_colon keyN
  || keyword_colon modeN || keyword_colon injN || keyword_colon embedN || keyword_colon returnN
  || keyword_colon congN || keyword_colon labelsN
  || keyword_colon leavingN || keyword_colon directionN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val names = Scan.repeat (Scan.unless any_keyword (Scan.lift Args.name))

val mode = keyword_colon modeN |-- ((Scan.lift (Args.$$$ manualN) >> K false)
  || (Scan.lift (Args.$$$ automaticN) >> K true));
val inj = (keyword_colon injN |-- thms) -- these (keyword_colon delN |-- thms);
val embed = (keyword_colon embedN |-- thms) -- these (keyword_colon delN |-- thms);
val return = (keyword_colon returnN |-- thms) -- these (keyword_colon delN |-- thms);
val cong = (keyword_colon congN |-- thms) -- these (keyword_colon delN |-- thms);
val labels = (keyword_colon labelsN |-- names) -- these (keyword_colon delN |-- names);

val entry_pair = these_pair inj -- these_pair embed
  -- these_pair return -- these_pair cong -- these_pair labels
  >> (fn (((((inja, injd), (embeda, embedd)), (returna, returnd)), (conga, congd)),
       (hintsa, hintsd)) =>
      ({ inj = inja, embed = embeda, return = returna, cong = conga, hints = hintsa },
        { inj = injd, embed = embedd, return = returnd, cong = congd, hints = hintsd }));

val selection = (keyword_colon directionN |-- (Args.term -- Args.term) >> Direction)
  || these names >> (fn hints => if null hints then Prop else Hints hints);

in

val transfer_attribute = keyword delN >> K (Thm.declaration_attribute drop)
  || keyword addN |-- Scan.optional mode true -- entry_pair
    >> (fn (guess, (entry_add, entry_del)) => Thm.declaration_attribute
      (fn thm => add thm guess entry_add #> del thm entry_del))
  || keyword_colon keyN |-- Attrib.thm
    >> (fn key => Thm.declaration_attribute
      (fn thm => add key false
        { inj = [], embed = [], return = [thm], cong = [], hints = [] }));

val transferred_attribute = selection -- these (keyword_colon leavingN |-- names)
  >> (fn (selection, leave) => Thm.rule_attribute (fn context =>
      Conjunction.intr_balanced o transfer context selection leave));

end;


(* theory setup *)

val setup =
  Attrib.setup @{binding transfer} transfer_attribute
    "Installs transfer data" #>
  Attrib.setup @{binding transferred} transferred_attribute
    "Transfers theorems";

end;
