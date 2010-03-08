(*  Author:     Amine Chaieb, University of Cambridge, 2009
    Author:     Jeremy Avigad, Carnegie Mellon University
*)

signature TRANSFER =
sig
  type entry
  val get: Proof.context -> (thm * entry) list
  val del: thm -> Context.generic -> Context.generic
  val setup: theory -> theory
end;

structure Transfer : TRANSFER =
struct

(* data administration *)

fun check_morphism_key ctxt key =
  let
    val _ = (Thm.match o pairself Thm.cprop_of) (@{thm transfer_morphismI}, key)
      handle Pattern.MATCH => error
        ("Expected theorem of the form " ^ quote (Display.string_of_thm ctxt @{thm transfer_morphismI}));
  in (Thm.dest_binop o Thm.dest_arg o Thm.cprop_of) key end;

type entry = { inj : thm list, emb : thm list, ret : thm list, cong : thm list,
  guess : bool, hints : string list };

fun merge_entry ({ inj = inj1, emb = emb1, ret = ret1, cong = cong1, guess = guess1, hints = hints1 } : entry,
  { inj = inj2, emb = emb2, ret = ret2, cong = cong2, guess = guess2, hints = hints2 } : entry) =
    { inj = merge Thm.eq_thm (inj1, inj2), emb = merge Thm.eq_thm (emb1, emb2),
      ret = merge Thm.eq_thm (ret1, ret2), cong = merge Thm.eq_thm (cong1, cong2),
      guess = guess1 andalso guess2, hints = merge (op =) (hints1, hints2) };

structure Data = Generic_Data
(
  type T = (thm * entry) list;
  val empty = [];
  val extend  = I;
  val merge = AList.join Thm.eq_thm (K merge_entry);
);

val get = Data.get o Context.Proof;

fun del key = Data.map (remove (eq_fst Thm.eq_thm) (key, []));

val del_attribute = Thm.declaration_attribute del;


(* applying transfer data *)

fun build_simpset inj_only {inj = inj, emb = emb, ret = ret, cong = cg, guess = g, hints = hints} =
  HOL_ss addsimps inj addsimps (if inj_only then [] else emb @ ret) addcongs cg;

fun basic_transfer_rule inj_only a0 D0 e leave ctxt0 th =
  let
    val ([a, D], ctxt) = apfst (map Drule.dest_term o snd)
      (Variable.import true (map Drule.mk_term [a0, D0]) ctxt0);
    val (aT, bT) =
      let val T = typ_of (ctyp_of_term a)
      in (Term.range_type T, Term.domain_type T) end;
    val ctxt' = (Variable.declare_term (term_of a) o Variable.declare_term (term_of D)
      o Variable.declare_thm th) ctxt;
    val ns = filter (fn i => Type.could_unify (snd i, aT) andalso
      not (member (op =) leave (fst (fst i)))) (Term.add_vars (prop_of th) []);
    val (ins, ctxt'') = Variable.variant_fixes (map (fst o fst) ns) ctxt';
    val certify = Thm.cterm_of (ProofContext.theory_of ctxt'');
    val cns = map (certify o Var) ns;
    val cfis = map (certify o (fn n => Free (n, bT))) ins;
    val cis = map (Thm.capply a) cfis
    val (hs, ctxt''') = Assumption.add_assumes (map (fn ct =>
      Thm.capply @{cterm "Trueprop"} (Thm.capply D ct)) cfis) ctxt'';
    val th1 = Drule.cterm_instantiate (cns ~~ cis) th;
    val th2 = fold Thm.elim_implies hs (fold_rev implies_intr (map cprop_of hs) th1);
    val th3 = Simplifier.asm_full_simplify (Simplifier.context ctxt'''
      (build_simpset inj_only e)) (fold_rev implies_intr (map cprop_of hs) th2);
  in hd (Variable.export ctxt''' ctxt0 [th3]) end;

fun transfer_rule (a, D) leave (gctxt, th) =
  let
    fun transfer_ruleh a D leave ctxt th =
      let
        val al = get ctxt;
        val certify = Thm.cterm_of (ProofContext.theory_of ctxt);
        val a0 = certify a;
        val D0 = certify D;
        fun h (th', e) =
          let
            val (a',D') = (Thm.dest_binop o Thm.dest_arg o cprop_of) th'
          in if a0 aconvc a' andalso D0 aconvc D' then SOME e else NONE end;
      in case get_first h al of
          SOME e => basic_transfer_rule false a0 D0 e leave ctxt th
        | NONE => error "Transfer: corresponding instance not found in context data"
      end;
  in 
    (gctxt, transfer_ruleh a D leave (Context.proof_of gctxt) th)
  end;

fun splits P [] = []
  | splits P (xxs as (x :: xs)) =
      let
        val pss = filter (P x) xxs;
        val qss = filter_out (P x) xxs;
      in if null pss then [qss] else if null qss then [pss] else pss:: splits P qss end;

fun all_transfers leave (gctxt, th) =
  let
    val ctxt = Context.proof_of gctxt;
    val tys = map snd (Term.add_vars (prop_of th) []);
    val _ = if null tys then error "transfer: Unable to guess instance" else ();
    val tyss = splits (curry Type.could_unify) tys;
    val get_ty = typ_of o ctyp_of_term o fst o Thm.dest_binop o Thm.dest_arg o cprop_of;
    val get_aD = Thm.dest_binop o Thm.dest_arg o cprop_of;
    val insts =
      map_filter (fn tys =>
        get_first (fn (k,ss) =>
          if Type.could_unify (hd tys, range_type (get_ty k))
          then SOME (get_aD k, ss)
          else NONE) (get ctxt)) tyss;
    val _ =
      if null insts then
        error "Transfer guesser: there were no possible instances, use direction: in order to provide a direction"
      else ();
    val ths = map (fn ((a, D), e) => basic_transfer_rule false a D e leave ctxt th) insts;
    val cth = Conjunction.intr_balanced ths;
  in (gctxt, cth) end;

fun transfer_rule_by_hint ls leave (gctxt, th) =
  let
    val ctxt = Context.proof_of gctxt;
    val get_aD = Thm.dest_binop o Thm.dest_arg o cprop_of;
    val insts = map_filter (fn (k,e) => if exists (member (op =) (#hints e)) ls
      then SOME (get_aD k, e) else NONE) (get ctxt);
    val _ = if null insts then error "Transfer: No labels provided are stored in the context" else ();
    val ths = map  (fn ((a,D),e) => basic_transfer_rule false a D e leave ctxt th) insts;
    val cth = Conjunction.intr_balanced ths;
  in (gctxt, cth) end;

fun transferred_attribute ls NONE leave =
      if null ls then all_transfers leave else transfer_rule_by_hint ls leave
  | transferred_attribute _ (SOME (a, D)) leave = transfer_rule (a, D) leave;


(* adding transfer data *)

fun merge_update eq m (k, v) [] = [(k, v)]
  | merge_update eq m (k, v) ((k', v') :: al) =
      if eq (k, k') then (k', m (v, v')) :: al else (k', v') :: merge_update eq m (k, v) al;

(*? fun merge_update eq m (k, v) = AList.map_entry eq k (fn v' => m (v, v'));*)

fun merge_entries {inj = inj0, emb = emb0, ret = ret0, cong = cg0, guess = g0, hints = hints0}
    ({inj = inj1, emb = emb1, ret = ret1, cong = cg1, guess = g1, hints = hints1},
     {inj = inj2, emb = emb2, ret = ret2, cong = cg2, guess = g2, hints = hints2} : entry) =
  let
    fun h xs0 xs ys = subtract Thm.eq_thm xs0 (merge Thm.eq_thm (xs, ys))
  in
    {inj = h inj0 inj1 inj2, emb = h emb0 emb1 emb2,
     ret = h ret0 ret1 ret2, cong = h cg0 cg1 cg2, guess = g1 andalso g2,
     hints = subtract (op =) hints0 (union (op =) hints1 hints2) }
  end;

fun add ((inja, injd), (emba, embd), (reta, retd), (cga, cgd), g, (hintsa, hintsd)) key =
  Data.map (fn al =>
    let
      val ctxt0 = ProofContext.init (Thm.theory_of_thm key); (*FIXME*)
      val (a0, D0) = check_morphism_key ctxt0 key;
      val e0 = {inj = inja, emb = emba, ret = reta, cong = cga, guess = g, hints = hintsa};
      val ed = {inj = injd, emb = embd, ret = retd, cong = cgd, guess = g, hints = hintsd};
      val entry = if g then
        let
          val inj' = if null inja then #inj
            (case AList.lookup Thm.eq_thm al key of SOME e => e
              | NONE => error "Transfer: cannot generate return rules on the fly, either add injectivity axiom or force manual mode with mode: manual")
            else inja
          val ret' = merge Thm.eq_thm (reta, map
            (fn th => basic_transfer_rule true a0 D0 {inj = inj', emb = [], ret = [], cong = cga, guess = g,
              hints = hintsa} [] ctxt0 th RS sym) emba);
        in {inj = inja, emb = emba, ret = ret', cong = cga, guess = g, hints = hintsa} end
        else e0;
    in merge_update Thm.eq_thm (merge_entries ed) (key, entry) al end);

fun add_attribute args = Thm.declaration_attribute (add args);


(* syntax *)

local

fun these scan = Scan.optional scan [];
fun these_pair scan = Scan.optional scan ([], []);

fun keyword k = Scan.lift (Args.$$$ k) >> K ();
fun keyword_colon k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val congN = "cong";
val injN = "inj";
val embedN = "embed";
val returnN = "return";
val addN = "add";
val delN = "del";
val modeN = "mode";
val automaticN = "automatic";
val manualN = "manual";
val directionN = "direction";
val labelsN = "labels";
val leavingN = "leaving";

val any_keyword = keyword_colon congN || keyword_colon injN || keyword_colon embedN
  || keyword_colon returnN || keyword_colon directionN || keyword_colon modeN
  || keyword_colon delN || keyword_colon labelsN || keyword_colon leavingN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val names = Scan.repeat (Scan.unless any_keyword (Scan.lift Args.name))

val mode = keyword_colon modeN |-- ((Scan.lift (Args.$$$ manualN) >> K false)
  || (Scan.lift (Args.$$$ automaticN) >> K true));
val inj = (keyword_colon injN |-- thms) -- these (keyword_colon delN |-- thms);
val embed = (keyword_colon embedN |-- thms) -- these (keyword_colon delN |-- thms);
val return = (keyword_colon returnN |-- thms) -- these (keyword_colon delN |-- thms);
val cong = (keyword_colon congN |-- thms) -- these (keyword_colon delN |-- thms);
val labels = (keyword_colon labelsN |-- names) -- these (keyword_colon delN |-- names);

val entry = Scan.optional mode true -- these_pair inj -- these_pair embed
  -- these_pair return -- these_pair cong -- these_pair labels;

val transfer_directive = these names -- Scan.option (keyword_colon directionN
  |-- (Args.term -- Args.term)) -- these (keyword_colon leavingN |-- names);

in

val transfer_syntax = (Scan.lift (Args.$$$ delN >> K del_attribute)
  || Scan.unless any_keyword (keyword addN) |-- entry
    >> (fn (((((g, inj), embed), ret), cg), hints) => add_attribute (inj, embed, ret, cg, g, hints)))

val transferred_syntax = transfer_directive
  >> (fn ((hints, aD), leave) => transferred_attribute hints aD leave);

end;


(* theory setup *)

val setup =
  Attrib.setup @{binding transfer} transfer_syntax
    "Installs transfer data" #>
  Attrib.setup @{binding transferred} transferred_syntax
    "Transfers theorems";

end;
