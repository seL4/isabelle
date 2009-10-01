(*  Author:     Amine Chaieb, University of Cambridge, 2009
                Jeremy Avigad, Carnegie Mellon University
*)

signature TRANSFER =
sig
  type data
  type entry
  val get: Proof.context -> data
  val del: attribute
  val setup: theory -> theory
end;

structure Transfer : TRANSFER =
struct

val eq_thm = Thm.eq_thm;

type entry = {inj : thm list, emb : thm list, ret : thm list, cong : thm list,
  guess : bool, hints : string list}; 
type data = simpset * (thm * entry) list;

structure Data = GenericDataFun
(
  type T = data;
  val empty = (HOL_ss, []);
  val extend  = I;
  fun merge _ ((ss1, e1), (ss2, e2)) =
    (merge_ss (ss1, ss2), AList.merge eq_thm (K true) (e1, e2));
);

val get = Data.get o Context.Proof;

fun del_data key = apsnd (remove (eq_fst eq_thm) (key, []));

val del = Thm.declaration_attribute (Data.map o del_data);
val add_ss = Thm.declaration_attribute 
   (fn th => Data.map (fn (ss,data) => (ss addsimps [th], data)));

val del_ss = Thm.declaration_attribute 
   (fn th => Data.map (fn (ss,data) => (ss delsimps [th], data)));

val transM_pat = (Thm.dest_arg1 o Thm.dest_arg o cprop_of) @{thm TransferMorphism_def};

fun merge_update eq m (k,v) [] = [(k,v)]
  | merge_update eq m (k,v) ((k',v')::al) = 
           if eq (k,k') then (k',m (v,v')):: al else (k',v') :: merge_update eq m (k,v) al

fun C f x y = f y x

fun simpset_of_entry injonly {inj = inj, emb = emb, ret = ret, cong = cg, guess = g, hints = hints} = 
 HOL_ss addsimps inj addsimps (if injonly then [] else emb@ret) addcongs cg;

fun basic_transfer_rule injonly a0 D0 e leave ctxt0 th = 
 let 
  val ([a,D], ctxt) = apfst (map Drule.dest_term o snd) (Variable.import true (map Drule.mk_term [a0, D0]) ctxt0)
  val (aT,bT) = 
     let val T = typ_of (ctyp_of_term a) 
     in (Term.range_type T, Term.domain_type T)
     end
  val ctxt' = (Variable.declare_term (term_of a) o Variable.declare_term (term_of D) o Variable.declare_thm th) ctxt
  val ns = filter (fn i => Type.could_unify (snd i, aT) andalso not (fst (fst i) mem_string leave)) (Term.add_vars (prop_of th) [])
  val (ins, ctxt'') = Variable.variant_fixes (map (fst o fst) ns) ctxt'
  val cns = map ((cterm_of o ProofContext.theory_of) ctxt'' o Var) ns
  val cfis = map ((cterm_of o ProofContext.theory_of) ctxt'' o (fn n => Free (n, bT))) ins
  val cis = map (Thm.capply a) cfis
  val (hs,ctxt''') = Assumption.add_assumes (map (fn ct => Thm.capply @{cterm "Trueprop"} (Thm.capply D ct)) cfis) ctxt''
  val th1 = Drule.cterm_instantiate (cns~~ cis) th
  val th2 = fold (C implies_elim) hs (fold_rev implies_intr (map cprop_of hs) th1)
  val th3 = Simplifier.asm_full_simplify (Simplifier.context ctxt''' (simpset_of_entry injonly e)) 
                                         (fold_rev implies_intr (map cprop_of hs) th2)
in hd (Variable.export ctxt''' ctxt0 [th3]) end;

local
fun transfer_ruleh a D leave ctxt th = 
 let val (ss,al) = get ctxt
     val a0 = cterm_of (ProofContext.theory_of ctxt) a
     val D0 = cterm_of (ProofContext.theory_of ctxt) D
     fun h (th', e) = let val (a',D') = (Thm.dest_binop o Thm.dest_arg o cprop_of) th' 
                 in if a0 aconvc a' andalso D0 aconvc D' then SOME e else NONE
                 end
 in case get_first h al of
      SOME e => basic_transfer_rule false a0 D0 e leave ctxt th
    | NONE => error "Transfer: corresponding instance not found in context-data"
 end
in fun transfer_rule (a,D) leave (gctxt,th) = 
   (gctxt, transfer_ruleh a D leave (Context.proof_of gctxt) th)
end;

fun  splits P [] = []
   | splits P (xxs as (x::xs)) = 
    let val pss = filter (P x) xxs
        val qss = filter_out (P x) xxs
    in if null pss then [qss] else if null qss then [pss] else pss:: splits P qss
    end

fun all_transfers leave (gctxt,th) = 
 let 
  val ctxt = Context.proof_of gctxt
  val tys = map snd (Term.add_vars (prop_of th) [])
  val _ = if null tys then error "transfer: Unable to guess instance" else ()
  val tyss = splits (curry Type.could_unify) tys 
  val get_ty = typ_of o ctyp_of_term o fst o Thm.dest_binop o Thm.dest_arg o cprop_of
  val get_aD = Thm.dest_binop o Thm.dest_arg o cprop_of
  val insts = 
    map_filter (fn tys => 
          get_first (fn (k,ss) => if Type.could_unify (hd tys, range_type (get_ty k)) 
                                  then SOME (get_aD k, ss) 
                                  else NONE) (snd (get ctxt))) tyss
  val _ = if null insts then error "Transfer guesser: there were no possible instances, use direction: in order to provide a direction" else ()
  val ths = map  (fn ((a,D),e) => basic_transfer_rule false a D e leave ctxt th) insts
  val cth = Conjunction.intr_balanced ths
 in (gctxt, cth)
 end;

fun transfer_rule_by_hint ls leave (gctxt,th) = 
 let 
  val ctxt = Context.proof_of gctxt
  val get_aD = Thm.dest_binop o Thm.dest_arg o cprop_of
  val insts = 
    map_filter (fn (k,e) => if exists (fn l => l mem_string (#hints e)) ls 
          then SOME (get_aD k, e) else NONE)
        (snd (get ctxt))
  val _ = if null insts then error "Transfer: No labels provided are stored in the context" else ()
  val ths = map  (fn ((a,D),e) => basic_transfer_rule false a D e leave ctxt th) insts
  val cth = Conjunction.intr_balanced ths
 in (gctxt, cth)
 end;


fun transferred_attribute ls NONE leave = 
         if null ls then all_transfers leave else transfer_rule_by_hint ls leave
  | transferred_attribute _ (SOME (a,D)) leave = transfer_rule (a,D) leave

                                                    (* Add data to the context *)
fun gen_merge_entries {inj = inj0, emb = emb0, ret = ret0, cong = cg0, guess = g0, hints = hints0}
                      ({inj = inj1, emb = emb1, ret = ret1, cong = cg1, guess = g1, hints = hints1}, 
                       {inj = inj2, emb = emb2, ret = ret2, cong = cg2, guess = g2, hints = hints2})
 = 
 let fun h xs0 xs ys = subtract Thm.eq_thm xs0 (merge Thm.eq_thm (xs,ys)) in
 {inj = h inj0 inj1 inj2, emb = h emb0 emb1 emb2, 
  ret = h ret0 ret1 ret2, cong = h cg0 cg1 cg2, guess = g1 andalso g2,
  hints = subtract (op = : string*string -> bool) hints0 
            (hints1 union_string hints2)}
 end;

local
 val h = curry (merge Thm.eq_thm)
in
fun merge_entries ({inj = inj1, emb = emb1, ret = ret1, cong = cg1, guess = g1, hints = hints1}, 
                   {inj = inj2, emb = emb2, ret = ret2, cong = cg2, guess = g2, hints = hints2}) = 
    {inj = h inj1 inj2, emb = h emb1 emb2, ret = h ret1 ret2, cong = h cg1 cg2, guess = g1 andalso g2, hints = hints1 union_string hints2}
end; 

fun add ((inja,injd), (emba,embd), (reta,retd), (cga,cgd), g, (hintsa, hintsd)) =
  Thm.declaration_attribute (fn key => fn context => context |> Data.map
   (fn (ss, al) => 
     let
      val _ = ((let val _ = Thm.match (transM_pat, (Thm.dest_arg o cprop_of) key) 
                in 0 end) 
                handle MATCH => error "Attribute expected Theorem of the form : TransferMorphism A a B b")
      val e0 = {inj = inja, emb = emba, ret = reta, cong = cga, guess = g, hints = hintsa}
      val ed = {inj = injd, emb = embd, ret = retd, cong = cgd, guess = g, hints = hintsd}
      val entry = 
        if g then 
         let val (a0,D0) = (Thm.dest_binop o Thm.dest_arg o cprop_of) key
             val ctxt0 = ProofContext.init (Thm.theory_of_thm key)
             val inj' = if null inja then #inj (case AList.lookup eq_thm al key of SOME e => e | NONE => error "Transfer: can not generate return rules on the fly, either add injectivity axiom or force manual mode with mode: manual") 
                        else inja
             val ret' = merge Thm.eq_thm (reta,  map (fn th => basic_transfer_rule true a0 D0 {inj = inj', emb = [], ret = [], cong = cga, guess = g, hints = hintsa} [] ctxt0 th RS sym) emba)
         in {inj = inja, emb = emba, ret = ret', cong = cga, guess = g, hints = hintsa} end 
        else e0
    in (ss, merge_update eq_thm (gen_merge_entries ed) (key, entry) al)
    end));



(* concrete syntax *)

local

fun keyword k = Scan.lift (Args.$$$ k) >> K ()
fun keywordC k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()

val congN = "cong"
val injN = "inj"
val embedN = "embed"
val returnN = "return"
val addN = "add"
val delN = "del"
val modeN = "mode"
val automaticN = "automatic"
val manualN = "manual"
val directionN = "direction"
val labelsN = "labels"
val leavingN = "leaving"

val any_keyword = keywordC congN || keywordC injN || keywordC embedN || keywordC returnN || keywordC directionN || keywordC modeN || keywordC delN || keywordC labelsN || keywordC leavingN

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat
val terms = thms >> map Drule.dest_term
val types = thms >> (Logic.dest_type o HOLogic.dest_Trueprop o prop_of o hd) 
val name = Scan.lift Args.name
val names = Scan.repeat (Scan.unless any_keyword name)
fun optional scan = Scan.optional scan []
fun optional2 scan = Scan.optional scan ([],[])

val mode = keywordC modeN |-- ((Scan.lift (Args.$$$ manualN) >> K false) || (Scan.lift (Args.$$$ automaticN) >> K true))
val inj = (keywordC injN |-- thms) -- optional (keywordC delN |-- thms)
val embed = (keywordC embedN |-- thms) -- optional (keywordC delN |-- thms)
val return = (keywordC returnN |-- thms) -- optional (keywordC delN |-- thms)
val cong = (keywordC congN |-- thms) -- optional (keywordC delN |-- thms)
val addscan = Scan.unless any_keyword (keyword addN)
val labels = (keywordC labelsN |-- names) -- optional (keywordC delN |-- names)
val entry = Scan.optional mode true -- optional2 inj -- optional2 embed -- optional2 return -- optional2 cong -- optional2 labels

val transf_add = addscan |-- entry
in

val install_att_syntax =
  (Scan.lift (Args.$$$ delN >> K del) ||
    transf_add
    >> (fn (((((g, inj), embed), ret), cg), hints) => add (inj, embed, ret, cg, g, hints)))

val transferred_att_syntax = (optional names -- Scan.option (keywordC directionN |-- (Args.term -- Args.term))
  -- optional (keywordC leavingN |-- names) >> (fn ((hints, aD),leave) => transferred_attribute hints aD leave));

end;


(* theory setup *)

val setup =
  Attrib.setup @{binding transfer} install_att_syntax
    "Installs transfer data" #>
  Attrib.setup @{binding transfer_simps} (Attrib.add_del add_ss del_ss)
    "simp rules for transfer" #>
  Attrib.setup @{binding transferred} transferred_att_syntax
    "Transfers theorems";

end;
