(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Tobias Nipkow and Markus Wenzel, TU Muenchen

User level interface to thm database (see also Pure/pure_thy.ML).
*)

signature BASIC_THM_DATABASE =
sig
  val store_thm: string * thm -> thm
  val store_thms: string * thm list -> thm list
  val bind_thm: string * thm -> unit
  val bind_thms: string * thm list -> unit
  val qed: string -> unit
  val qed_goal: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw: string -> theory -> thm list -> string -> (thm list -> tactic list) -> unit
  val no_qed: unit -> unit
  (*these peek at the proof state!*)
  val thms_containing: xstring list -> (string * thm) list
  val findI: int -> (string * thm) list
  val findEs: int -> (string * thm) list
  val findE: int -> int -> (string * thm) list
end;

signature THM_DATABASE =
sig
  include BASIC_THM_DATABASE
  val qed_thms: thm list ref
  val ml_store_thm: string * thm -> unit
  val ml_store_thms: string * thm list -> unit
  val is_ml_identifier: string -> bool
  val print_thms_containing: theory -> xstring list -> unit
end;

structure ThmDatabase: THM_DATABASE =
struct

(** store theorems **)

(* store in theory and generate HTML *)

fun store_thm (name, thm) =
  let val thm' = hd (PureThy.smart_store_thms (name, [thm]))
  in Present.theorem name thm'; thm' end;

fun store_thms (name, thms) =
  let val thms' = PureThy.smart_store_thms (name, thms)
  in Present.theorems name thms'; thms' end;


(* store on ML toplevel *)

val qed_thms: thm list ref = ref [];

val ml_reserved =
 ["abstype", "and", "andalso", "as", "case", "do", "datatype", "else",
  "end", "exception", "fn", "fun", "handle", "if", "in", "infix",
  "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse",
  "raise", "rec", "then", "type", "val", "with", "withtype", "while",
  "eqtype", "functor", "include", "sharing", "sig", "signature",
  "struct", "structure", "where"];

fun is_ml_identifier name =
  Syntax.is_identifier name andalso not (name mem ml_reserved);

fun warn_ml name =
  if is_ml_identifier name then false
  else if name = "" then true
  else (warning ("Cannot bind theorem(s) " ^ quote name ^ " as ML value"); true);

val use_text_verbose = use_text writeln true;

fun ml_store_thm (name, thm) =
  let val thm' = store_thm (name, thm) in
    if warn_ml name then ()
    else (qed_thms := [thm']; use_text_verbose ("val " ^ name ^ " = hd (! ThmDatabase.qed_thms);"))
  end;

fun ml_store_thms (name, thms) =
  let val thms' = store_thms (name, thms) in
    if warn_ml name then ()
    else (qed_thms := thms'; use_text_verbose ("val " ^ name ^ " = ! ThmDatabase.qed_thms;"))
  end;

fun bind_thm (name, thm) = ml_store_thm (name, standard thm);
fun bind_thms (name, thms) = ml_store_thms (name, map standard thms);

fun qed name = ml_store_thm (name, Goals.result ());
fun qed_goal name thy goal tacsf = ml_store_thm (name, prove_goal thy goal tacsf);
fun qed_goalw name thy rews goal tacsf = ml_store_thm (name, prove_goalw thy rews goal tacsf);

fun no_qed () = ();



(** retrieve theorems **)

(*get theorems that contain all of given constants*)
fun thms_containing_thy thy raw_consts =
  let val consts = map (Sign.intern_const (Theory.sign_of thy)) raw_consts;
  in PureThy.thms_containing thy consts end
  handle THEORY (msg,_) => error msg;

fun thms_containing cs =
  thms_containing_thy (ThyInfo.theory_of_sign (Thm.sign_of_thm (Goals.topthm ()))) cs;

fun prt_thm (a, th) =
  Pretty.block [Pretty.str (a ^ ":"), Pretty.brk 1,
    Display.pretty_thm_no_quote (#1 (Drule.freeze_thaw th))];

fun print_thms_containing thy cs =
  Pretty.writeln (Pretty.blk (0, Pretty.fbreaks (map prt_thm (thms_containing_thy thy cs))));


(*top_const: main constant, ignoring Trueprop*)
fun top_const (_ $ t) = (case head_of t of Const (c, _) => Some c | _ => None)
  | top_const _ = None;

val intro_const = top_const o concl_of;

fun elim_const thm = case prems_of thm of [] => None | p::_ => top_const p;

(* In case faster access is necessary, the thm db should provide special
functions

index_intros, index_elims: string -> (string * thm) list

where thm [| A1 ; ...; An |] ==> B is returned by
- index_intros c if B  is of the form c t1 ... tn
- index_elims c  if A1 is of the form c t1 ... tn
*)

(* could be provided by thm db *)
fun index_intros c =
  let fun topc(_,thm) = intro_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(* could be provided by thm db *)
fun index_elims c =
  let fun topc(_,thm) = elim_const thm = Some(c);
      val named_thms = thms_containing [c]
  in filter topc named_thms end;

(*assume that parameters have unique names; reverse them for substitution*)
fun goal_params i =
  let val gi = getgoal i
      val rfrees = rev(map Free (Logic.strip_params gi))
  in (gi,rfrees) end;

fun concl_of_goal i =
  let val (gi,rfrees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(rfrees,B) end;

fun prems_of_goal i =
  let val (gi,rfrees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(rfrees,A)) As end;

(*returns all those named_thms whose subterm extracted by extract can be
  instantiated to obj; the list is sorted according to the number of premises
  and the size of the required substitution.*)
fun select_match(obj, signobj, named_thms, extract) =
  let fun matches(prop, tsig) =
            case extract prop of
              None => false
            | Some pat => Pattern.matches tsig (pat, obj);

      fun substsize(prop, tsig) =
            let val Some pat = extract prop
                val (_,subst) = Pattern.match tsig (pat,obj)
            in foldl op+
                (0, map (fn (_,t) => size_of_term t) subst)
            end

      fun thm_ord ((p0,s0,_),(p1,s1,_)) =
            prod_ord (int_ord o pairself (fn 0 => 0 | x => 1)) int_ord ((p0,s0),(p1,s1));

      fun select((p as (_,thm))::named_thms, sels) =
            let val {prop, sign, ...} = rep_thm thm
            in select(named_thms,
                      if Sign.subsig(sign, signobj) andalso
                         matches(prop,#tsig(Sign.rep_sg signobj))
                      then
                        (nprems_of thm,substsize(prop,#tsig(Sign.rep_sg signobj)),p)::sels
                      else sels)
            end
        | select([],sels) = sels

  in map (fn (_,_,t) => t) (sort thm_ord (select(named_thms, []))) end;

fun find_matching(prop,sign,index,extract) =
  (case top_const prop of
     Some c => select_match(prop,sign,index c,extract)
   | _      => []);

fun find_intros(prop,sign) =
  find_matching(prop,sign,index_intros,Some o Logic.strip_imp_concl);

fun find_elims sign prop =
  let fun major prop = case Logic.strip_imp_prems prop of
                         [] => None | p::_ => Some p
  in find_matching(prop,sign,index_elims,major) end;

fun findI i = find_intros(concl_of_goal i,#sign(rep_thm(topthm())));

fun findEs i =
  let fun eq_nth((n1,th1),(n2,th2)) = n1=n2 andalso eq_thm(th1,th2);
      val sign = #sign(rep_thm(topthm()))
      val thmss = map (find_elims sign) (prems_of_goal i)
  in foldl (gen_union eq_nth) ([],thmss) end;

fun findE i j =
  let val sign = #sign(rep_thm(topthm()))
  in find_elims sign (nth_elem(j-1, prems_of_goal i)) end;


end;


structure BasicThmDatabase: BASIC_THM_DATABASE = ThmDatabase;
open BasicThmDatabase;
