(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Carsten Clasohm and Tobias Nipkow and Markus Wenzel, TU Muenchen

User level interface to thm database (see also Pure/pure_thy.ML).
*)

signature BASIC_THM_DATABASE =
sig
  val store_thm: string * thm -> thm
  val qed_thm: thm option ref
  val bind_thm: string * thm -> unit
  val qed: string -> unit
  val qed_goal: string -> theory -> string -> (thm list -> tactic list) -> unit
  val qed_goalw: string -> theory -> thm list -> string -> (thm list -> tactic list) -> unit
  (*these peek at the proof state!*)
  val thms_containing: xstring list -> (string * thm) list
  val findI: int -> (string * thm) list
  val findEs: int -> (string * thm) list
  val findE: int -> int -> (string * thm) list
end;

signature THM_DATABASE =
sig
  include BASIC_THM_DATABASE
  val ml_store_thm: string * thm -> unit
  val is_ml_identifier: string -> bool
end;

structure ThmDatabase: THM_DATABASE =
struct

(** store theorems **)

(* store in theory and generate HTML *)

fun store_thm (name, thm) =
  let val thm' = PureThy.smart_store_thm (name, thm)
  in Present.theorem name thm'; thm' end;


(* store on ML toplevel *)

val qed_thm: thm option ref = ref None;

val ml_reserved =
 ["abstype", "and", "andalso", "as", "case", "do", "datatype", "else",
  "end", "exception", "fn", "fun", "handle", "if", "in", "infix",
  "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse",
  "raise", "rec", "then", "type", "val", "with", "withtype", "while",
  "eqtype", "functor", "include", "sharing", "sig", "signature",
  "struct", "structure", "where"];

fun is_ml_identifier name =
  Syntax.is_identifier name andalso not (name mem ml_reserved);

fun ml_store_thm (name, thm) =
  let val thm' = store_thm (name, thm) in
    if is_ml_identifier name then
      (qed_thm := Some thm';
        use_text true ("val " ^ name ^ " = the (! ThmDatabase.qed_thm);"))
    else warning ("Cannot bind thm " ^ quote name ^ " as ML value")
  end;

fun bind_thm (name, thm) = ml_store_thm (name, standard thm);
fun qed name = ml_store_thm (name, result ());
fun qed_goal name thy goal tacsf = ml_store_thm (name, prove_goal thy goal tacsf);
fun qed_goalw name thy rews goal tacsf = ml_store_thm (name, prove_goalw thy rews goal tacsf);



(** retrieve theorems **)

(*get theorems that contain all of given constants*)
fun thms_containing raw_consts =
  let
    val sign = sign_of_thm (topthm ());
    val consts = map (Sign.intern_const sign) raw_consts;
    val thy = ThyInfo.theory_of_sign sign;
  in PureThy.thms_containing thy consts end;


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

(*assume that parameters have unique names*)
fun goal_params i =
  let val gi = getgoal i
      val frees = map Free (Logic.strip_params gi)
  in (gi,frees) end;

fun concl_of_goal i =
  let val (gi,frees) = goal_params i
      val B = Logic.strip_assums_concl gi
  in subst_bounds(frees,B) end;

fun prems_of_goal i =
  let val (gi,frees) = goal_params i
      val As = Logic.strip_assums_hyp gi
  in map (fn A => subst_bounds(frees,A)) As end;

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
