(*  Title:      HOL/Tools/Groebner_Basis/normalizer_data.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

Ring normalization data.
*)

signature NORMALIZER_DATA =
sig
  type entry
  val get: Proof.context -> simpset * (thm * entry) list
  val match: Proof.context -> cterm -> entry option
  val del: attribute
  val add: {semiring: cterm list * thm list, ring: cterm list * thm list, idom: thm list, ideal: thm list}
    -> attribute
  val funs: thm -> {is_const: morphism -> cterm -> bool,
    dest_const: morphism -> cterm -> Rat.rat,
    mk_const: morphism -> ctyp -> Rat.rat -> cterm,
    conv: morphism -> Proof.context -> cterm -> thm} -> declaration
  val setup: theory -> theory
end;

structure NormalizerData: NORMALIZER_DATA =
struct

(* data *)

type entry =
 {vars: cterm list,
  semiring: cterm list * thm list,
  ring: cterm list * thm list,
  idom: thm list,
  ideal: thm list} *
 {is_const: cterm -> bool,
  dest_const: cterm -> Rat.rat,
  mk_const: ctyp -> Rat.rat -> cterm,
  conv: Proof.context -> cterm -> thm};

val eq_key = Thm.eq_thm;
fun eq_data arg = eq_fst eq_key arg;

structure Data = GenericDataFun
(
  type T = simpset * (thm * entry) list;
  val empty = (HOL_basic_ss, []);
  val extend = I;
  fun merge _ ((ss, e), (ss', e')) =
    (merge_ss (ss, ss'), AList.merge eq_key (K true) (e, e'));
);

val get = Data.get o Context.Proof;


(* match data *)

fun match ctxt tm =
  let
    fun match_inst
        ({vars, semiring = (sr_ops, sr_rules), 
          ring = (r_ops, r_rules), idom, ideal},
         fns as {is_const, dest_const, mk_const, conv}) pat =
       let
        fun h instT =
          let
            val substT = Thm.instantiate (instT, []);
            val substT_cterm = Drule.cterm_rule substT;

            val vars' = map substT_cterm vars;
            val semiring' = (map substT_cterm sr_ops, map substT sr_rules);
            val ring' = (map substT_cterm r_ops, map substT r_rules);
            val idom' = map substT idom;
            val ideal' = map substT ideal;

            val result = ({vars = vars', semiring = semiring', 
                           ring = ring', idom = idom', ideal = ideal'}, fns);
          in SOME result end
      in (case try Thm.match (pat, tm) of
           NONE => NONE
         | SOME (instT, _) => h instT)
      end;

    fun match_struct (_,
        entry as ({semiring = (sr_ops, _), ring = (r_ops, _), ...}, _): entry) =
      get_first (match_inst entry) (sr_ops @ r_ops);
  in get_first match_struct (snd (get ctxt)) end;


(* logical content *)

val semiringN = "semiring";
val ringN = "ring";
val idomN = "idom";
val idealN = "ideal";

fun undefined _ = raise Match;

fun del_data key = apsnd (remove eq_data (key, []));

val del = Thm.declaration_attribute (Data.map o del_data);
val add_ss = Thm.declaration_attribute 
   (fn th => Data.map (fn (ss,data) => (ss addsimps [th], data)));

val del_ss = Thm.declaration_attribute 
   (fn th => Data.map (fn (ss,data) => (ss delsimps [th], data)));

fun add {semiring = (sr_ops, sr_rules), ring = (r_ops, r_rules), idom, ideal} =
  Thm.declaration_attribute (fn key => fn context => context |> Data.map
    let
      val ctxt = Context.proof_of context;

      fun check kind name xs n =
        null xs orelse length xs = n orelse
        error ("Expected " ^ string_of_int n ^ " " ^ kind ^ " for " ^ name);
      val check_ops = check "operations";
      val check_rules = check "rules";

      val _ =
        check_ops semiringN sr_ops 5 andalso
        check_rules semiringN sr_rules 37 andalso
        check_ops ringN r_ops 2 andalso
        check_rules ringN r_rules 2 andalso
        check_rules idomN idom 2;

      val mk_meta = LocalDefs.meta_rewrite_rule ctxt;
      val sr_rules' = map mk_meta sr_rules;
      val r_rules' = map mk_meta r_rules;

      fun rule i = nth sr_rules' (i - 1);

      val (cx, cy) = Thm.dest_binop (hd sr_ops);
      val cz = rule 34 |> Thm.rhs_of |> Thm.dest_arg |> Thm.dest_arg;
      val cn = rule 36 |> Thm.rhs_of |> Thm.dest_arg |> Thm.dest_arg;
      val ((clx, crx), (cly, cry)) =
        rule 13 |> Thm.rhs_of |> Thm.dest_binop |> pairself Thm.dest_binop;
      val ((ca, cb), (cc, cd)) =
        rule 20 |> Thm.lhs_of |> Thm.dest_binop |> pairself Thm.dest_binop;
      val cm = rule 1 |> Thm.rhs_of |> Thm.dest_arg;
      val (cp, cq) = rule 26 |> Thm.lhs_of |> Thm.dest_binop |> pairself Thm.dest_arg;

      val vars = [ca, cb, cc, cd, cm, cn, cp, cq, cx, cy, cz, clx, crx, cly, cry];
      val semiring = (sr_ops, sr_rules');
      val ring = (r_ops, r_rules');
      val ideal' = map (symmetric o mk_meta) ideal
    in
      del_data key #>
      apsnd (cons (key, ({vars = vars, semiring = semiring, 
                          ring = ring, idom = idom, ideal = ideal'},
             {is_const = undefined, dest_const = undefined, mk_const = undefined,
             conv = undefined})))
    end);


(* extra-logical functions *)

fun funs raw_key {is_const, dest_const, mk_const, conv} phi = 
 (Data.map o apsnd) (fn data =>
  let
    val key = Morphism.thm phi raw_key;
    val _ = AList.defined eq_key data key orelse
      raise THM ("No data entry for structure key", 0, [key]);
    val fns = {is_const = is_const phi, dest_const = dest_const phi,
      mk_const = mk_const phi, conv = conv phi};
  in AList.map_entry eq_key key (apsnd (K fns)) data end);


(* concrete syntax *)

local

fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
fun keyword2 k1 k2 = Scan.lift (Args.$$$ k1 -- Args.$$$ k2 -- Args.colon) >> K ();
fun keyword3 k1 k2 k3 =
  Scan.lift (Args.$$$ k1 -- Args.$$$ k2 -- Args.$$$ k3 -- Args.colon) >> K ();

val opsN = "ops";
val rulesN = "rules";

val normN = "norm";
val constN = "const";
val delN = "del";

val any_keyword =
  keyword2 semiringN opsN || keyword2 semiringN rulesN ||
  keyword2 ringN opsN || keyword2 ringN rulesN ||
  keyword2 idomN rulesN || keyword2 idealN rulesN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map Drule.dest_term;

fun optional scan = Scan.optional scan [];

in

val normalizer_setup =
  Attrib.setup @{binding normalizer}
    (Scan.lift (Args.$$$ delN >> K del) ||
      ((keyword2 semiringN opsN |-- terms) --
       (keyword2 semiringN rulesN |-- thms)) --
      (optional (keyword2 ringN opsN |-- terms) --
       optional (keyword2 ringN rulesN |-- thms)) --
      optional (keyword2 idomN rulesN |-- thms) --
      optional (keyword2 idealN rulesN |-- thms)
      >> (fn (((sr, r), id), idl) => add {semiring = sr, ring = r, idom = id, ideal = idl}))
    "semiring normalizer data";

end;


(* theory setup *)

val setup =
  normalizer_setup #>
  Attrib.setup @{binding algebra} (Attrib.add_del add_ss del_ss) "pre-simplification for algebra";

end;
