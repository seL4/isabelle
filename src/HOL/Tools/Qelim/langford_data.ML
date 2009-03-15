signature LANGFORD_DATA =
sig
  type entry
  val get: Proof.context -> simpset * (thm * entry) list
  val add: entry -> attribute 
  val del: attribute
  val setup: theory -> theory
  val match: Proof.context -> cterm -> entry option
end;

structure Langford_Data: LANGFORD_DATA = 
struct

(* data *)
type entry = {qe_bnds: thm, qe_nolb : thm , qe_noub: thm, 
              gs : thm list, gst : thm, atoms: cterm list};
val eq_key = Thm.eq_thm;
fun eq_data arg = eq_fst eq_key arg;

structure Data = GenericDataFun
( type T = simpset * (thm * entry) list;
  val empty = (HOL_basic_ss, []);
  val extend = I;
  fun merge _ ((ss1,es1), (ss2,es2)) = 
       (merge_ss (ss1,ss2), AList.merge eq_key (K true) (es1,es2));;
);

val get = Data.get o Context.Proof;

fun del_data key = apsnd (remove eq_data (key, []));

val del = Thm.declaration_attribute (Data.map o del_data);

fun add entry = 
    Thm.declaration_attribute (fn key => fn context => context |> Data.map 
      (del_data key #> apsnd (cons (key, entry))));

val add_simp = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (fn (ss,ts') => (ss addsimps [th], ts'))) 

val del_simp = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (fn (ss,ts') => (ss delsimps [th], ts'))) 

fun match ctxt tm =
  let
    fun match_inst
        {qe_bnds, qe_nolb, qe_noub, gs, gst, atoms} pat =
       let
        fun h instT =
          let
            val substT = Thm.instantiate (instT, []);
            val substT_cterm = Drule.cterm_rule substT;

            val qe_bnds' = substT qe_bnds
            val qe_nolb' = substT qe_nolb
            val qe_noub' = substT qe_noub
            val gs' = map substT gs
            val gst' = substT gst
            val atoms' = map substT_cterm atoms
            val result = {qe_bnds = qe_bnds', qe_nolb = qe_nolb', 
                          qe_noub = qe_noub', gs = gs', gst = gst', 
                          atoms = atoms'}
          in SOME result end
      in (case try Thm.match (pat, tm) of
           NONE => NONE
         | SOME (instT, _) => h instT)
      end;

    fun match_struct (_,
        entry as ({atoms = atoms, ...}): entry) =
      get_first (match_inst entry) atoms;
  in get_first match_struct (snd (get ctxt)) end;

(* concrete syntax *)

local
val qeN = "qe";
val gatherN = "gather";
val atomsN = "atoms"
fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
val any_keyword =
  keyword qeN || keyword gatherN || keyword atomsN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map Drule.dest_term;
in

val attribute =
    (keyword qeN |-- thms)
     -- (keyword gatherN |-- thms)
     -- (keyword atomsN |-- terms) >> 
     (fn ((qes,gs), atoms) => 
     if length qes = 3 andalso length gs > 1 then
       let 
         val [q1,q2,q3] = qes
         val gst::gss = gs
         val entry = {qe_bnds = q1, qe_nolb = q2,
                      qe_noub = q3, gs = gss, gst = gst, atoms = atoms}
       in add entry end
     else error "Need 3 theorems for qe and at least one for gs")
end;

(* theory setup *)

val setup =
  Attrib.setup @{binding langford} attribute "Langford data" #>
  Attrib.setup @{binding langfordsimp} (Attrib.add_del add_simp del_simp) "Langford simpset";

end;
