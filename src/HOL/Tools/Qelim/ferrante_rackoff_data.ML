(* Title:      HOL/Tools/Qelim/ferrante_rackoff_data.ML
   ID:         $Id$
   Author:     Amine Chaieb, TU Muenchen

Context data for Ferrante and Rackoff's algorithm for quantifier
elimination in dense linear orders.
*)

signature FERRANTE_RACKOF_DATA =
sig
  datatype ord = Lt | Le | Gt | Ge | Eq | NEq | Nox
  type entry
  val get: Proof.context -> (thm * entry) list
  val del: attribute
  val add: entry -> attribute 
  val funs: thm -> 
    {isolate_conv: morphism -> Proof.context -> cterm list -> cterm -> thm,
     whatis: morphism -> cterm -> cterm -> ord,
     simpset: morphism -> simpset} -> declaration
  val match: Proof.context -> cterm -> entry option
  val setup: theory -> theory
end;

structure Ferrante_Rackoff_Data: FERRANTE_RACKOF_DATA = 
struct

(* data *)

datatype ord = Lt | Le | Gt | Ge | Eq | NEq | Nox

type entry = 
  {minf: thm list, pinf: thm list, nmi: thm list, npi: thm list,  
   ld: thm list, qe: thm, atoms : cterm list} *
   {isolate_conv: Proof.context -> cterm list -> cterm -> thm, 
    whatis : cterm -> cterm -> ord, 
    simpset : simpset};

val eq_key = Thm.eq_thm;
fun eq_data arg = eq_fst eq_key arg;

structure Data = Generic_Data
(
  type T = (thm * entry) list;
  val empty = [];
  val extend = I;
  fun merge data : T = AList.merge eq_key (K true) data;
);

val get = Data.get o Context.Proof;

fun del_data key = remove eq_data (key, []);

val del = Thm.declaration_attribute (Data.map o del_data);

fun undefined x = error "undefined";

fun add entry = 
    Thm.declaration_attribute (fn key => fn context => context |> Data.map 
      (del_data key #> cons (key, entry)));


(* extra-logical functions *)

fun funs raw_key {isolate_conv = icv, whatis = wi, simpset = ss} phi = Data.map (fn data =>
  let
    val key = Morphism.thm phi raw_key;
    val _ = AList.defined eq_key data key orelse
      raise THM ("No data entry for structure key", 0, [key]);
    val fns = {isolate_conv = icv phi, whatis = wi phi, simpset = ss phi};
  in AList.map_entry eq_key key (apsnd (K fns)) data end);

fun match ctxt tm =
  let
    fun match_inst
        ({minf, pinf, nmi, npi, ld, qe, atoms},
         fns as {isolate_conv, whatis, simpset}) pat =
       let
        fun h instT =
          let
            val substT = Thm.instantiate (instT, []);
            val substT_cterm = Drule.cterm_rule substT;

            val minf' = map substT minf
            val pinf' = map substT pinf
            val nmi' = map substT nmi
            val npi' = map substT npi
            val ld' = map substT ld
            val qe' = substT qe
            val atoms' = map substT_cterm atoms
            val result = ({minf = minf', pinf = pinf', nmi = nmi', npi = npi', 
                           ld = ld', qe = qe', atoms = atoms'}, fns)
          in SOME result end
      in (case try Thm.match (pat, tm) of
           NONE => NONE
         | SOME (instT, _) => h instT)
      end;

    fun match_struct (_,
        entry as ({atoms = atoms, ...}, _): entry) =
      get_first (match_inst entry) atoms;
  in get_first match_struct (get ctxt) end;


(* concrete syntax *)

local
val minfN = "minf";
val pinfN = "pinf";
val nmiN = "nmi";
val npiN = "npi";
val lin_denseN = "lindense";
val qeN = "qe"
val atomsN = "atoms"
val simpsN = "simps"
fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
val any_keyword =
  keyword minfN || keyword pinfN || keyword nmiN 
|| keyword npiN || keyword lin_denseN || keyword qeN 
|| keyword atomsN || keyword simpsN;

val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map Drule.dest_term;
in

val ferrak_setup =
  Attrib.setup @{binding ferrack}
    ((keyword minfN |-- thms)
     -- (keyword pinfN |-- thms)
     -- (keyword nmiN |-- thms)
     -- (keyword npiN |-- thms)
     -- (keyword lin_denseN |-- thms)
     -- (keyword qeN |-- thms)
     -- (keyword atomsN |-- terms) >>
       (fn ((((((minf,pinf),nmi),npi),lin_dense),qe), atoms)=> 
       if length qe = 1 then
         add ({minf = minf, pinf = pinf, nmi = nmi, npi = npi, ld = lin_dense, 
              qe = hd qe, atoms = atoms},
             {isolate_conv = undefined, whatis = undefined, simpset = HOL_ss})
       else error "only one theorem for qe!"))
    "Ferrante Rackoff data";

end;


(* theory setup *)

val setup = ferrak_setup;

end;
