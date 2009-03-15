(*  Title:      HOL/Tools/Qelim/cooper_data.ML
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

signature COOPER_DATA =
sig
  type entry
  val get: Proof.context -> entry
  val del: term list -> attribute
  val add: term list -> attribute 
  val setup: theory -> theory
end;

structure CooperData : COOPER_DATA =
struct

type entry = simpset * (term list);
val start_ss = HOL_ss (* addsimps @{thms "Groebner_Basis.comp_arith"}
               addcongs [if_weak_cong, @{thm "let_weak_cong"}];*)
val allowed_consts = 
  [@{term "op + :: int => _"}, @{term "op + :: nat => _"},
   @{term "op - :: int => _"}, @{term "op - :: nat => _"},
   @{term "op * :: int => _"}, @{term "op * :: nat => _"},
   @{term "op div :: int => _"}, @{term "op div :: nat => _"},
   @{term "op mod :: int => _"}, @{term "op mod :: nat => _"},
   @{term "Int.Bit0"}, @{term "Int.Bit1"},
   @{term "op &"}, @{term "op |"}, @{term "op -->"}, 
   @{term "op = :: int => _"}, @{term "op = :: nat => _"}, @{term "op = :: bool => _"},
   @{term "op < :: int => _"}, @{term "op < :: nat => _"},
   @{term "op <= :: int => _"}, @{term "op <= :: nat => _"},
   @{term "op dvd :: int => _"}, @{term "op dvd :: nat => _"},
   @{term "abs :: int => _"},
   @{term "max :: int => _"}, @{term "max :: nat => _"},
   @{term "min :: int => _"}, @{term "min :: nat => _"},
   @{term "HOL.uminus :: int => _"}, (*@ {term "HOL.uminus :: nat => _"},*)
   @{term "Not"}, @{term "Suc"},
   @{term "Ex :: (int => _) => _"}, @{term "Ex :: (nat => _) => _"},
   @{term "All :: (int => _) => _"}, @{term "All :: (nat => _) => _"},
   @{term "nat"}, @{term "int"},
   @{term "Int.Bit0"}, @{term "Int.Bit1"},
   @{term "Int.Pls"}, @{term "Int.Min"},
   @{term "Int.number_of :: int => int"}, @{term "Int.number_of :: int => nat"},
   @{term "0::int"}, @{term "1::int"}, @{term "0::nat"}, @{term "1::nat"},
   @{term "True"}, @{term "False"}];

structure Data = GenericDataFun
(
  type T = simpset * (term list);
  val empty = (start_ss, allowed_consts);
  val extend  = I;
  fun merge _ ((ss1, ts1), (ss2, ts2)) =
    (merge_ss (ss1, ss2), Library.merge (op aconv) (ts1, ts2));
);

val get = Data.get o Context.Proof;

fun add ts = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (fn (ss,ts') => 
     (ss addsimps [th], merge (op aconv) (ts',ts) ))) 

fun del ts = Thm.declaration_attribute (fn th => fn context => 
  context |> Data.map (fn (ss,ts') => 
     (ss delsimps [th], subtract (op aconv) ts' ts ))) 


(* concrete syntax *)

local
fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();

val constsN = "consts";
val any_keyword = keyword constsN
val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
val terms = thms >> map (term_of o Drule.dest_term);

fun optional scan = Scan.optional scan [];

in
val attribute =
 (Scan.lift (Args.$$$ "del") |-- optional (keyword constsN |-- terms)) >> del ||
  optional (keyword constsN |-- terms) >> add
end;


(* theory setup *)

val setup = Attrib.setup @{binding presburger} attribute "Cooper data";

end;
