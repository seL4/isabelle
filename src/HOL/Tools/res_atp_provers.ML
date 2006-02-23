(*  ID:         $Id$
    Author:     Jia Meng, NICTA

Functions used for ATP Oracle.
*)


structure ResAtpProvers =

struct

fun if_proof_vampire instr = (TextIO.inputLine instr = "Refutation found. Thanks to Tanya!\n");

fun if_proof_E instr =
  let val thisLine = TextIO.inputLine instr
  in
  if thisLine = "# Proof found!\n"
  then true
  else if (thisLine = "") then false
  else if_proof_E instr end;		


local 

fun locations [] = ()
|   locations (s::ss) = (warning s; locations ss);

in 

fun call_vampire (files:string list, time: int) = 
  let val _ = locations files
      val output = (space_implode " " files) ^ "  "
      val runtime = "-t " ^ (string_of_int time)
      val vampire = ResAtp.helper_path "VAMPIRE_HOME" "vampire"
      val ch:(TextIO.instream,TextIO.outstream) Unix.proc = Unix.execute(vampire, [runtime,output])
      val (instr,outstr) = Unix.streamsOf ch
  in if_proof_vampire instr
  end;

fun call_eprover (files:string list, time:int) =
  let val _ = locations files
      val output = (space_implode " " files) ^ "  "
      val eprover = ResAtp.helper_path "E_HOME" "/PROVER/eprover"
      val runtime = "--cpu-limit=" ^ (string_of_int time)
      val ch:(TextIO.instream,TextIO.outstream) Unix.proc = Unix.execute(eprover, [runtime,"--tptp-format","-tAuto","-xAuto",output])
      val (instr,outstr) = Unix.streamsOf ch
  in if_proof_E instr
  end; 

end

fun vampire_o thy ((helper,files),time) = (if (call_vampire (helper @ files,time)) then (warning (hd files); ResAtpSetup.cond_rm_tmp files;HOLogic.mk_Trueprop HOLogic.false_const)  
  else (ResAtpSetup.cond_rm_tmp files;raise Fail ("vampire oracle failed")));


fun eprover_o thy ((helper,files),time) = (if (call_eprover (helper @ files,time)) then (warning (hd files); ResAtpSetup.cond_rm_tmp files;HOLogic.mk_Trueprop HOLogic.false_const)
  else (ResAtpSetup.cond_rm_tmp files;raise Fail ("eprover oracle failed")));

end;

