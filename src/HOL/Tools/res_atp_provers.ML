(*  ID:         $Id$
    Author:     Jia Meng, NICTA

Functions used for ATP Oracle.
*)


structure ResAtpProvers =

struct

fun if_proof_vampire instr = (TextIO.inputLine instr = "Refutation found. Thanks to Tanya!\n");

fun if_proof_E instr =
  let val thisLine = TextIO.inputLine instr
  in thisLine <> "" andalso 
     (thisLine = "# Proof found!\n" orelse if_proof_E instr) 
  end;

fun if_proof_spass instr = 
    let val thisLine = TextIO.inputLine instr
    in thisLine <> "" andalso 
       (thisLine = "SPASS beiseite: Proof found.\n" orelse if_proof_spass instr) 
    end;

local 

fun location s = warning ("ATP input at: " ^ s);

in 

fun call_vampire (file:string, time: int) = 
  let val _ = location file
      val runtime = "-t " ^ (string_of_int time)
      val vampire = ResAtp.helper_path "VAMPIRE_HOME" "vampire"
      val ch:(TextIO.instream,TextIO.outstream) Unix.proc = 
          Unix.execute(vampire, [runtime,file])
      val (instr,outstr) = Unix.streamsOf ch
  in if_proof_vampire instr
  end;

fun call_eprover (file:string, time:int) =
  let val _ = location file
      val eprover = ResAtp.helper_path "E_HOME" "/PROVER/eprover"
      val runtime = "--cpu-limit=" ^ (string_of_int time)
      val ch:(TextIO.instream,TextIO.outstream) Unix.proc = 
          Unix.execute(eprover, [runtime,"--tptp-format","-tAuto","-xAuto",file])
      val (instr,outstr) = Unix.streamsOf ch
  in if_proof_E instr
  end; 

fun call_spass (file:string, time:int) =
    let val _ = location file
	val runtime = "-TimeLimit=" ^ (string_of_int time)
	val spass = ResAtp.helper_path "SPASS_HOME" "SPASS"
	val ch:(TextIO.instream,TextIO.outstream) Unix.proc =
	    Unix.execute(spass, [runtime,"-Splits=0", "-FullRed=0", "-SOS=1",file])
	val (instr,outstr) = Unix.streamsOf ch
    in if_proof_spass instr
    end;


end

fun vampire_o _ (file,time) = 
  if call_vampire (file,time) 
  then (warning file; ResAtp.cond_rm_tmp file; HOLogic.mk_Trueprop HOLogic.false_const)  
  else (ResAtp.cond_rm_tmp file; raise Fail ("vampire oracle failed"));

fun eprover_o _ (file,time) = 
  if call_eprover (file,time) 
  then (warning file; ResAtp.cond_rm_tmp file; HOLogic.mk_Trueprop HOLogic.false_const)
  else (ResAtp.cond_rm_tmp file; raise Fail ("eprover oracle failed"));

fun spass_o _ (file,time) =
    if call_spass (file,time)
    then (warning file; ResAtp.cond_rm_tmp file; HOLogic.mk_Trueprop HOLogic.false_const)
    else (ResAtp.cond_rm_tmp file; raise Fail ("SPASS oracle failed"));


end;

