signature IMPORT_PACKAGE =
sig
    val import_meth: Args.src -> Proof.context -> Proof.method
    val setup      : (theory -> theory) list
    val debug      : bool ref
end

structure ImportPackage :> IMPORT_PACKAGE =
struct

val debug = ref false
fun message s = if !debug then writeln s else ()

val string_of_thm = Library.setmp print_mode [] string_of_thm
val string_of_cterm = Library.setmp print_mode [] string_of_cterm

fun import_tac (thyname,thmname) =
    if !SkipProof.quick_and_dirty
    then SkipProof.cheat_tac
    else
     fn thy =>
     fn th =>
	let
	    val sg = sign_of_thm th
	    val prem = hd (prems_of th)
	    val _ = message ("Import trying to prove " ^ (string_of_cterm (cterm_of sg prem)))
	    val int_thms = fst (Replay.setup_int_thms thyname thy)
	    val proof = snd (ProofKernel.import_proof thyname thmname thy) thy
	    val hol4thm = snd (Replay.replay_proof int_thms thyname thmname proof thy)
	    val thm = snd (ProofKernel.to_isa_thm hol4thm)
	    val rew = ProofKernel.rewrite_hol4_term (concl_of thm) thy
	    val thm = equal_elim rew thm
	    val prew = ProofKernel.rewrite_hol4_term prem thy
	    val prem' = #2 (Logic.dest_equals (prop_of prew))
	    val _ = message ("Import proved " ^ (string_of_thm thm))  
	in
	    case Shuffler.set_prop thy prem' [("",thm)] of
		Some (_,thm) =>
		let
		    val _ = if prem' aconv (prop_of thm)
			    then message "import: Terms match up"
			    else message "import: Terms DO NOT match up"
		    val thm' = equal_elim (symmetric prew) thm
		    val res = bicompose true (false,thm',0) 1 th
		in
		    res
		end
	      | None => (message "import: set_prop didn't succeed"; no_tac th)
	end
	
val import_meth = Method.simple_args (Args.name -- Args.name)
		  (fn arg =>
		   fn ctxt =>
		      let
			  val thy = ProofContext.theory_of ctxt
		      in
			  Method.SIMPLE_METHOD (import_tac arg thy)
		      end)

val setup = [Method.add_method("import",import_meth,"Import HOL4 theorem")]
end
