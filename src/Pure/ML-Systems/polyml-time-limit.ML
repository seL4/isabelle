(*  Title:      Pure/ML-Systems/polyml-time-limit.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2004

Bounded time execution (similar to SML/NJ's TimeLimit structure) for Poly/ML.
*)

structure TimeLimit : sig
	exception TimeOut
	val timeLimit : Time.time -> ('a -> 'b) -> 'a -> 'b
end = struct

	exception TimeOut

	fun timeLimit t f x =
	let
		datatype ('a, 'b) union =
			INL of 'a | INR of 'b
		val result = Process.channel ()
		fun workerThread () =
			Process.send (result, SOME (INL (f x) handle exn => INR exn))
		val interrupt = Process.console workerThread
		val old_handle = Signal.signal (Posix.Signal.alrm, Signal.SIG_HANDLE
			(fn _ => ((Process.send (result, NONE)) before (interrupt ()))))
	in
		Posix.Process.alarm t;
		case Process.receive result of
		  SOME (INL fx)  => (Posix.Process.alarm Time.zeroTime; Signal.signal (Posix.Signal.alrm, old_handle); fx)
		| SOME (INR exn) => (Posix.Process.alarm Time.zeroTime; Signal.signal (Posix.Signal.alrm, old_handle); raise exn)
		| NONE           => (Signal.signal (Posix.Signal.alrm, old_handle); raise TimeOut)
	end

end;
