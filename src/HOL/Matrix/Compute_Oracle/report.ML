structure Report =
struct

local

    val report_depth = Unsynchronized.ref 0
    fun space n = if n <= 0 then "" else (space (n-1))^" "
    fun report_space () = space (!report_depth)

in

fun timeit f =
    let
        val t1 = Timing.start ()
        val x = f ()
        val t2 = Timing.message (Timing.result t1)
        val _ = writeln ((report_space ()) ^ "--> "^t2)
    in
        x       
    end

fun report s f = 
let
    val _ = writeln ((report_space ())^s)
    val _ = report_depth := !report_depth + 1
    val x = timeit f
    val _ = report_depth := !report_depth - 1
in
    x
end

end
end