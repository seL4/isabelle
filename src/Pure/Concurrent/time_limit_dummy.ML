(*  Title:      Pure/Concurrent/time_limit_dummy.ML
    Author:     Makarius

Execution with time limit -- dummy version.
*)

structure TimeLimit: TIME_LIMIT =
struct

exception TimeOut;

fun timeLimit _ f x = (warning "No timeout support on this ML platform"; f x);

end;

