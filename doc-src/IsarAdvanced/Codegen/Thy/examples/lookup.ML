structure ROOT = 
struct

structure Codegen = 
struct

fun lookup ((k, v) :: xs) l =
  (if ((k : string) = l) then SOME v else lookup xs l);

end; (*struct Codegen*)

end; (*struct ROOT*)
