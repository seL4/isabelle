structure Codegen = 
struct

val arbitrary_option : 'a option = NONE;

fun dummy_option [] = arbitrary_option
  | dummy_option (x :: xs) = SOME x;

end; (*struct Codegen*)
