(*---------------------------------------------------------------------------
 * This structure is intended to shield TFL from any constructors already 
 * declared in the environment. In the Isabelle port, for example, there
 * was already a datatype with "|->" being a constructor. In TFL we were
 * trying to define a function "|->", but it failed in PolyML (which conforms
 * better to the Standard) while the definition was accepted in NJ/SML
 * (which doesn't always conform so well to the standard).
 *---------------------------------------------------------------------------*)

structure Mask : Mask_sig =
struct

 datatype 'a binding = |-> of ('a * 'a)   (* infix 7 |->; *)

 datatype mask = ERR 
end;
