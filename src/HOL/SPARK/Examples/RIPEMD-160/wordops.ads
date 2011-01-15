
with Interfaces;
--# inherit Interfaces;

package WordOps is

   subtype Word is Interfaces.Unsigned_32;

   subtype Rotate_Amount is Integer range 0..15;

   --# function rotate_left(I : Rotate_Amount; W : Word) return Word;

   function Rotate(I : Rotate_Amount; W : Word) return Word;
   --# return rotate_left(I, W);
   --# accept W, 3, "Expecting this warning";
   pragma Inline (Rotate);
   --# end accept;

end Wordops;
