package body Wordops is

   function Rotate(I : Rotate_Amount; W : Word) return Word
   is
   begin
      return Interfaces.Rotate_Left (W, I);
   end Rotate;

end Wordops;
