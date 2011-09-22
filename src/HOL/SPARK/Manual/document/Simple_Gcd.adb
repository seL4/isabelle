package body Simple_Greatest_Common_Divisor
is

   procedure G_C_D (M, N : in Natural; G : out Natural)
   is
      C, D, R : Natural;
   begin
      C := M; D := N;
      while D /= 0
        --# assert Gcd (C, D) = Gcd (M, N);
      loop
         R := C mod D;
         C := D; D := R;
      end loop;
      G := C;
   end G_C_D;

end Simple_Greatest_Common_Divisor;
