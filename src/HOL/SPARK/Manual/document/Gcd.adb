package body Greatest_Common_Divisor
is

   procedure G_C_D(M, N: in Natural; G: out Natural)
   is
      C, D, R: Integer;
   begin
      C := M; D := N;
      while D /= 0 loop
         --# assert C >= 0 and D > 0 and Gcd(C, D) = Gcd(M, N);
         R := C rem D;
         C := D; D := R;
      end loop;
      G := C;
   end G_C_D;

end Greatest_Common_Divisor;
