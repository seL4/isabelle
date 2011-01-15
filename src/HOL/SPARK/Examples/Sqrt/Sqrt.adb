package body Sqrt is

   function Isqrt(N: Natural) return Natural
   is
     R: Natural;
   begin
      R := 0;
      loop
         --# assert R * R <= N;
         exit when N - R * R < 2 * R + 1;
         R := R + 1;
      end loop;
      return R;
   end Isqrt;

end Sqrt;
