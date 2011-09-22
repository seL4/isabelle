package body Complex_Types_App
is

   procedure Initialize (A : in out Complex_Types.Array_Type2)
   is
   begin
      for I in Complex_Types.Array_Index
        --# assert Complex_Types.Initialized (A, I);
      loop
         for J in Complex_Types.Array_Index
           --# assert
           --#   Complex_Types.Initialized (A, I) and
           --#   Complex_Types.Initialized2 (A (I).Field1, J);
         loop
            for K in Complex_Types.Day
              --# assert
              --#   Complex_Types.Initialized (A, I) and
              --#   Complex_Types.Initialized2 (A (I).Field1, J) and
              --#   Complex_Types.Initialized3
              --#     (A (I).Field1, J, Complex_Types.Day'Pos (K));
            loop
               A (I).Field1 (J, K) := 0;
            end loop;
         end loop;
         A (I).Field2 := 0;
      end loop;
   end Initialize;

end Complex_Types_App;
