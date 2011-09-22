package body Loop_Invariant
is

   procedure Proc1 (A : in Natural; B : in Word32; C : out Word32)
   is
   begin
      C := 0;
      for I in Natural range 1 .. A
        --# assert Word32 (I - 1) * B = C;
      loop
         C := C + B;
      end loop;
   end Proc1;

   procedure Proc2 (A : in Natural; B : in Word32; C : out Word32)
   is
   begin
      C := 0;
      for I in Natural range 1 .. A
        --# assert Word32 (I - 1) * B = C;
      loop
         C := C + B;
        --# assert Word32 (I) * B = C;
      end loop;
   end Proc2;

end Loop_Invariant;
