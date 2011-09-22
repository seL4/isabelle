package Loop_Invariant
is

   type Word32 is mod 2 ** 32;

   procedure Proc1 (A : in Natural; B : in Word32; C : out Word32);
   --# derives C from A, B;
   --# post Word32 (A) * B = C;

   procedure Proc2 (A : in Natural; B : in Word32; C : out Word32);
   --# derives C from A, B;
   --# post Word32 (A) * B = C;

end Loop_Invariant;
