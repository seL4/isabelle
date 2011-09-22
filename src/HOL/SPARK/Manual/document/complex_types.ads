package Complex_Types
is

   type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   subtype Array_Index is Natural range 0 .. 9;

   type Array_Type1 is array (Array_Index, Day) of Integer;

   type Record_Type is
      record
         Field1 : Array_Type1;
         Field2 : Integer;
      end record;

   type Array_Type2 is array (Array_Index) of Record_Type;

   --# function Initialized
   --#   (A: Array_Type2; I : Natural) return Boolean;

   --# function Initialized2
   --#   (A: Array_Type1; I : Natural) return Boolean;

   --# function Initialized3
   --#   (A: Array_Type1; I : Natural; K : Natural) return Boolean;

end Complex_Types;
