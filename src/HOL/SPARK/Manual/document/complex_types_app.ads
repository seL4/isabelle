with Complex_Types;
--# inherit Complex_Types;

package Complex_Types_App
is

   procedure Initialize (A : in out Complex_Types.Array_Type2);
   --# derives A from A;
   --# post Complex_Types.Initialized (A, 10);

end Complex_Types_App;
