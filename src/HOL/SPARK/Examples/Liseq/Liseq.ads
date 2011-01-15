-------------------------------------------------------------------------------
-- Longest increasing subsequence of an array of integers
-------------------------------------------------------------------------------

package Liseq is

   type Vector is array (Integer range <>) of Integer;

   --# function Liseq_prfx(A: Vector; i: Integer) return Integer;
   --# function Liseq_ends_at(A: Vector; i: Integer) return Integer;
   --# function Max_ext(A: Vector; i, j: Integer) return Integer;

   procedure Liseq_length(A: in Vector; L: in out Vector; maxi: out Integer);
   --# derives maxi, L from A, L;
   --# pre A'First = 0 and L'First = 0 and A'Last = L'Last and A'Last < Integer'Last;
   --# post maxi = Liseq_prfx (A, A'Last+1);

end Liseq;
