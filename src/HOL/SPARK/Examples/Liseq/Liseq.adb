-------------------------------------------------------------------------------
-- Longest increasing subsequence of an array of integers
-------------------------------------------------------------------------------

package body Liseq is

   procedure Liseq_length(A: in Vector; L: in out Vector; maxi: out Integer)
   is
      maxj,i,j,pmax : Integer;
   begin
      L(0) := 1;
      pmax := 0;
      maxi := 1;
      i := 1;
      while i <= L'Last
        --# assert
        --#   (for all i2 in Integer range 0 .. i-1 =>
        --#      (L(i2) = Liseq_ends_at(A, i2))) and
        --#   L(pmax) = maxi and L(pmax) = Liseq_prfx(A, i) and
        --#   0 <= i and i <= L'Last+1 and 0 <= pmax and pmax < i and
        --#   A'First = 0 and L'First = 0 and A'Last = L'Last and A'Last < Integer'Last;
      loop
         if A(i) < A(pmax) then
            maxj := 0;
            j := 0;
            while j < i
              --# assert
              --#  (for all i2 in Integer range 0 .. i-1 =>
              --#     (L(i2) = Liseq_ends_at(A, i2))) and
              --#  L(pmax) = maxi and L(pmax) = Liseq_prfx(A, I) and
              --#  0 <= i and i <= L'Last and 0 <= pmax and pmax < i and
              --#  0 <= j and j <= i and
              --#  maxj = Max_ext (A, i, j) and
              --#  A'First = 0 and L'First = 0 and A'Last = L'Last and A'Last < Integer'Last;
            loop
               if (A(j) <= A(i) and
                     maxj < L(j)) then
                  maxj := L(j);
               end if;
               j := j+1;
            end loop;
            L(i) := maxj+1;
            if L(i) > maxi then
               maxi := maxi+1;
               pmax := i;
            end if;
         else
            maxi := maxi+1;
            L(i) := maxi;
            pmax := i;
         end if;
         i := i+1;
      end loop;
   end Liseq_length;
end Liseq;
