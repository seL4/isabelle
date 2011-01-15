package body RMD is



   function F(J : Round_Index; X,Y,Z : Word) return Word
   is
      Result: Word;
   begin
      if     0 <= J and J <= 15 then Result := X xor Y xor Z;
      elsif 16 <= J and J <= 31 then Result := (X and Y) or (not X and Z);
      elsif 32 <= J and J <= 47 then Result := (X or not Y) xor Z;
      elsif 48 <= J and J <= 63 then Result := (X and Z) or (Y and not Z);
      else                           Result := X xor (Y or not Z);
      end if;
      return Result;
   end F;



   function K_L(J : Round_Index) return Word
   is
      K: Word;
   begin
      if     0 <= J and J <= 15 then K := 16#0000_0000#;
      elsif 16 <= J and J <= 31 then K := 16#5A82_7999#;
      elsif 32 <= J and J <= 47 then K := 16#6ED9_EBA1#;
      elsif 48 <= J and J <= 63 then K := 16#8F1B_BCDC#;
      else                           K := 16#A953_FD4E#;
      end if;
      return K;
   end K_L;


   function K_R(J : Round_Index) return Word
   is
      K: Word;
   begin
      if     0 <= J and J <= 15 then K := 16#50A2_8BE6#;
      elsif 16 <= J and J <= 31 then K := 16#5C4D_D124#;
      elsif 32 <= J and J <= 47 then K := 16#6D70_3EF3#;
      elsif 48 <= J and J <= 63 then K := 16#7A6D_76E9#;
      else                           K := 16#0000_0000#;
      end if;
      return K;
   end K_R;



   function R_L(J : Round_Index) return Block_Index
   is
      R_Values : constant Block_Permutation := Block_Permutation'
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
         7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
         3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
         1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
         4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13);
      --# for R_Values declare rule;
   begin
      return R_Values(J);
   end R_L;


   function R_R(J : Round_Index) return Block_Index
   is
      R_Values : constant Block_Permutation := Block_Permutation'
        (5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
         6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
         15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
         8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
         12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11);
      --# for R_Values declare rule;
   begin
      return R_Values(J);
   end R_R;


   function S_L(J : Round_Index) return Rotate_Amount
   is
      S_Values : constant Rotate_Definition := Rotate_Definition'
        (11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
         7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
         11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
         11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
         9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6);
      --# for S_Values declare rule;
   begin
      return S_Values(J);
   end S_L;


   function S_R(J : Round_Index) return Rotate_Amount
   is
      S_Values : constant Rotate_Definition := Rotate_Definition'
        (8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
         9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
         9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
         15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
         8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11);
      --# for S_Values declare rule;
   begin
      return S_Values(J);
   end S_R;



   procedure Round(CA, CB, CC, CD, CE : in out Word; X : in Block)
   is
      CLA, CLB, CLC, CLD, CLE, CRA, CRB, CRC, CRD, CRE : Word;
      T : Word;
   begin
      CLA := CA;
      CLB := CB;
      CLC := CC;
      CLD := CD;
      CLE := CE;
      CRA := CA;
      CRB := CB;
      CRC := CC;
      CRD := CD;
      CRE := CE;
      for J in Round_Index range 0..79
      loop
         -- left
         T := Wordops.Rotate(S_L(J),
                             CLA +
                               F(J, CLB, CLC, CLD) +
                               X(R_L(J)) +
                               K_L(J)) +
           CLE;
         CLA := CLE;
         CLE := CLD;
         CLD := Wordops.Rotate(10, CLC);
         CLC := CLB;
         CLB := T;
         -- right
         T := Wordops.Rotate(S_R(J),
                             CRA +
                               F(79 - J, CRB, CRC, CRD) +
                               X(R_R(J)) +
                               K_R(J)) +
           CRE;
         CRA := CRE;
         CRE := CRD;
         CRD := Wordops.Rotate(10, CRC);
         CRC := CRB;
         CRB := T;
         --# assert Chain_Pair'(Chain'(CLA, CLB, CLC, CLD, CLE),
         --#                    Chain'(CRA, CRB, CRC, CRD, CRE)) =
         --#   steps(Chain_Pair'(Chain'(CA~, CB~, CC~, CD~, CE~),
         --#                    Chain'(CA~, CB~, CC~, CD~, CE~)), J + 1, X)
         --# and CA = CA~ and CB = CB~ and CC = CC~ and CD = CD~ and CE = CE~;
      end loop;
      T    := CB + CLC + CRD;
      CB := CC + CLD + CRE;
      CC := CD + CLE + CRA;
      CD := CE + CLA + CRB;
      CE := CA + CLB + CRC;
      CA := T;
   end Round;

   function Hash(X : Message) return Chain
   is
      CA_Init : constant Word := 16#6745_2301#;
      CB_Init : constant Word := 16#EFCD_AB89#;
      CC_Init : constant Word := 16#98BA_DCFE#;
      CD_Init : constant Word := 16#1032_5476#;
      CE_Init : constant Word := 16#C3D2_E1F0#;
      CA, CB, CC, CD, CE : Word;
   begin
      CA := CA_Init;
      CB := CB_Init;
      CC := CC_Init;
      CD := CD_Init;
      CE := CE_Init;
      for I in Message_Index range X'First..X'Last
      loop
         Round(CA, CB, CC, CD, CE, X(I));
         --# assert Chain'(CA, CB, CC, CD, CE) = rounds(
         --#    Chain'(CA_Init, CB_Init, CC_Init, CD_Init, CE_Init),
         --#    I + 1,
         --#    X);
      end loop;
      return Chain'(CA, CB, CC, CD, CE);
   end Hash;

end RMD;

