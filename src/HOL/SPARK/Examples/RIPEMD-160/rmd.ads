with Wordops;
use type Wordops.Word;
--# inherit Wordops;

package RMD
is

   -- Types

   subtype Word is Wordops.Word;

   type Chain is
     record
        H0, H1, H2, H3, H4 : Word;
     end record;

   type Block_Index is range 0..15;
   type Block is array(Block_Index) of Word;

   type Message_Index is range 0..2**32;
   type Message is array(Message_Index range <>) of Block;

   -- Isabelle specification

   --# function rmd_hash(X : Message; L : Message_Index) return Chain;

   function Hash(X : Message) return Chain;
   --# pre X'First = 0;
   --# return rmd_hash(X, X'Last + 1);

private

   -- Types

   type Round_Index is range 0..79;

   type Chain_Pair is
      record
         Left, Right : Chain;
      end record;

   type Block_Permutation is array(Round_Index) of Block_Index;

   subtype Rotate_Amount is Wordops.Rotate_Amount;
   type Rotate_Definition is array(Round_Index) of Rotate_Amount;


   -- Isabelle proof functions

   --# function f_spec(J : Round_Index; X,Y,Z : Word) return Word;
   --# function K_l_spec(J : Round_Index) return Word;
   --# function K_r_spec(J : Round_Index) return Word;
   --# function r_l_spec(J : Round_Index) return Block_Index;
   --# function r_r_spec(J : Round_Index) return Block_Index;
   --# function s_l_spec(J : Round_Index) return Rotate_Amount;
   --# function s_r_spec(J : Round_Index) return Rotate_Amount;
   --# function steps(CS : Chain_Pair; I : Round_Index; B : Block)
   --#    return Chain_Pair;
   --# function round_spec(C : Chain; B : Block) return Chain;
   --# function rounds(C : Chain; I : Message_Index; X : Message)
   --#    return Chain;


   -- Spark Implementation

   function F(J : Round_Index; X,Y,Z : Word) return Word;
   --# return f_spec(J, X, Y, Z);

   function K_L(J : Round_Index) return Word;
   --# return K_l_spec(J);

   function K_R(J : Round_Index) return Word;
   --# return K_r_spec(J);

   function R_L(J : Round_Index) return Block_Index;
   --# return r_l_spec(J);

   function R_R(J : Round_Index) return Block_Index;
   --# return r_r_spec(J);

   function S_L(J : Round_Index) return Rotate_Amount;
   --# return s_l_spec(J);

   function S_R(J : Round_Index) return Rotate_Amount;
   --# return s_r_spec(J);

   procedure Round(CA, CB, CC, CD, CE : in out Word; X: in Block);
   --# derives CA, CB, CC, CD, CE from X, CA, CB, CC, CD, CE;
   --# post Chain'(CA, CB, CC, CD, CE) =
   --#        round_spec(Chain'(CA~, CB~, CC~, CD~, CE~), X);

end RMD;
