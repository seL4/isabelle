(*<*)
theory a5 = Main:
(*>*)

subsection {*BIGNAT - Specification and Verification*};

text{*
Hardware platforms have a limit on the largest number they can represent. This is normally fixed by the bit lengths of registers and ALUs used. In order to be able to perform calculations that require arbitrarily large numbers, the provided arithmetic operations need to be extended in order for them to work on an abstract data type representing numbers of arbitrary size.

In this exercise we will build and verify an implementation for BIGNAT, an abstract data type representing natural numbers of arbitrary size.
*}

text {*\subsubsection*{Representation}*}

text{*
A BIGNAT is represented as a list of natural numbers in a range supported by the target machine. In our case, this will be all natural numbers in the range [0, BASE-1]. (Note: natural numbers in Isabelle are of arbitrary size)
*}

types 
  bigNat = "nat list"

text{*
Define a function @{term "valid"} that takes a value for BASE, and checks if the given BIGNAT is valid.
*}

consts valid :: "nat \<Rightarrow> bigNat \<Rightarrow> bool"

text{*
Define a function @{term "val"} that takes a BIGNAT and its corresponding BASE, and returns the natural number represented by it. *}

consts val :: "nat \<Rightarrow> bigNat \<Rightarrow> nat"

text {*\subsubsection*{Addition}*}

text{*
Define a function @{term "add"} that adds two BIGNATs with the same value for BASE. Make sure that your algorithm preserves the validity of the BIGNAT representation.
*}

consts add :: "nat \<Rightarrow> bigNat \<Rightarrow> bigNat \<Rightarrow> bigNat"

text{*
Using @{term "val"}, verify formally that your function @{term "add"} computes the sum of two BIGNATs correctly.*}

text{*
Using @{term "valid"}, verify formally that your function @{term "add"} preserves the validity of the BIGNAT representation.*}


text {*
\subsubsection*{Multiplication}*}

text{*
Define a function @{term "mult"} that multiplies two BIGNATs with the same value for BASE. You may use @{term "add"}, but not so often as to make the solution trivial. Make sure that your algorithm preserves the validity of the BIGNAT representation.
*}
consts mult :: "nat \<Rightarrow> bigNat \<Rightarrow> bigNat \<Rightarrow> bigNat"
text{*
Using @{term "val"}, verify formally that your function @{term "mult"} computes the product of two BIGNATs correctly.*}

text{*
Using @{term "valid"}, verify formally that your function @{term "mult"} preserves the validity of the BIGNAT representation.*}


(*<*) end (*>*)




