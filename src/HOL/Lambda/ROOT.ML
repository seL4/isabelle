(*  Title: 	HOL/Lambda/ROOT.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Confluence proof for untyped lambda-calculus using de Bruijn's notation.
Covers beta, eta, and beta+eta.

Beta is proved confluent both in the traditional way and also following the
first two pages of

@article{Takahashi-IC-95,author="Masako Takahashi",
title="Parallel Reductions in $\lambda$-Calculus",
journal=IC,year=1995,volume=118,pages="120--127"}

*)

HOL_build_completed;	(*Make examples fail if HOL did*)

writeln"Root file for HOL/Lambda";
loadpath := [".","Lambda"];

time_use_thy "Eta";

make_chart ();   (*make HTML chart*)
