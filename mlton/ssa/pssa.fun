(* Copyright (C) 1999-2005 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-2000 NEC Research Institute.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

functor PssaParse (S: SSA_TREE): PSSA =
struct
open S
val pssa = fn p =>
    case p of Program.T {datatypes, functions, globals, main} =>
    let
        val _ = print "PSSA\n"
        val len = List.length functions
        val _ = print ("Num of functions =" ^ (Int.toString len) ^ "\n")
    in
        p
    end

end

functor Pssa (S: SSA_TREE_STRUCTS): PSSA =
    PssaParse (SsaTree(S))