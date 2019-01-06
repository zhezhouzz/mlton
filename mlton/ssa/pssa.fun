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
        val expvar_l = Vector.foldr (globals, [], (fn (stat, r) =>
            case (Statement.exp stat) of
              Exp.Const expvar =>
                let val expvar_str = Const.toString expvar
                    (* val _ = print (expvar_str ^ "\n") *) in
                (if String.compare (expvar_str, "\"PSSACOMPRE\"") = EQUAL then
                    let val _ = print "Got:\n" in
                    (case (Statement.var stat) of
                      SOME var =>
                          let val _ = print ("Got :" ^ (Var.toString var) ^ "\n") in       
                          (Var.toString var) :: r end
                    | NONE => r) end
                else
                    r)
                end
            | _ => r
        ))
        val _ = print ("num of PSSA = " ^ (Int.toString (List.length expvar_l)) ^ "\n")
        val expvar_l_str = List.foldr (expvar_l, "", (fn (v,r) => v ^ " " ^ r))
        val _ = print ("PSSA in Label:" ^ expvar_l_str ^ "\n")
        val _ = Program.dfs (p,
            (fn f =>
            let
                val _ = () (* print (Func.toString (Function.name f)) *)
            in
                fn () => ()
            end
            )
        )
    in
        p
    end

end

functor Pssa (S: SSA_TREE_STRUCTS): PSSA =
    PssaParse (SsaTree(S))