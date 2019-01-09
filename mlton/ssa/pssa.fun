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

fun vec_in_list vec l =
    Vector.foldr (
        vec, false, (fn (vece, r) =>
                        r orelse (
                            List.foldr (
                                l, false, (fn (le, r) =>
                                              r orelse (Var.equals (vece, le))
                                          )
                            )
                        )
                    )
    )

fun print_prim_block b =
    let
        val _ = print "New Block:\n"
        val stats = Block.statements b
        val _ = print ("stats num = " ^ (Int.toString (Vector.length stats)) ^ "\n")
        val _ = Vector.foreach (
                stats, (fn stat =>
                           case stat of
                               Statement.T {exp, ty, var} =>
                               case exp of
                                   Exp.PrimApp {args, prim, targs} =>
                                   let
                                       val name = Prim.Name.toString (Prim.name prim)
                                       val _ = print ("Prim: " ^ name ^ "\n")
                                   in
                                       ()
                                   end
                                 | _ => ()
                       )
            )
    in
        ()
    end

fun find_thread_block b =
    let
        val stats = Block.statements b
        val result = Vector.foldr (
                stats, false, (fn (stat, r) =>
                           case stat of
                               Statement.T {exp, ty, var} =>
                               case exp of
                                   Exp.PrimApp {args, prim, targs} =>
                                   let
                                       val name = Prim.Name.toString (Prim.name prim)
                                       val _ = print ("Prim: " ^ name ^ "\n")
                                       val if_thread = String.compare (name, "Thread_atomicBegin") = EQUAL
                                       val _ = if if_thread
                                               then
                                                   print_prim_block b
                                               else
                                                   ()
                                   in
                                       if if_thread then true else r
                                   end
                                 | _ => r
                              )
            )
    in
        result
    end



fun fold_prim_block f r b =
    let
        val stats = Block.statements b
        val r' = Vector.foldr (
                stats, r, (fn (stat, result) =>
                           case stat of
                               Statement.T {exp, ty, var} =>
                               case exp of
                                   Exp.PrimApp {args, prim, targs} =>
                                   f (result, prim)
                                 | _ => result
                          )
            )
    in
        r'
    end


fun print_prim f =
    Function.dfs (
        f, (fn b =>
               let
                   val _ = print_prim_block b
                   val _ = print "============\n"
                   val if_thread = find_thread_block b
                   val _ = if if_thread then print "<<<<<<======FOLDTHREAD======>>>>>>\n" else ()
               in
                   fn () => ()
               end
           )
    )


fun labelBlock f label =
    let
        val {graph, labelNode, nodeBlock} = Function.controlFlow f
    in
        nodeBlock (labelNode label)
    end

fun block_normal_next f b =
    let
        val trans = Block.transfer b
        val next = case trans of
                       Transfer.Case {cases, default, ...} =>
                       let
                           val label_l = case default of
                                              SOME lab => [lab]
                                            | NONE => []
                           val caselab_l = case cases of
                                               Cases.Con vec =>
                                               Vector.foldr (
                                                   vec, [], (fn ((c, lab), r) =>
                                                                lab :: r
                                                            )
                                               )
                                             | Cases.Word (w, vec) =>
                                               Vector.foldr (
                                                   vec, [], (fn ((w, lab), r) =>
                                                                lab :: r
                                                            )
                                               )
                                                            val lab_l = label_l @ caselab_l
                       in
                           lab_l
                       end
                     | Transfer.Goto {args, dst} => [dst]
                     | _ => []
    in
        next
    end

fun block_dfs f lab r v control =
    let
        val {blocks, start, ...} = Function.dest f
        val numBlocks = Vector.length blocks
        val {get = labelIndex, set = setLabelIndex, rem, ...} =
            Property.getSetOnce (Label.plist,
                                 Property.initRaise ("index", Label.layout))
        val _ = Vector.foreachi (blocks, fn (i, Block.T {label, ...}) =>
                                            setLabelIndex (label, i))
        val visited = Array.array (numBlocks, false)
        fun visit r (l: Label.t) =
            let
                val i = labelIndex l
            in
                if Array.sub (visited, i)
                then ()
                else
                    let
                        val _ = Array.update (visited, i, true)
                        val b as Block.T {transfer, ...} =
                            Vector.sub (blocks, i)
                        val r' = v (r, b)
                    in
                        if control b
                        then
                            ()
                        else
                            let
                                val next = block_normal_next f b
                                val r = List.foldr (
                                        next, r', (fn (lab, r) =>
                                                      visit r lab
                                                  )
                                    )
                            in
                                r
                            end
                    end
            end
        val r' = visit r lab
        val _ = Vector.foreach (blocks, rem o Block.label)
    in
        ()
    end


fun print_compre_blocks f labstart =
    let
        fun control b =
            let
                fun check_end (r, prim) =
                    r orelse (
                        case (Prim.name prim) of
                            Prim.Name.Thread_atomicEnd => true
                         | _ => false
                    )
                val has_end = fold_prim_block check_end false b
                (* val _ = print ("control... the block has Thread_atomicEnd? " ^ (Bool.toString has_end) ^ "\n") *)
            in
                has_end
            end
        fun v (r, b) =
            let
                val lab = Block.label b
                val lab_str = Label.toString lab
                val _ = print ("visiting Label: " ^ lab_str ^ "\nLocal variables:\n")
                val stats = Block.statements b
                fun print_local stat =
                    case stat of
                        Statement.T {var = var, ...} =>
                        case var of
                            SOME var =>
                            print ((Var.toString var) ^ "\n")
                          | _ => ()
                val _ = Vector.foreach (stats, print_local)
            in
                ()
            end
        val _ = block_dfs f labstart () v control
    in
        ()
    end

fun find_compre p pssavar_l =
    let
        fun visit_f f =
            let
                val bs =
                    Function.blocks f
                fun visit_b b =
                    let
                        val trans = Block.transfer b
                    in
                        case trans of
                            Transfer.Call {args, func, return} =>
                            if (vec_in_list args pssavar_l)
                            then
                                let
                                    val _ = print "Found Calling PSSA\n"
                                    val labstart =
                                        case return of
                                            Return.NonTail {cont, handler} =>
                                            print_compre_blocks f cont
                                          | _ => ()
                                in
                                    ()
                                end
                            else
                                ()
                          | _ => ()
                    end
                val _ =
                    Vector.foreach (bs, visit_b)
            in
                ()
            end
        val _ = Program.dfs (p, (fn f =>
                                    let val _ = visit_f f
                                    in
                                        fn () => ()
                                    end)
                            )
    in
        ()
    end

fun print_local stat =
    case stat of
        Statement.T {var = var, ...} =>
        case var of
            SOME var =>
            print ((Var.toString var) ^ "\n")
          | _ => ()

fun find_parallel p =
    let
        fun visit_f f =
            let
                val bs =
                    Function.blocks f
                fun visit_b b =
                    let
                        fun check_begin (r, prim) =
                            r orelse (
                                case (Prim.name prim) of
                                    Prim.Name.Thread_parallelBegin => true
                                  | _ => false
                            )
                        fun check_end (r, prim) =
                            r orelse (
                                case (Prim.name prim) of
                                    Prim.Name.Thread_parallelEnd => true
                                  | _ => false
                            )
                        val has_begin = fold_prim_block check_begin false b
                    in
                        if has_begin
                        then
                            let
                                val labstart = Block.label b
                                fun control b =
                                    let
                                        val has_end = fold_prim_block check_end false b
                                        val _ = print ("control... the block has Thread_parallelEnd? " ^ (Bool.toString has_end) ^ "\n")
                                    in
                                        has_end
                                    end
                                fun v (r, b) =
                                    let
                                        val lab = Block.label b
                                        val lab_str = Label.toString lab
                                        val _ = print ("visiting Label: " ^ lab_str ^ "\nLocal variables:\n")
                                        val stats = Block.statements b
                                        val _ = Vector.foreach (stats, print_local)
                                    in
                                        ()
                                    end
                                val _ = block_dfs f labstart () v control
                            in
                                ()
                            end
                        else
                            ()
                    end
                val _ =
                    Vector.foreach (bs, visit_b)
            in
                ()
            end
        val _ = Program.dfs (p, (fn f =>
                                    let val _ = visit_f f
                                    in
                                        fn () => ()
                                    end)
                            )
    in
        ()
    end



val pssa =
 fn p =>
    case p of
        Program.T {datatypes, functions, globals, main} =>
        let
            val _ = print "PSSA\n"
            val pssavar_l = Vector.foldr (
                    globals, [], (
                        fn (stat, r) =>
                           case (Statement.exp stat) of
                               Exp.Const expvar =>
                               let
                                   val expvar_str = Const.toString expvar
                               in
                                   if String.compare (expvar_str, "\"PSSACOMPRE\"") = EQUAL
                                   then
                                       let
                                           val _ = print "Got:\n"
                                       in
                                           case (Statement.var stat) of
                                               SOME var =>
                                               let
                                                   val _ = print ("Got :" ^ (Var.toString var) ^ "\n")
                                               in
                                                   var :: r
                                               end
                                             | NONE => r
                                       end
                                   else
                                       r
                               end
                             | _ => r
                    )
                )
            (* val _ = find_compre p pssavar_l *)
            val _ = find_parallel p
        in
            p
        end

end

functor Pssa (S: SSA_TREE_STRUCTS): PSSA =
    PssaParse (SsaTree(S))
