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
                then r
                else
                    let
                        val _ = Array.update (visited, i, true)
                        val b as Block.T {transfer, ...} =
                            Vector.sub (blocks, i)
                        val r' = v (r, b)
                    in
                        if control b
                        then
                            r'
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
        r'
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

fun string_local stat =
    case stat of
        Statement.T {var = var, ...} =>
        case var of
            SOME var =>
            Var.toString var
          | _ => ""

fun add_global_strings g varstrs =
    let
        fun varstr2stat (new_var, str) =
            let
                val new_exp = Exp.Const (Const.string str)
                val new_ty = Type.vector (Type.word WordSize.word8)
            in
                Statement.T {exp = new_exp,
                             ty = new_ty,
                             var = new_var}
            end
        val stats = List.map (varstrs, varstr2stat)
        val stats_vec = Vector.fromList stats
        val new_g = Vector.concat [g, stats_vec]
    in
        new_g
    end

datatype walkstate =
         GotNone
         | GotBegin of (Var.t * string)
         | GotEnd of (Var.t * string)

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

fun error_headle str = print ("pssa_error: " ^ str ^ "\n")

fun pssa_walk_s ((stat:Statement.t), walkstate) =
    let
        fun normal_case var =
            case var of
                NONE => (stat, walkstate)
              | SOME statvar =>
                case walkstate of
                    GotBegin (var, str) =>
                    let
                        val new_str = str ^ " " ^ (Var.toString statvar)
                    in
                        (stat, (GotBegin (var, new_str)))
                    end
                  | _ => (stat, walkstate)
        val (new_stat, new_state) =
            case stat of
        Statement.T {exp, ty, var} =>
        case exp of
            Exp.PrimApp {args, prim, targs} =>
            (case (Prim.name prim) of
                 Prim.Name.Thread_parallelBegin =>
                 (case walkstate of
                      GotNone =>
                      let
                          val new_var = Var.newString "parallel"
                          val _ = print ("pssa_walk_s: " ^ (Var.toString new_var) ^ "\n")
                          val new_state = GotBegin (new_var, "")
                          val args = Vector.new1 new_var
                          val new_stat = Statement.T {exp = Exp.PrimApp {args = args, prim = prim, targs = targs}, ty = ty, var = var}
                      in
                          (new_stat, new_state)
                      end
                    | _ =>
                      let
                          val _ = error_headle "statement"
                      in
                          (stat, walkstate)
                      end
                 )
               | Prim.Name.Thread_parallelEnd =>
                 (case walkstate of
                      GotBegin (var, str) =>
                      (stat, (GotEnd (var, str)))
                    | _ =>
                      let
                          val _ = error_headle "statement"
                      in
                          (stat, walkstate)
                      end
                 )
               | _ => normal_case var
            )
          | _ => normal_case var
    in
        (new_stat, new_state)
    end

fun has_parallel_s s =
    case s of
        Statement.T {exp, ty, var} =>
        case exp of
            Exp.PrimApp {args, prim, targs} =>
            (case (Prim.name prim) of
                 Prim.Name.Thread_parallelBegin => true
               | _ => false)
          | _ => false

fun has_parallel_b b =
    let
        val stats = Block.statements b
    in
        Vector.exists (stats, has_parallel_s)
    end

fun pssa_walk_b (b, walkstate) =
    let
        val stats = Block.statements b
        val (new_stats, walkstate) =
            Vector.fold (stats, ([], walkstate), (
                             fn (stat, (new_stats, walkstate)) =>
                                let
                                    val (stat', walkstate') = pssa_walk_s (stat, walkstate)
                                in
                                    ((new_stats @ [stat']), walkstate')
                                end
                        ))
        val new_b = case b of
        Block.T {args, label, statements, transfer} =>
        Block.T {args = args, label = label, statements = (Vector.fromList new_stats), transfer = transfer}
    in

        (new_b, walkstate)
    end

fun merge_local rs =
    let
        val resultr = ref []
        fun merge r =
            List.foreach (r, (fn (var, str) =>
                                 resultr :=
                                 List.fold (!resultr, [], (fn ((var', str'), tmp) =>
                                                              if Var.equals (var, var')
                                                              then
                                                                  (var', (str' ^ str)) :: tmp
                                                              else
                                                                  (var', str') :: tmp
                                           ))
                         ))
        val _ = List.foreach (rs, merge)
    in
        !resultr
    end

fun pssa_walker_f f =
    let
        val {blocks, start, ...} = Function.dest f
        val numBlocks = Vector.length blocks
        val {get = labelIndex, set = setLabelIndex, rem, ...} =
            Property.getSetOnce (Label.plist,
                                 Property.initRaise ("index", Label.layout))
        val _ = Vector.foreachi (blocks, fn (i, Block.T {label, ...}) =>
                                            setLabelIndex (label, i))
        val visited = Array.array (numBlocks, false)
        val new_bs = Array.fromVector blocks
        fun visit (l: Label.t) walkstate =
            let
                val i = labelIndex l
                val _ = print ("pssa_walk_f: " ^ (Label.toString l) ^ "\n")
            in
                if Array.sub (visited, i)
                then NONE
                else
                    let
                        val _ = Array.update (visited, i, true)
                        val b as Block.T {transfer, ...} =
                            Vector.sub (blocks, i)
                        val (newb, walkstate) = pssa_walk_b (b, walkstate)
                        val _ = Array.update (new_bs, i, newb)
                        val (new_state, orest, if_continue) = case walkstate of
                                                    GotNone => (GotNone, NONE, false)
                                                  | GotBegin (var, str) =>
                                                    (GotBegin (var, ""), (SOME (var, str)), true)
                                                  | GotEnd (var, str) =>
                                                    (GotNone, (SOME (var, str)), false)
                        val nexts = if if_continue
                                    then
                                        block_normal_next f b
                                    else
                                        []
                        val orest = List.foldr (
                                nexts, orest, (fn (lab, orest) =>
                                                 let
                                                     val tmp = visit lab new_state
                                                 in
                                                     case tmp of
                                                         NONE => orest
                                                       | SOME (var', str') =>
                                                         case orest of
                                                             NONE => SOME (var', str')
                                                           | SOME (var, str) =>
                                                             SOME (var, (str ^ str'))
                                                 end
                                             )
                            )
                        (* val new_r = merge_local (r :: rest :: rs) *)
                    in
                        orest
                    end
            end
        val paralel_list = Vector.fold (blocks, [], (fn (b, r) =>
                                                        if has_parallel_b b
                                                        then
                                                            (Block.label b) :: r
                                                        else
                                                            r
                                       ))
        val r = List.fold (paralel_list, [], (fn (l, r) =>
                                                 let
                                                     val orest = visit l GotNone
                                                 in
                                                     case orest of
                                                         NONE =>
                                                         let
                                                             val _ = print "BAD ERROR\n"
                                                         in
                                                             r
                                                         end
                                                       | SOME rest => rest :: r
                                                 end
                          ))
        val _ = Vector.foreach (blocks, rem o Block.label)
        val {args, blocks, mayInline, name, raises, returns, start} = Function.dest f
        val new_f = Function.new {args = args, blocks = (Array.toVector new_bs), mayInline = mayInline, name = name, raises = raises, returns = returns, start = start}
    in
        (new_f, r)
    end

fun pssa_walker_p p =
    let
        val (functions_new, r) = case p of
                                     Program.T {functions, ...} =>
                    List.fold (functions, ([], []), (fn (f, (new_fs, r)) =>
                                                        let
                                                            val (new_f, new_r) = pssa_walker_f f
                                                        in
                                                            ((new_f :: new_fs), (new_r @ r))
                                                        end
                              ))
        val varstats = List.map (r, (fn (var, str) =>
                                        (SOME var, str)
                                    )
                                )
        val new_g = case p of
                        Program.T {globals, ...} =>
                        add_global_strings globals varstats
    in
        case p of
            Program.T {datatypes, functions, globals, main} =>
            Program.T {datatypes = datatypes, functions = functions_new, globals = new_g, main = main}
    end


val pssa =
 fn p =>
    let
        val _ = print "PSSA\n"
        val p = pssa_walker_p p
    in
        p
    end

end

functor Pssa (S: SSA_TREE_STRUCTS): PSSA =
    PssaParse (SsaTree(S))
