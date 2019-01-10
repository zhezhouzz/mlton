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


fun block_normal_next b =
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
                                                   vec, [], (fn ((_, lab), r) =>
                                                                lab :: r
                                                            )
                                               )
                                             | Cases.Word (_, vec) =>
                                               Vector.foldr (
                                                   vec, [], (fn ((_, lab), r) =>
                                                                lab :: r
                                                            )
                                               )
                                                            val lab_l = label_l @ caselab_l
                       in
                           lab_l
                       end
                     | Transfer.Goto {dst, ...} => [dst]
                     | _ => []
    in
        next
    end

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
        Statement.T {exp, ...} =>
        case exp of
            Exp.PrimApp {prim, ...} =>
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

(* fun merge_local rs = *)
(*     let *)
(*         val resultr = ref [] *)
(*         fun merge r = *)
(*             List.foreach (r, (fn (var, str) => *)
(*                                  resultr := *)
(*                                  List.fold (!resultr, [], (fn ((var', str'), tmp) => *)
(*                                                               if Var.equals (var, var') *)
(*                                                               then *)
(*                                                                   (var', (str' ^ str)) :: tmp *)
(*                                                               else *)
(*                                                                   (var', str') :: tmp *)
(*                                            )) *)
(*                          )) *)
(*         val _ = List.foreach (rs, merge) *)
(*     in *)
(*         !resultr *)
(*     end *)

fun pssa_walker_f f =
    let
        val {blocks, ...} = Function.dest f
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
                        val b = Vector.sub (blocks, i)
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
                                        block_normal_next b
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
