structure MLtonMatrix : MLTON_MATRIX =
struct

structure Prim = Primitive.MLton.Matrix
    open Prim
    type t = Prim.t
    val create = fn (a1, a2) =>
                    Prim.matrix_create ((Word32.fromInt a1 ), (Word32.fromInt a2))
    val read = fn (p, a1, a2) =>
                  Word32.toInt (Prim.matrix_read (p, (Word32.fromInt a1), (Word32.fromInt a2)))
    val write = fn (p, a1, a2, b) =>
                   Prim.matrix_write (p, (Word32.fromInt a1), (Word32.fromInt a2), (Word32.fromInt b))
    val multiply = Prim.matrix_multiply
end
