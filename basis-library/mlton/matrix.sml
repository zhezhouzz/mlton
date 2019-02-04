structure MLtonMatrix : MLTON_MATRIX =
struct

structure Prim = Primitive.MLton.Matrix
    open Prim
    type t = Prim.t
    val get_rows = fn p => Word32.toInt (Prim.matrix_get_rows p)
    val get_cols = fn p => Word32.toInt (Prim.matrix_get_cols p)
    val get_size = fn p => Word32.toInt (Prim.matrix_get_size p)
    val initFromHexFile = fn (p, s) =>
                            Prim.matrix_initFromHexFile (p, Primitive.NullString8.fromString (String.nullTerm s))
    val initFromMMFile = fn (p, s) =>
                            Prim.matrix_initFromMMFile (p, Primitive.NullString8.fromString (String.nullTerm s))
    val create = fn (a1, a2) =>
                    Prim.matrix_create ((Word32.fromInt a1 ), (Word32.fromInt a2))
    val read = fn (p, a1, a2) =>
                  Word32.toInt (Prim.matrix_read (p, (Word32.fromInt a1), (Word32.fromInt a2)))
    val write = fn (p, a1, a2, b) =>
                   Prim.matrix_write (p, (Word32.fromInt a1), (Word32.fromInt a2), (Word32.fromInt b))
    val multiply = fn (p1, p2) => Prim.matrix_multiply (p1, p2)
    val add = fn (p1, p2) => Prim.matrix_add (p1, p2)
end
