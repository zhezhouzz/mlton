(* Primitive Matrix Signature *)
(* By Zhe Zhou *)

type int = Int.int
type string = String.string

signature MLTON_MATRIX =
sig
    type t
    val get_rows: t -> int
    val get_cols: t -> int
    val get_size: t -> int
    val initFromMMFile: t * string -> unit
    val initFromHexFile: t * string -> unit
    val create: int * int -> t
    val read: t * int * int -> int
    val write: t * int * int * int -> unit
    val multiply: t * t -> t
    val add: t * t -> t
end
