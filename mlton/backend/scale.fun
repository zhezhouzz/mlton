(* Copyright (C) 2004 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under the GNU General Public License (GPL).
 * Please see the file MLton-LICENSE for license information.
 *)

functor Scale (S: SCALE_STRUCTS): SCALE =
struct

open S

datatype t = One | Two | Four | Eight

val toString =
   fn One => "1"
    | Two => "2"
    | Four => "4"
    | Eight => "8"

val layout = Layout.str o toString

val fromInt: int -> t option =
   fn 1 => SOME One
    | 2 => SOME Two
    | 4 => SOME Four
    | 8 => SOME Eight
    | _ => NONE

end
