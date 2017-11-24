type extradata = unit
val initial_data : unit -> unit
val file : string ref
val line : int ref
type pos = int
val string_of_pos : int -> string
val cur_pd : unit -> int * unit
type pd = pos * extradata
