structure Debug :> DEBUG =
struct
  val wrap = BackTrace.monitor
end
