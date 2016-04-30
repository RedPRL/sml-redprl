structure Target : TARGET =
struct
  open RefinerKit

  infix 4 >>
  infix 3 |>

  datatype target =
      TARGET_HYP of symbol
    | TARGET_CONCL

  type judgment = Lcf.J.judgment

  fun mapConcl f =
    fn TRUE (p, tau) => TRUE (f p, tau)
     | TYPE (p, tau) => TYPE (f p, tau)
     | EQ_MEM (m, n, a) => EQ_MEM (f m, f n, f a)
     | EQ_NEU (r, s) => EQ_NEU (f r, f s)

  fun targetRewrite f target (G |> H >> concl) =
    case target of
        TARGET_HYP sym =>
          let
            val H' = updateHyps (SymbolTelescope.modify sym (fn (x, tau) => (f x, tau))) H
          in
            G |> H' >> concl
          end
      | TARGET_CONCL => G |> H >> mapConcl f concl
end
