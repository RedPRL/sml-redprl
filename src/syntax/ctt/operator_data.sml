structure CttOperatorData =
struct
  datatype ctt_operator =
      CAPPROX of Sort.t
    | CEQUIV of Sort.t
    | AX
end
