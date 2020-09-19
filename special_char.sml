structure SpecialChar :> sig
  type t

  val classify : word -> t option
  val as_ascii : t -> string
end = struct
  datatype t
    = Forall
    | Exist
    | CapitalPi
    | CapitalSigma
    | Lambda
    | CapitalLambda
    | Circle

  val classify =
    fn 0wx2200 => SOME Forall
     | 0wx2203 => SOME Exist
     | 0wx03A0 => SOME CapitalPi
     | 0wx03A3 => SOME CapitalSigma
     | 0wx03BB => SOME Lambda
     | 0wx039B => SOME CapitalLambda
     | 0wx25CB => SOME Circle
     | _       => NONE

  val as_ascii =
    fn Forall        => " forall "
     | Exist         => " exist "
     | CapitalPi     => " " (* TODO *)
     | CapitalSigma  => " " (* TODO *)
     | Lambda        => " fun "
     | CapitalLambda => " poly "
     | Circle        => " circ "
end
