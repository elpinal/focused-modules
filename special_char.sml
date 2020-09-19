structure SpecialChar :> sig
  type t

  val classify : word -> t option
  val as_ascii : t -> string
end = struct
  datatype t
    = Forall
    | Exist

  val classify =
    fn 0wx2200 => SOME Forall
     | 0wx2203 => SOME Exist
     | _       => NONE

  val as_ascii =
    fn Forall => " forall "
     | Exist  => " exist "
end
