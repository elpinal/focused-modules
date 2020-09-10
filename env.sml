signature ENV = sig
  type t

  val initial : t

  structure Type : sig
    exception Unbound of tvar

    val lookup : t -> tvar -> kind
    val insert : tvar -> kind -> t -> t
  end

  structure Val : sig
    val lookup : t -> var -> tycon
    val insert : var -> tycon -> t -> t
  end

  structure Module : sig
    val lookup : t -> mvar -> sign * tvar
    val insert : tvar -> mvar -> kind -> sign -> t -> t
  end
end

structure Env :> ENV = struct
  structure TMap = BinarySearchMap (TVar)
  structure VMap = BinarySearchMap (open String type t = string)
  structure MMap = VMap :> MAP where type key = string

  type t = kind TMap.t * tycon VMap.t * (sign * tvar) MMap.t

  val initial = (TMap.empty, VMap.empty, MMap.empty)

  structure Type = struct
    exception Unbound of tvar

    fun lookup (m, _, _) v =
      case TMap.lookup v m of
           NONE   => raise Unbound v
         | SOME x => x

    fun insert v x (m, a, b) = (TMap.insert v x m, a, b)
  end

  structure Module = struct
    exception Unbound of mvar

    fun lookup (_, _, m) v =
      case MMap.lookup v m of
           NONE   => raise Unbound v
         | SOME x => x

    fun insert tv mv k s (tm, vm, mm) =
      (TMap.insert tv k tm, vm, MMap.insert mv (s, tv) mm)
  end

  structure Val = struct
    exception Unbound of var

    fun lookup (_, m, _) v =
      case VMap.lookup v m of
           NONE   => raise Unbound v
         | SOME x => x

    fun insert v x (a, m, b) = (a, VMap.insert v x m, b)
  end
end

type env = Env.t
