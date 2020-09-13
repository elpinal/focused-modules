type path = tycon

structure SK : sig
  exception NotSubkind of kind * kind
  exception PathMismatch of env * tycon * tycon
  exception VarMismatch of tvar * tvar

  val get_natural_kind : env -> path -> kind option
  val normalize        : env -> tycon -> tycon

  val is_valid_kind : env -> kind -> unit

  (* Returns a principal kind. *)
  val synthesize_kind : env -> tycon -> kind

  (* The kind must be valid. *)
  val kind_check : env -> tycon -> kind -> unit

  (* The two kinds must be valid. *)
  val equiv_kind : env -> kind -> kind -> unit

  (* The two types must have the given kind. *)
  val equiv_type : env -> tycon -> tycon -> kind -> unit

  (* The two paths must have the given kind. *)
  val equiv_path : env -> path -> path -> kind

  (* The two kinds must be valid. *)
  val is_subkind_of : env -> kind -> kind -> unit
end = struct
  open Std

  exception CannotApplyNonFunction of kind
  exception CannotProjectNonProduct of kind
  exception KindMismatch of kind * kind
  exception NotSubkind of kind * kind
  exception PathMismatch of env * tycon * tycon
  exception VarMismatch of tvar * tvar

  exception IsThisReallyOccur of kind (* I'm doubtful whether this exception may be raised. *)

  exception NotPath of tycon

  fun get_natural_kind env =
    fn TUnit => KType
     | TFree v => Env.Type.lookup env v
     | TApp(p, ty) =>
         let val (_, k) = get_natural_kind env p |> Destructor.kind_arrow CannotApplyNonFunction in
           open_at_kind 0 ty k
         end
     | TProj(i, p) =>
         let in
           case i of
                Fst => get_natural_kind env p |> Destructor.kind_product CannotProjectNonProduct |> #1
              | Snd =>
                  get_natural_kind env p
                    |> Destructor.kind_product CannotProjectNonProduct
                    |> #2
                    |> open_at_kind 0 (TProj(Fst, p))
         end
     | ty => raise NotPath ty


  val get_natural_kind = fn env => fn p =>
    SOME(get_natural_kind env p)
    handle NotPath _ => NONE

  fun normalize env ty =
    case get_natural_kind env ty of
         SOME (KSingleton ty1) => normalize env ty1
       | _ =>
           case ty of
                TApp(x, y)  => normalize_app env (normalize env x) y
              | TProj(i, x) => normalize_proj env i $ normalize env x
              | _           => ty

  and normalize_app env x y =
    case x of
         TAbs(_, x') => normalize env $ open_at_tycon 0 y x'
       | _           => TApp(x, y)

  and normalize_proj env i =
    fn TPair p => normalize env $ index i p
       | x     => TProj(i, x)

  fun equiv_kind env k1 k2 =
    case (k1, k2) of
         (KUnit, KUnit) => ()
       | (KType, KType) => ()
       | (KSingleton x, KSingleton y) => equiv_type env x y KType
       | (KArrow(k11, k12), KArrow(k21, k22)) =>
           let
             val () = equiv_kind env k11 k21
             val fv = TVar.fresh ()
             val f = open_at_kind 0 (TFree fv)
           in
             equiv_kind (env |> Env.Type.insert fv k11) (f k12) (f k22)
           end
       | (KProd(k11, k12), KProd(k21, k22)) =>
           let
             val () = equiv_kind env k11 k21
             val fv = TVar.fresh ()
             val f = open_at_kind 0 (TFree fv)
           in
             equiv_kind (env |> Env.Type.insert fv k11) (f k12) (f k22)
           end
       | _ => raise KindMismatch(k1, k2)

  and equiv_type env ty1 ty2 k0 =
    case k0 of
         KSingleton _ => ()
       | KUnit        => () (* All constructors of kind 1 are equivalent. *)
       | KType =>
           let
             val p1 = normalize env ty1
             val p2 = normalize env ty2
             val k = equiv_path env p1 p2
           in
             case k of
                  KType => ()
                | _     => raise IsThisReallyOccur k
           end
       | KArrow(k1, k2) =>
           let
             val fv = TVar.fresh ()
             fun f x = TApp(x, TFree fv)
           in
             equiv_type (env |> Env.Type.insert fv k1) (f ty1) (f ty2) $ open_at_kind 0 (TFree fv) k2
           end
       | KProd(k1, k2) =>
           let val () = equiv_type env (TProj(Fst, ty1)) (TProj(Fst, ty2)) k1 in
             equiv_type env (TProj(Snd, ty1)) (TProj(Snd, ty2)) $ open_at_kind 0 (TProj(Fst, ty1)) k2
           end

  and equiv_path env p1 p2 =
    case (p1, p2) of
        (TFree v1, TFree v2) =>
          if v1 = v2
          then Env.Type.lookup env v1
          else raise VarMismatch(v1, v2)
      | (TUnit, TUnit) => KType
      | (TArrow(ty11, ty12), TArrow(ty21, ty22)) =>
          KType
          before equiv_type env ty11 ty21 KType
          before equiv_type env ty12 ty22 KType
      | (TProd(ty11, ty12), TProd(ty21, ty22)) =>
          KType
          before equiv_type env ty11 ty21 KType
          before equiv_type env ty12 ty22 KType
      | (TForall(k1, ty1), TForall(k2, ty2)) =>
          let
            val fv = TVar.fresh ()
            val () = equiv_kind env k1 k2
            val f = open_at_tycon 0 (TFree fv)
            val () = equiv_type (env |> Env.Type.insert fv k1) (f ty1) (f ty2) KType
          in
            KType
          end
      | (TExist(k1, ty1), TExist(k2, ty2)) =>
          let
            val fv = TVar.fresh ()
            val () = equiv_kind env k1 k2
            val f = open_at_tycon 0 (TFree fv)
            val () = equiv_type (env |> Env.Type.insert fv k1) (f ty1) (f ty2) KType
          in
            KType
          end
      | (TProj(Fst, p1), TProj(Fst, p2)) =>
          equiv_path env p1 p2 |> Destructor.kind_product CannotProjectNonProduct |> #1
      | (TProj(Snd, p1), TProj(Snd, p2)) =>
          equiv_path env p1 p2 |> Destructor.kind_product CannotProjectNonProduct |> #2 |> open_at_kind 0 (TProj(Fst, p1))
      | (TApp(p1, x), TApp(p2, y)) =>
          let
            val (k1, k2) = equiv_path env p1 p2 |> Destructor.kind_arrow CannotApplyNonFunction
            val () = equiv_type env x y k1
          in
            open_at_kind 0 x k2
          end
      (* I think `TStar` never arise here. *)
      | _ => raise PathMismatch(env, p1, p2)

  fun is_subkind_of env k1 k2 =
    case (k1, k2) of
        (KType, KType)        => ()
      | (KUnit, KUnit)        => ()
      | (KSingleton _, KType) => ()
      | (KSingleton ty1, KSingleton ty2) => equiv_type env ty1 ty2 KType
      | (KArrow(k11, k12), KArrow(k21, k22)) =>
          let
            val () = is_subkind_of env k21 k11 (* Contravariant. *)
            val fv = TVar.fresh ()
            val x = open_at_kind 0 (TFree fv) k12
            val y = open_at_kind 0 (TFree fv) k22
          in
            is_subkind_of (env |> Env.Type.insert fv k21) x y
          end
      | (KProd(k11, k12), KProd(k21, k22)) =>
          let
            val () = is_subkind_of env k11 k21 (* Covariant. *)
            val fv = TVar.fresh ()
            val x = open_at_kind 0 (TFree fv) k12
            val y = open_at_kind 0 (TFree fv) k22
          in
            is_subkind_of (env |> Env.Type.insert fv k11) x y
          end
      | _ => raise NotSubkind(k1, k2)

  fun is_valid_kind env =
    fn KType          => ()
     | KUnit          => ()
     | KSingleton ty  => kind_check env ty KType
     | KArrow(k1, k2) =>
         let val fv = TVar.fresh () in
           is_valid_kind env k1
           before is_valid_kind (env |> Env.Type.insert fv k1) (open_at_kind 0 (TFree fv) k2)
         end
     | KProd(k1, k2) =>
         let val fv = TVar.fresh () in
           is_valid_kind env k1
           before is_valid_kind (env |> Env.Type.insert fv k1) (open_at_kind 0 (TFree fv) k2)
         end

  and synthesize_kind env =
    fn TBound _      => raise Unreachable (* We work only on locally closed types. *)
     | TFree v       => Singleton.kind (TFree v) $ Env.Type.lookup env v
     | TStar         => KUnit
     | TAbs(k, ty) =>
         let
           val () = is_valid_kind env k
           val fv = TVar.fresh ()
           val k' = synthesize_kind (env |> Env.Type.insert fv k) $ open_at_tycon 0 (TFree fv) ty
         in
           KArrow(k, close_at_kind 0 fv k')
         end
     | TApp(ty1, ty2) =>
         let
           val (k1, k2) = synthesize_kind env ty1 |> Destructor.kind_arrow CannotApplyNonFunction
           val () = kind_check env ty2 k1
         in
           open_at_kind 0 ty2 k2
         end
     | TPair(ty1, ty2) =>
         let
           val k1 = synthesize_kind env ty1
           val k2 = synthesize_kind env ty2
         in
           KProd(k1, k2)
         end
     | TProj(i, ty) =>
         let val (k1, k2) = synthesize_kind env ty |> Destructor.kind_product CannotProjectNonProduct in
           case i of
               Fst => k1
             | Snd => open_at_kind 0 (TProj(Fst, ty)) k2
         end
     | TUnit => KSingleton TUnit
     | TArrow(x, y) =>
         KSingleton (TArrow(x, y))
         before kind_check env x KType
         before kind_check env y KType
     | TProd(x, y) =>
         KSingleton (TProd(x, y))
         before kind_check env x KType
         before kind_check env y KType
     | TForall(k, ty) =>
         let
           val () = is_valid_kind env k
           val fv = TVar.fresh ()
         in
           KSingleton (TForall(k, ty))
           before kind_check (env |> Env.Type.insert fv k) (open_at_tycon 0 (TFree fv) ty) KType
         end
     | TExist(k, ty) =>
         let
           val () = is_valid_kind env k
           val fv = TVar.fresh ()
         in
           KSingleton (TExist(k, ty))
           before kind_check (env |> Env.Type.insert fv k) (open_at_tycon 0 (TFree fv) ty) KType
         end

  and kind_check env ty k2 =
  let val k1 = synthesize_kind env ty in
    is_subkind_of env k1 k2
  end
end
