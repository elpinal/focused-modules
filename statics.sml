structure Signature : sig
  val fst : sign -> kind
end = struct
  (* Need not to open because it preserves the binding structure. *)
  val rec fst =
    fn SUnit        => KUnit
     | SStatic k    => k
     | SDynamic _   => KUnit
     | SArrow(x, y) => KArrow(fst x, fst y)
     | SProd(x, y)  => KProd(fst x, fst y)
     | SMonad _     => KUnit
end

structure Module : sig
  val fst : env -> module -> tycon
end = struct
  structure Subst :> sig
    type t

    val empty : t

    val delete : mvar -> t -> t
    val insert : mvar -> tycon -> t -> t
    val lookup : mvar -> t -> tycon option
  end = struct
    structure Map = BinarySearchMap (open String type t = string)
    open Map

    (* While MLton wrongly warns this as "Unused type: t", but this is in fact necessary. *)
    type t = tycon t
  end

  open Std

  fun fst_exp env subst =
    fn MVar v =>
         let in
           case Subst.lookup v subst of
                NONE    => Env.Module.lookup env v |> #2 |> TFree
              | SOME ty => ty (* Indicating that the module variable is to be replaced by a static atomic module. *)
         end
     | MStar          => TStar
     | MStatic ty     => ty
     | MDynamic _     => TStar
     | MAbs(mv, s, x) =>
         let
           val fv = TVar.fresh ()
           val k = Signature.fst s
           val env' = env |> Env.Module.insert fv mv k s
           val subst' = Subst.delete mv subst
         in
           TAbs(k, close_at_tycon 0 fv $ fst_exp env' subst' $ open_at_module 0 (TFree fv) x)
         end
     | MApp(x, y)           => TApp(fst_exp env subst x, fst_exp env subst y)
     | MPair(x, y)          => TPair(fst_exp env subst x, fst_exp env subst y)
     | MProj(i, x)          => TProj(i, fst_exp env subst x)
     | MLet(_, _, x)        => fst_exp env subst x
     | MCirc _              => TStar
     | MLetModule(mv, x, y) =>
         let
           val ty1 = fst_exp env subst x
           (* Use `mv` as a static atomic module containing `ty1`. *)
           val ty2 = fst_exp env (Subst.insert mv ty1 subst) $ open_at_module 0 ty1 y
         in
           ty2
         end

  fun fst env m = fst_exp env Subst.empty m
end

signature SK = sig
  val is_valid_kind : env -> kind -> unit

  val normalize : env -> tycon -> tycon

  (* Return a principal kind. *)
  val synthesize_kind : env -> tycon -> kind

  (* The kind must be valid. *)
  val kind_check : env -> tycon -> kind -> unit

  (* The two kinds must be valid. *)
  val is_subkind_of : env -> kind -> kind -> unit

  (* The two types must have the given kind. *)
  val equiv_type : env -> tycon -> tycon -> kind -> unit
end

functor F(X : SK) = struct
  open Std

  exception CannotApplyNonFunctor of sign
  exception CannotProjectNonProduct of sign
  exception CannotBindNonMonad of sign
  exception NotSubsignature of sign * sign
  exception CannotExtractNonDynamic of sign
  exception CannotInstNonUniversal of tycon
  exception CannotUnpackNonExist of tycon
  exception CannotProjectNonProductType of tycon
  exception CannotApplyNonFunction of tycon
  exception ValueRestriction of term

  (* This error is impossible due to the syntactic restriction. *)
  exception NotPosSubsignature of pos_sig * pos_sig

  structure Lit = struct
    val synthesize_type =
      fn LBool _ => TBase BBool
       | LInt _  => TBase BInt
  end

  (* The argument must be locally closed. *)
  val rec inhabit =
    fn KUnit         => TStar
     | KType         => TUnit (* TODO: Use a designated type rather than `unit` type. *)
     | KSingleton ty => ty
     | KArrow(x, y)  =>
         let val fv = TVar.fresh () in
           TAbs(x, close_at_tycon 0 fv $ inhabit $ open_at_kind 0 (TFree fv) y)
         end
     | KProd(x, y)   =>
         let val ty1 = inhabit x in
           TPair(ty1, inhabit $ open_at_kind 0 ty1 y)
         end

  val inhabit_env =
    foldr
      (fn ((v, k), f) => open_at_tycon 0 (inhabit k) o close_at_tycon 0 v o f)
      (fn ty => ty)

  (* Preserve locally closed property in the hope that error messages may be improved. *)
  val rec enforce_value_restriction =
    fn EStar             => ()
     | EAbs _            => ()
     | EPair(x, y)       => enforce_value_restriction x before enforce_value_restriction y
     | EGen(_, x)        => enforce_value_restriction $ open_at_term 0 (TFree $ TVar.fresh ()) x
     | EPack(_, x, _, _) => enforce_value_restriction x
     | e                 => raise ValueRestriction e

  val rec left_inversion =
    fn PDown s      => ([], s)
     | PExist(k, p) =>
         let
           val fv = TVar.fresh ()
           val (xs, s) = left_inversion $ open_at_pos_sig 0 (TFree fv) p
         in
           ((fv, k) :: xs, s)
         end

  fun well_formed_sig env =
    fn SUnit => ()
     | SStatic k => X.is_valid_kind env k
     | SDynamic ty => X.kind_check env ty KType
     | SArrow(x, y) =>
         let
           val () = well_formed_sig env x
           val fv = TVar.fresh ()
         in
           well_formed_sig (env |> Env.Type.insert fv (Signature.fst x)) $ open_at_sig 0 (TFree fv) y
         end
     | SProd(x, y) =>
         let
           val () = well_formed_sig env x
           val fv = TVar.fresh ()
         in
           well_formed_sig (env |> Env.Type.insert fv (Signature.fst x)) $ open_at_sig 0 (TFree fv) y
         end
     | SMonad p => well_formed_pos_sig env p

  and well_formed_pos_sig env =
    fn PDown s => well_formed_sig env s
     | PExist(k, p) =>
         let
           val () = X.is_valid_kind env k
           val fv = TVar.fresh ()
         in
           well_formed_pos_sig (env |> Env.Type.insert fv k) $ open_at_pos_sig 0 (TFree fv) p
         end

  fun subsignature env s1 s2 =
    case (s1, s2) of
         (SUnit, SUnit) => ()
       | (SStatic k1, SStatic k2) => X.is_subkind_of env k1 k2
       | (SDynamic ty1, SDynamic ty2) => X.equiv_type env ty1 ty2 KType
       | (SMonad p1, SMonad p2) => pos_subsignature env p1 p2
       | (SArrow(s11, s12), SArrow(s21, s22)) =>
           let
             val () = subsignature env s21 s11
             val fv = TVar.fresh ()
             val env' = env |> Env.Type.insert fv (Signature.fst s21)
           in
             subsignature env' (open_at_sig 0 (TFree fv) s12) (open_at_sig 0 (TFree fv) s22)
           end
       | (SProd(s11, s12), SProd(s21, s22)) =>
           let
             val () = subsignature env s11 s21
             val fv = TVar.fresh ()
             val env' = env |> Env.Type.insert fv (Signature.fst s11)
           in
             subsignature env' (open_at_sig 0 (TFree fv) s12) (open_at_sig 0 (TFree fv) s22)
           end
       | _ => raise NotSubsignature(s1, s2)

  and pos_subsignature env p1 p2 =
    case (p1, p2) of
         (PDown s1, PDown s2) => subsignature env s1 s2
       | (PExist(k, p1), _)   =>
           let val fv = TVar.fresh () in
             pos_subsignature (env |> Env.Type.insert fv k) (open_at_pos_sig 0 (TFree fv) p1) p2
           end
       | _ => raise NotPosSubsignature(p1, p2)

  (* Produce a principal signature of a module. *)
  (* The returned value is always locally closed. *)
  fun synthesize_signature env =
    fn MVar v =>
      let val (s, tv) = Env.Module.lookup env v in
        Singleton.sign (TFree tv) s
      end
     | MStar         => SUnit
     | MStatic ty    => SStatic $ X.synthesize_kind env ty
     | MDynamic e    => SDynamic $ synthesize_type env e
     | MAbs(v, s, x) =>
         let
           val () = well_formed_sig env s
           val fv = TVar.fresh ()
           val env' = env |> Env.Module.insert fv v (Signature.fst s) s
           val s2 = synthesize_signature env' $ open_at_module 0 (TFree fv) x
         in
           SArrow(s, close_at_sig 0 fv s2)
         end
     | MApp(x, y) =>
         let
           val (s11, s12) = synthesize_signature env x |> Destructor.sig_arrow CannotApplyNonFunctor
           val () = signature_check env y s11
           val ty = Module.fst env y
         in
           open_at_sig 0 ty s12
         end
     | MPair(x, y) => SProd(synthesize_signature env x, synthesize_signature env y)
     | MProj(i, x) =>
         let
           val (s1, s2) = synthesize_signature env x |> Destructor.sig_product CannotProjectNonProduct
         in
           case i of
                Fst => s1
              | Snd => open_at_sig 0 (TProj(Fst, Module.fst env x)) s2
         end
     | MLet(v, e, x) =>
         let
           val ty = synthesize_type env e
         in
           synthesize_signature (env |> Env.Val.insert v ty) x
         end
     | MCirc l              => SMonad $ synthesize_pos_sig env l
     | MLetModule(mv, x, y) =>
         let
           val s1 = synthesize_signature env x
           val ty = Module.fst env x
           val fv = TVar.fresh ()
           val env' = env |> Env.Module.insert fv mv (Signature.fst s1) s1
           val s2 = synthesize_signature env' $ open_at_module 0 (TFree fv) y
         in
           open_at_sig 0 ty $ close_at_sig 0 fv s2
         end

  and signature_check env m s0 =
    let val s = synthesize_signature env m in
      subsignature env s s0
    end

  and synthesize_pos_sig env =
    fn LRet m => PDown $ synthesize_signature env m
     | LSeal(m, s) =>
         PDown s
         before well_formed_sig env s
         before signature_check env m s
     | LBind(v, m, x) =>
         let
           val p = synthesize_signature env m |> Destructor.sig_monad CannotBindNonMonad
           val (xs, s) = left_inversion p
           val k = Signature.fst s
           val fv = TVar.fresh ()
           val env' = env
              |> foldr (fn ((tv, k), f) => f o Env.Type.insert tv k) (Env.Module.insert fv v k s) xs
           val p' = synthesize_pos_sig env' $ open_at_lax_module 0 (TFree fv) x
         in
           PExist(k, pos_exist_close xs $ close_at_pos_sig 0 fv p')
         end
     | LUnpack(v, e, x) =>
         let
           val (k, ty) = synthesize_type env e |> X.normalize env |> Destructor.tycon_exist CannotUnpackNonExist
           val fv = TVar.fresh ()
           val env' = env |> Env.Type.insert fv k |> Env.Val.insert v (open_at_tycon 0 (TFree fv) ty)
           val p = synthesize_pos_sig env' $ open_at_lax_module 0 (TFree fv) x
         in
           PExist(k, close_at_pos_sig 0 fv p)
         end

  and pos_exist_close xs p0 = foldr (fn ((tv, k), p) => PExist(k, close_at_pos_sig 0 tv p)) p0 xs

  (* Produce a type of a term *)
  and synthesize_type env =
    fn EVar v => Env.Val.lookup env v
     | EStar  => TUnit
     | ELit l => Lit.synthesize_type l
     | EAbs(v, ty, x) =>
         let
           val () = X.kind_check env ty KType
           val ty2 = synthesize_type (env |> Env.Val.insert v ty) x
         in
           TArrow(ty, ty2)
         end
     | EApp(x, y) =>
         let
           val (ty1, ty2) = synthesize_type env x |> X.normalize env |> Destructor.tycon_arrow CannotApplyNonFunction
           val () = typecheck env y ty1
         in
           ty2
         end
     | EPair(x, y) => TProd(synthesize_type env x, synthesize_type env y)
     | EProj(i, x) => synthesize_type env x
         |> X.normalize env
         |> Destructor.tycon_product CannotProjectNonProductType
         |> index i
     | EGen(k, x) =>
         let
           val () = X.is_valid_kind env k
           val fv = TVar.fresh ()
           val x' = open_at_term 0 (TFree fv) x
           val () = enforce_value_restriction x'
           val ty = synthesize_type (env |> Env.Type.insert fv k) x'
         in
           TForall(k, close_at_tycon 0 fv ty)
         end
     | EInst(x, ty) =>
         let
           val (k, ty') = synthesize_type env x |> X.normalize env |> Destructor.tycon_forall CannotInstNonUniversal
           val () = X.kind_check env ty k
         in
           open_at_tycon 0 ty ty'
         end
     | EPack(w, x, k, ty) =>
         let
           val () = X.is_valid_kind env k
           val () = X.kind_check env w k
           val () = typecheck env x $ open_at_tycon 0 w ty
           val fv = TVar.fresh ()
           val () = X.kind_check (env |> Env.Type.insert fv k) (open_at_tycon 0 (TFree fv) ty) KType
         in
           TExist(k, ty)
         end
     | EUnpack(v, x, y) =>
         let
           val (k, ty) = synthesize_type env x |> X.normalize env |> Destructor.tycon_exist CannotUnpackNonExist
           val fv = TVar.fresh ()
           val env' = env |> Env.Type.insert fv k |> Env.Val.insert v (open_at_tycon 0 (TFree fv) ty)
           val ty2 = synthesize_type env' $ open_at_term 0 (TFree fv) y
           val ty2' = open_at_tycon 0 (inhabit k) $ close_at_tycon 0 fv ty2
           val () = X.equiv_type env' ty2 ty2' KType
         in
           ty2'
         end
     | EFix(ty, x) =>
         let
           val () = X.kind_check env ty KType
           val () = typecheck env x $ TArrow(TArrow(TUnit, ty), ty)
         in
           ty
         end
     | ELet(v, x, y)    => synthesize_type (env |> Env.Val.insert v (synthesize_type env x)) y
     | EExt m           => synthesize_signature env m |> Destructor.sig_dynamic CannotExtractNonDynamic
     | ELetLax(v, l, x) =>
         let
           val p = synthesize_pos_sig env l
           val (xs, s) = left_inversion p
           val k = Signature.fst s
           val fv = TVar.fresh ()
           val env' = env
             |> foldr (fn ((tv, k), f) => f o Env.Type.insert tv k) (Env.Module.insert fv v k s) xs
           val ty = synthesize_type env' $ open_at_term 0 (TFree fv) x
           val ty' = inhabit_env xs $ open_at_tycon 0 (inhabit k) $ close_at_tycon 0 fv ty
           val () = X.equiv_type env' ty ty' KType
         in
           ty'
         end
     | EIf(x, y, z) =>
         let
           val () = typecheck env x $ TBase BBool
           val ty = synthesize_type env y
           val () = typecheck env z ty
         in
           ty
         end

  and typecheck env e ty =
  let val ty' = synthesize_type env e in
    X.equiv_type env ty' ty KType
  end
end

structure M = F (SK)
