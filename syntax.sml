(* Syntax definition. Type variables are represented by the locally-nameless representation. *)

structure TVar :> sig
  eqtype t

  val fresh : unit -> t
  val compare : t * t -> order

  val from_string : string -> t (* For parsing. *)

  val show : t -> string

  (* Be careful to use. *)
  val reset : unit -> unit
end = struct
  datatype t
    = I of int (* Generated. For the static semantics. *)
    | S of string (* Textual representation written by users. Only for parsing. *)

  val counter = ref 0

  fun fresh () =
    let
      val n = !counter
      val () = counter := n + 1
    in
      I n
    end

  fun compare (I x, I y) = Int.compare (x, y)
    | compare (S x, S y) = String.compare (x, y)
    | compare (I _, S _) = LESS
    | compare (S _, I _) = GREATER

  val from_string = S

  fun show (I n) = "'" ^ Int.toString n
    | show (S s) = "'" ^ s

  fun reset () = counter := 0
end

(* Type variable *)
type tvar = TVar.t

(* Term variable *)
type var = string

(* Module variable *)
type mvar = string

datatype index
  = Fst
  | Snd

fun index Fst (x, _) = x
  | index Snd (_, y) = y

(* Base type constructor. It can be higher-kinded. *)
datatype base
  = BBool
  | BInt

datatype kind
  = KUnit
  | KType
  | KSingleton of tycon
  | KArrow of kind * kind
  | KProd of kind * kind

and tycon
  = TBound of int
  | TFree of tvar
  | TStar (* Unit constructor *)
  | TAbs of kind * tycon
  | TApp of tycon * tycon
  | TPair of tycon * tycon
  | TProj of index * tycon

  | TUnit (* Unit type *)
  | TBase of base
  | TArrow of tycon * tycon
  | TProd of tycon * tycon
  | TForall of kind * tycon
  | TExist of kind * tycon

datatype sign (* Negative signature *)
  = SUnit
  | SStatic of kind
  | SDynamic of tycon
  | SArrow of sign * sign
  | SProd of sign * sign
  | SMonad of pos_sig

and pos_sig (* Positive signature *)
  = PDown of sign
  | PExist of kind * pos_sig

datatype term
  = EVar of var
  | EStar
  | EAbs of var * tycon * term
  | EApp of term * term
  | EPair of term * term
  | EProj of index * term
  | EGen of kind * term
  | EInst of term * tycon
  | EPack of tycon * term * kind * tycon
  | EUnpack of var * term * term
  | EFix of tycon * term
  | ELet of var * term * term
  | EExt of module
  | ELetLax of mvar * lax_module * term

and module
  = MVar of mvar
  | MStar
  | MStatic of tycon
  | MDynamic of term
  | MAbs of mvar * sign * module
  | MApp of module * module
  | MPair of module * module
  | MProj of index * module
  | MLet of var * term * module
  | MCirc of lax_module
  | MLetModule of mvar * module * module

and lax_module
  = LRet of module
  | LSeal of module * sign
  | LBind of mvar * module * lax_module
  | LUnpack of var * term * lax_module

fun close_at_tycon j fv =
let fun iter x = close_at_tycon j fv x in
  fn TBound i => TBound i
   | TFree tv =>
       if tv = fv
       then TBound j
       else TFree tv
   | TStar         => TStar
   | TAbs(k, x)    => TAbs(close_at_kind j fv k, close_at_tycon (j + 1) fv x)
   | TApp(x, y)    => TApp(iter x, iter y)
   | TPair(x, y)   => TPair(iter x, iter y)
   | TProj(i, x)   => TProj(i, iter x)
   | TUnit         => TUnit
   | TBase b       => TBase b
   | TArrow(x, y)  => TArrow(iter x, iter y)
   | TProd(x, y)   => TProd(iter x, iter y)
   | TForall(k, x) => TForall(close_at_kind j fv k, close_at_tycon (j + 1) fv x)
   | TExist(k, x)  => TExist(close_at_kind j fv k, close_at_tycon (j + 1) fv x)
end

and close_at_kind j fv =
  fn KUnit         => KUnit
   | KType         => KType
   | KSingleton ty => KSingleton(close_at_tycon j fv ty)
   | KArrow(x, y)  => KArrow(close_at_kind j fv x, close_at_kind (j + 1) fv y)
   | KProd(x, y)   => KProd(close_at_kind j fv x, close_at_kind (j + 1) fv y)

fun close_at_sig j fv =
  fn SUnit         => SUnit
   | SStatic k     => SStatic(close_at_kind j fv k)
   | SDynamic ty   => SDynamic(close_at_tycon j fv ty)
   | SArrow(x, y)  => SArrow(close_at_sig j fv x, close_at_sig (j + 1) fv y)
   | SProd(x, y)   => SProd(close_at_sig j fv x, close_at_sig (j + 1) fv y)
   | SMonad p      => SMonad(close_at_pos_sig j fv p)

and close_at_pos_sig j fv =
  fn PDown s      => PDown(close_at_sig j fv s)
   | PExist(k, p) => PExist(close_at_kind j fv k, close_at_pos_sig (j + 1) fv p)

fun close_at_module j fv =
let fun iter x = close_at_module j fv x in
  fn MVar v              => MVar v
   | MStar               => MStar
   | MStatic ty          => MStatic(close_at_tycon j fv ty)
   | MDynamic e          => MDynamic(close_at_term j fv e)
   | MAbs(v, s, x)       => MAbs(v, close_at_sig j fv s, close_at_module (j + 1) fv x)
   | MApp(x, y)          => MApp(iter x, iter y)
   | MPair(x, y)         => MPair(iter x, iter y)
   | MProj(i, x)         => MProj(i, iter x)
   | MLet(v, e, x)       => MLet(v, close_at_term j fv e, iter x)
   | MCirc l             => MCirc(close_at_lax_module j fv l)
   | MLetModule(v, x, y) => MLetModule(v, iter x, close_at_module (j + 1) fv y)
end

and close_at_lax_module j fv =
  fn LRet m           => LRet(close_at_module j fv m)
   | LSeal(m, s)      => LSeal(close_at_module j fv m, close_at_sig j fv s)
   | LBind(v, m, x)   => LBind(v, close_at_module j fv m, close_at_lax_module (j + 1) fv x)
   | LUnpack(v, e, x) => LUnpack(v, close_at_term j fv e, close_at_lax_module (j + 1) fv x)

and close_at_term j fv =
let fun iter x = close_at_term j fv x in
  fn EVar v             => EVar v
   | EStar              => EStar
   | EAbs(v, ty, x)     => EAbs(v, close_at_tycon j fv ty, iter x)
   | EApp(x, y)         => EApp(iter x, iter y)
   | EPair(x, y)        => EPair(iter x, iter y)
   | EProj(i, x)        => EProj(i, iter x)
   | EGen(k, x)         => EGen(close_at_kind j fv k, close_at_term (j + 1) fv x)
   | EInst(x, ty)       => EInst(iter x, close_at_tycon j fv ty)
   | EPack(w, x, k, ty) => EPack(close_at_tycon j fv w, iter x, close_at_kind j fv k, close_at_tycon (j + 1) fv ty)
   | EUnpack(v, x, y)   => EUnpack(v, iter x, close_at_term (j + 1) fv y)
   | EFix(ty, x)        => EFix(close_at_tycon j fv ty, iter x)
   | ELet(v, x, y)      => ELet(v, iter x, iter y)
   | EExt m             => EExt(close_at_module j fv m)
   | ELetLax(v, l, x)   => ELetLax(v, close_at_lax_module j fv l, close_at_term (j + 1) fv x)
end

fun open_at_tycon j by =
let fun iter x = open_at_tycon j by x in
  fn TBound i =>
       if i = j
       then by
       else TBound i
   | TFree tv      => TFree tv
   | TStar         => TStar
   | TAbs(k, x)    => TAbs(open_at_kind j by k, open_at_tycon (j + 1) by x)
   | TApp(x, y)    => TApp(iter x, iter y)
   | TPair(x, y)   => TPair(iter x, iter y)
   | TProj(i, x)   => TProj(i, iter x)
   | TUnit         => TUnit
   | TBase b       => TBase b
   | TArrow(x, y)  => TArrow(iter x, iter y)
   | TProd(x, y)   => TProd(iter x, iter y)
   | TForall(k, x) => TForall(open_at_kind j by k, open_at_tycon (j + 1) by x)
   | TExist(k, x)  => TExist(open_at_kind j by k, open_at_tycon (j + 1) by x)
end

and open_at_kind j by =
  fn KUnit         => KUnit
   | KType         => KType
   | KSingleton ty => KSingleton(open_at_tycon j by ty)
   | KArrow(x, y)  => KArrow(open_at_kind j by x, open_at_kind (j + 1) by y)
   | KProd(x, y)   => KProd(open_at_kind j by x, open_at_kind (j + 1) by y)

fun open_at_sig j by =
  fn SUnit         => SUnit
   | SStatic k     => SStatic(open_at_kind j by k)
   | SDynamic ty   => SDynamic(open_at_tycon j by ty)
   | SArrow(x, y)  => SArrow(open_at_sig j by x, open_at_sig (j + 1) by y)
   | SProd(x, y)   => SProd(open_at_sig j by x, open_at_sig (j + 1) by y)
   | SMonad p      => SMonad(open_at_pos_sig j by p)

and open_at_pos_sig j by =
  fn PDown s      => PDown(open_at_sig j by s)
   | PExist(k, p) => PExist(open_at_kind j by k, open_at_pos_sig (j + 1) by p)

fun open_at_module j by =
let fun iter x = open_at_module j by x in
  fn MVar v              => MVar v
   | MStar               => MStar
   | MStatic ty          => MStatic(open_at_tycon j by ty)
   | MDynamic e          => MDynamic(open_at_term j by e)
   | MAbs(v, s, x)       => MAbs(v, open_at_sig j by s, open_at_module (j + 1) by x)
   | MApp(x, y)          => MApp(iter x, iter y)
   | MPair(x, y)         => MPair(iter x, iter y)
   | MProj(i, x)         => MProj(i, iter x)
   | MLet(v, e, x)       => MLet(v, open_at_term j by e, iter x)
   | MCirc l             => MCirc(open_at_lax_module j by l)
   | MLetModule(v, x, y) => MLetModule(v, iter x, open_at_module (j + 1) by y)
end

and open_at_lax_module j by =
  fn LRet m           => LRet(open_at_module j by m)
   | LSeal(m, s)      => LSeal(open_at_module j by m, open_at_sig j by s)
   | LBind(v, m, x)   => LBind(v, open_at_module j by m, open_at_lax_module (j + 1) by x)
   | LUnpack(v, e, x) => LUnpack(v, open_at_term j by e, open_at_lax_module (j + 1) by x)

and open_at_term j by =
let fun iter x = open_at_term j by x in
  fn EVar v             => EVar v
   | EStar              => EStar
   | EAbs(v, ty, x)     => EAbs(v, open_at_tycon j by ty, iter x)
   | EApp(x, y)         => EApp(iter x, iter y)
   | EPair(x, y)        => EPair(iter x, iter y)
   | EProj(i, x)        => EProj(i, iter x)
   | EGen(k, x)         => EGen(open_at_kind j by k, open_at_term (j + 1) by x)
   | EInst(x, ty)       => EInst(iter x, open_at_tycon j by ty)
   | EPack(w, x, k, ty) => EPack(open_at_tycon j by w, iter x, open_at_kind j by k, open_at_tycon (j + 1) by ty)
   | EUnpack(v, x, y)   => EUnpack(v, iter x, open_at_term (j + 1) by y)
   | EFix(ty, x)        => EFix(open_at_tycon j by ty, iter x)
   | ELet(v, x, y)      => ELet(v, iter x, iter y)
   | EExt m             => EExt(open_at_module j by m)
   | ELetLax(v, l, x)   => ELetLax(v, open_at_lax_module j by l, open_at_term (j + 1) by x)
end

structure Singleton : sig
  val kind : tycon -> kind -> kind
  val sign : tycon -> sign -> sign
end = struct
  open Std

  (* If both arguments are locally closed, so is the returned value. *)
  fun kind ty =
    fn KUnit        => KUnit
     | KType        => KSingleton ty
     | KSingleton _ => KSingleton ty
     | KArrow(x, y) =>
         let val fv = TVar.fresh () in
           KArrow(x, close_at_kind 0 fv $ kind (TApp(ty, TFree fv)) $ open_at_kind 0 (TFree fv) y)
         end
     | KProd(x, y) =>
         KProd(kind (TProj(Fst, ty)) x, kind (TProj(Snd, ty)) $ open_at_kind 0 (TProj(Fst, ty)) y)

  fun sign ty =
    fn SUnit        => SUnit
     | SStatic k    => SStatic $ kind ty k
     | SDynamic ty' => SDynamic ty'
     | SArrow(x, y) =>
         let val fv = TVar.fresh () in
           SArrow(x, close_at_sig 0 fv $ sign (TApp(ty, TFree fv)) $ open_at_sig 0 (TFree fv) y)
         end
     | SProd(x, y) =>
         SProd(sign (TProj(Fst, ty)) x, sign (TProj(Snd, ty)) $ open_at_sig 0 (TProj(Fst, ty)) y)
     | SMonad p => SMonad p (* I think this is correct. *)
end

structure Destructor = struct
  fun sig_arrow f =
    fn SArrow(x, y) => (x, y)
     | s            => raise (f s)

  fun sig_product f =
    fn SProd(x, y) => (x, y)
     | s           => raise (f s)

  fun sig_monad f =
    fn SMonad p => p
     | s        => raise (f s)

  fun sig_dynamic f =
    fn SDynamic ty => ty
     | s           => raise (f s)

  fun tycon_exist f =
    fn TExist(k, ty) => (k, ty)
     | ty            => raise (f ty)

  fun tycon_forall f =
    fn TForall(k, ty) => (k, ty)
     | ty             => raise (f ty)

  fun tycon_product f =
    fn TProd(x, y) => (x, y)
     | ty          => raise (f ty)

  fun tycon_arrow f =
    fn TArrow(x, y) => (x, y)
     | ty           => raise (f ty)

  fun kind_arrow f =
    fn KArrow(x, y) => (x, y)
     | k            => raise (f k)

  fun kind_product f =
    fn KProd(x, y) => (x, y)
     | k           => raise (f k)
end

structure Show = struct
  open Std
  open Pretty

  infix 5 <:>

  fun x <:> y = x <+> ":" <+> y

  fun show_index Fst = "fst"
    | show_index Snd = "snd"

  val show_base =
    fn BBool => "bool"
     | BInt  => "int"

  fun show_type n =
    fn TBound _   => raise Unreachable
     | TFree v    => TVar.show v
     | TStar      => "()"
     | TAbs(k, x) =>
         let val fv = TVar.fresh () in
           paren (n > 0) $
           "fun" <+> paren true (TVar.show fv <:> show_kind k) <+> "->" <+> show_type 0 (open_at_tycon 0 (TFree fv) x)
         end
     | TApp(x, y) =>
         paren (n > 4) $
         show_type 4 x <+> show_type 5 y
     | TPair(x, y)  => paren true $ show_type 0 x <> "," <+> show_type 0 y
     | TProj(i, x)  => paren (n > 4) $ show_index i <+> show_type 5 x
     | TUnit        => "1"
     | TBase b      => show_base b
     | TArrow(x, y) =>
         paren (n > 2) $
         show_type 3 x <+> "->" <+> show_type 2 y
     | TProd(x, y) =>
         paren (n > 3) $
         show_type 4 x <+> "*" <+> show_type 3 y
     | TForall(k, x) =>
         let val fv = TVar.fresh () in
           paren (n > 0) $
           "∀" <> TVar.show fv <:> show_kind k <> "." <+> show_type 0 (open_at_tycon 0 (TFree fv) x)
         end
     | TExist(k, x) =>
         let val fv = TVar.fresh () in
           paren (n > 0) $
           "∃" <> TVar.show fv <:> show_kind k <> "." <+> show_type 0 (open_at_tycon 0 (TFree fv) x)
         end

  and show_kind ty = case ty of
      KUnit         => "1"
    | KType         => "Type"
    | KSingleton ty => "S" <> paren true (show_type 0 ty)
    | KArrow(x, y)  =>
        let val fv = TVar.fresh () in
          "Π" <> TVar.show fv <:> show_kind x <> "." <+> show_kind (open_at_kind 0 (TFree fv) y)
        end
    | KProd(x, y)  =>
        let val fv = TVar.fresh () in
          "Σ" <> TVar.show fv <:> show_kind x <> "." <+> show_kind (open_at_kind 0 (TFree fv) y)
        end

  fun show_sig s =
    case s of
         SUnit        => "1"
       | SStatic k    => "(|" <> show_kind k <> "|)"
       | SDynamic ty  => "<|" <> show_type 0 ty <> "|>"
       | SArrow(x, y) =>
           let val fv = TVar.fresh () in
             "Π" <> TVar.show fv <:> show_sig x <> "." <+> show_sig (open_at_sig 0 (TFree fv) y)
           end
       | SProd(x, y) =>
           let val fv = TVar.fresh () in
             "Σ" <> TVar.show fv <:> show_sig x <> "." <+> show_sig (open_at_sig 0 (TFree fv) y)
           end
       | SMonad p => "○" <> paren true (show_pos_sig p)

  and show_pos_sig p =
    case p of
         PDown s => show_sig s
       | PExist(k, x) =>
           let val fv = TVar.fresh () in
             "∃" <> TVar.show fv <:> show_kind k <> "." <+> show_pos_sig (open_at_pos_sig 0 (TFree fv) x)
           end
end
