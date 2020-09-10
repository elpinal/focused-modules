open Std

datatype dyn_var
  = E of var
  | M of mvar
  | Wildcard

val show_var =
  fn E v => v
   | M v => v
   | Wildcard => "_"

datatype dyn_term
  = Var of dyn_var
  | Star
  | Abs of dyn_var * dyn_term
  | App of dyn_term * dyn_term
  | Pair of dyn_term * dyn_term
  | Proj of index * dyn_term
  | Fix of dyn_term
  | Let of dyn_var * dyn_term * dyn_term

fun Pack x = x
val Unpack = Let

(* Thanks to the value restriction. *)
fun Gen x = x
fun Inst x = x

structure Dyn = struct
  open Pretty

  fun show n e =
    case e of
         Var v     => show_var v
       | Star      => "()"
       | Abs(v, x) => paren (n > 0) $ "fun" <+> show_var v <+> "->" <+> show 0 x
       | App(x, y) => paren (n > 4) $ show 4 x <+> show 5 y
       | Pair(x, y) => paren true $ show 0 x <> "," <+> show 0 y
       | Proj(i, x) => paren (n > 4) $ Show.show_index i <+> show 5 x
       | Fix x      => paren (n > 4) $ "fix" <+> show 5 x
       | Let(v, x, y) => paren (n > 0) $ "let" <+> show_var v <+> "=" <+> show 0 x <+> "in" <+> show 0 y
end

(* Phase-split and take the second (i.e., dynamic) component. The result is type-erased. *)
fun snd_module m = case m of
    MVar v              => Var $ M v
  | MStar               => Star
  | MStatic _           => Star
  | MDynamic e          => translate_term e
  | MAbs(v, _, x)       => Gen $ Abs(M v, snd_module x)
  | MApp(x, y)          => App(Inst $ snd_module x, snd_module y)
  | MPair(x, y)         => Pair(snd_module x, snd_module y)
  | MProj(i, x)         => Proj(i, snd_module x)
  | MLet(v, e, x)       => Let(E v, translate_term e, snd_module x)
  | MCirc l             => translate_lax_module l
  | MLetModule(v, x, y) => Let(M v, snd_module x, snd_module y)

(*
* Static components of lax modules are not statically well-determined.
* However, once they are bound to variables via `bind`,
* they have non-trivial static components.
* Thus, this function returns an existential package.
* *)
and translate_lax_module l = case l of
    LRet m           => Pack $ snd_module m (* Pack with some fully transparent signature. *)
  | LSeal(m, _)      => Pack $ snd_module m
  | LBind(v, m, x)   => Unpack(M v, snd_module m, translate_lax_module x)
  | LUnpack(v, e, x) => Unpack(E v, translate_term e, translate_lax_module x)

and translate_term (e : term) : dyn_term = case e of
    EVar v            => Var $ E v
  | EStar             => Star
  | EAbs(v, _, x)     => Abs(E v, translate_term x)
  | EApp(x, y)        => App(translate_term x, translate_term y)
  | EPair(x, y)       => Pair(translate_term x, translate_term y)
  | EProj(i, x)       => Proj(i, translate_term x)
  | EGen(_, x)        => Gen $ translate_term x
  | EInst(x, _)       => Inst $ translate_term x
  | EPack(_, x, _, _) => Pack $ translate_term x
  | EUnpack(v, x, y)  => Unpack(E v, translate_term x, translate_term y)
  | EFix(_, x)        => Fix $ translate_term x
  | ELet(v, x, y)     => Let(E v, translate_term x, translate_term y)
  | EExt m            => snd_module m
  | ELetLax(v, l, x)  => Unpack(M v, translate_lax_module l, translate_term x)

exception RuntimeError of string

local
  structure Env = struct
    structure Map = BinarySearchMap (struct
      type t = dyn_var

      fun compare (E x, E y) = String.compare (x, y)
        | compare (M x, M y) = String.compare (x, y)
        | compare (E _, M _) = LESS
        | compare (M _, E _) = GREATER
        | compare (Wildcard, Wildcard) = EQUAL
        | compare (_, Wildcard)        = LESS
        | compare (Wildcard, _)        = GREATER
    end)

    fun lookup v env =
      case Map.lookup v env of
           NONE   => raise RuntimeError "unbound variable"
         | SOME x => x
  end
in
  fun eval env =
    fn Var v => Env.lookup v env
     | Star  => Star
     | Abs(v, x) => Abs(v, x)
     | App(x, y) =>
         let in
           case eval env x of
                Abs(v, x') => eval (Env.Map.insert v (eval env y) env) x'
              | _          => raise RuntimeError "not function"
         end
     | Pair(x, y) => Pair(eval env x, eval env y)
     | Proj(i, x) =>
         let in
           case eval env x of
                Pair(x, y) => index i (x, y)
              | _          => raise RuntimeError "not pair"
         end
     | Fix x => eval env $ App(x, Abs(Wildcard, Fix x))
     | Let(v, x, y) => eval (Env.Map.insert v (eval env x) env) y

  val evaluate = eval Env.Map.empty
end
