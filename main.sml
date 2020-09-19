open Std
open Pretty

datatype 'a result
  = Ok of 'a
  | Err of string

exception UnicodeError

fun handle_utf8 (w : word, cs : char Stream.stream) : char Stream.stream =
let open Stream in
  case SpecialChar.classify w of
       SOME x => cs @ Stream.fromList (String.explode $ SpecialChar.as_ascii x)
     | NONE   => cs @ (eager $ Cons(Char.chr $ Word.toInt w, eager Nil))
     handle Overflow => raise UnicodeError
          | Chr      => raise UnicodeError
end

fun process_stream (stream : char Stream.stream) : char Stream.stream =
let open Stream in
  stream
  |> toList
  |> String.implode
  |> Utf8.fromString
  |> Utf8.foldl handle_utf8 (eager Nil)
end handle Chr => raise UnicodeError

fun main stream =
let
  val m : module = #1 $ Parser.parse $ Lexer.lex $ process_stream stream
  val s : sign = M.synthesize_signature Env.initial m
  val e : dyn_term = snd_module m
  val e : dyn_term = evaluate e
in
  Ok(s, e)
end
  handle ParserError.UnexpectedToken NONE     => Err "parse error: unexpected end of file"
       | ParserError.UnexpectedToken (SOME t) => Err ("parse error: unexpected token:" <+> Token.show t)
       | ParserError.ForbiddenExistentialSignature =>
           Err "parse error: existential signatures are forbidden to write for decidability reason"
       | Env.Module.Unbound v => Err ("unbound module variable:" <+> v)
       | Env.Val.Unbound v    => Err ("unbound value variable:" <+> v)
       | Env.Type.Unbound v   => Err ("unbound type variable:" <+> TVar.show v)
       | SK.CannotApplyNonFunction k =>
           Err ("cannot apply a type of non-function kind:" <+> Show.show_kind k)
       | SK.CannotProjectNonProduct k =>
           Err ("cannot project out from a type of non-product kind:" <+> Show.show_kind k)
       | SK.KindMismatch(x, y) =>
           Err ("kind mismatch:" <+> Show.show_kind x <+> "vs." <+> Show.show_kind y)
       | SK.PathMismatch(_, x, y) =>
           Err ("path mismatch:" <+> Show.show_type 0 x <+> "vs." <+> Show.show_type 0 y)
       | SK.NotSubkind(x, y) =>
           Err ("the following subkind relation does not hold:" <+> Show.show_kind x <+> "<:" <+> Show.show_kind y)
       | SK.VarMismatch(x, y) =>
           Err ("type variable mismatch:" <+> TVar.show x <+> "vs." <+> TVar.show y)
       | M.CannotExtractNonDynamic s =>
           Err ("cannot extract a term from a non-dynamic-atomic module:" <+> Show.show_sig s)
       | M.CannotApplyNonFunctor s =>
           Err ("cannot apply a module of non-functor signature:" <+> Show.show_sig s)
       | M.CannotProjectNonProduct s =>
           Err ("cannot project out from a module of non-product signature:" <+> Show.show_sig s)
       | M.CannotBindNonMonad s =>
           Err ("cannot bind a module of non-monadic signature:" <+> Show.show_sig s)
       | M.NotSubsignature(x, y) =>
           Err ("the following subsignature relation does not hold:" <+> Show.show_sig x <+> "<:" <+> Show.show_sig y)
       | M.ValueRestriction _ =>
           Err "value restriction: the body of a polymorphic function must be a syntactic value"
       | M.CannotApplyNonFunction ty =>
           Err ("cannot apply a term of non-function type:" <+> Show.show_type 0 ty)
       | M.CannotProjectNonProductType ty =>
           Err ("cannot project out from a term of non-product type:" <+> Show.show_type 0 ty)
       | M.CannotUnpackNonExist ty =>
           Err ("cannot unpack a term of non-existential type:" <+> Show.show_type 0 ty)
       | M.CannotInstNonUniversal ty =>
           Err ("cannot instantiate a term of non-universal type:" <+> Show.show_type 0 ty)
       | LexerError.Illegal (SOME c) => Err ("illegal character:" <+> Char.toString c)
