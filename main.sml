open Std
open Pretty

datatype 'a result
  = Ok of 'a
  | Err of string

fun main stream =
let
  val m : module = #1 $ Parser.parse $ Lexer.lex stream
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
       | M.NotSubsignature(x, y) =>
           Err ("the following subsignature relation does not hold:" <+> Show.show_sig x <+> "<:" <+> Show.show_sig y)
       | SK.PathMismatch(_, x, y) =>
           Err ("path mismatch:" <+> Show.show_type 0 x <+> "vs." <+> Show.show_type 0 y)
       | SK.NotSubkind(x, y) =>
           Err ("the following subkind relation does not hold:" <+> Show.show_kind x <+> "<:" <+> Show.show_kind y)
       | SK.VarMismatch(x, y) =>
           Err ("type variable mismatch:" <+> TVar.show x <+> "vs." <+> TVar.show y)
       | M.ValueRestriction _ =>
           Err "value restriction: the body of a polymorphic function must be a syntactic value"
       | LexerError.Illegal (SOME c) => Err ("illegal character:" <+> Char.toString c)
       | M.CannotApplyNonFunction ty =>
           Err ("cannot apply a term of non-function type:" <+> Show.show_type 0 ty)
       | M.CannotExtractNonDynamic s =>
           Err ("cannot extract a term from a non-dynamic-atomic module:" <+> Show.show_sig s)
