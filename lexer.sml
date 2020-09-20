structure LexerError = struct
  exception Illegal of char option
  exception IllegalBackSlash of string
end

structure Lexer = MakeLexer (struct
  structure Streamable = StreamStreamable
  structure Arg = struct
    type symbol = char
    val ord = Char.ord

    datatype t = datatype Token.token
    type t = t Streamable.t

    type self = { lex : symbol Streamable.t -> t }
    type info = {
      match : symbol list,
      len : int,
      start : symbol Streamable.t,
      follow : symbol Streamable.t,
      self : self
    }

    open LexerError

    fun eager_follow ({self, follow, ...} : info) tok =
    let open Stream in
      eager (Cons(tok, #lex self follow))
    end

    fun stream_head s =
      case Stream.front s of
           Stream.Nil        => NONE
         | Stream.Cons(x, _) => SOME(x)

    fun illegal ({follow, ...} : info) = raise Illegal(stream_head follow)
    fun eof _ = Stream.fromList []

    fun asterisk info = eager_follow info STAR
    fun colon info = eager_follow info COLON
    fun comma info = eager_follow info COMMA
    fun dot info = eager_follow info DOT
    fun slash info = eager_follow info SLASH
    fun equal info = eager_follow info EQUAL
    fun rarrow info = eager_follow info RARROW
    fun larrow info = eager_follow info LARROW
    fun seal info = eager_follow info SEAL

    fun lparen info = eager_follow info LPAREN
    fun rparen info = eager_follow info RPAREN
    fun lbrack info = eager_follow info LBRACK
    fun rbrack info = eager_follow info RBRACK
    fun lwhiteparen info = eager_follow info LWHITEPAREN
    fun rwhiteparen info = eager_follow info RWHITEPAREN
    fun lwhiteangle info = eager_follow info LWHITEANGLE
    fun rwhiteangle info = eager_follow info RWHITEANGLE

    fun one info = eager_follow info ONE

    fun whitespace ({self, follow, ...} : info) = #lex self follow

    fun quote_ident ({match, self, follow, ...} : info) =
      Stream.lazy (fn () => Stream.Cons(QUOTE_IDENT(String.implode (List.tl match)), #lex self follow))

    fun backslash_ident ({match, self, follow, ...} : info) =
    let val f =
      fn "Pi"     => CAP_PI
       | "Sigma"  => CAP_SIGMA
       | s        => raise IllegalBackSlash(s)
    in
      Stream.lazy (fn () => Stream.Cons(f (String.implode (List.tl match)), #lex self follow))
    end

    fun upper_ident ({match, self, follow, ...} : info) =
    let val f =
      fn "Type"   => CAP_TYPE
       | "Ext"    => CAP_EXT
       | "S"      => S
       | s        => UPPER_IDENT s
    in
      Stream.lazy (fn () => Stream.Cons(f (String.implode match), #lex self follow))
    end

    fun lower_ident ({match, self, follow, ...} : info) =
    let val f =
      fn "fun"    => FUN
       | "fst"    => FST
       | "snd"    => SND
       | "forall" => FORALL
       | "exist"  => EXIST
       | "poly"   => POLY
       | "pack"   => PACK
       | "unpack" => UNPACK
       | "as"     => AS
       | "in"     => IN
       | "fix"    => FIX
       | "let"    => LET
       | "circ"   => CIRC
       | "ret"    => RET
       | "bind"   => BIND
       | "bool"   => BOOL
       | "int"    => INT
       | s        => LOWER_IDENT s
    in
      Stream.lazy (fn () => Stream.Cons(f (String.implode match), #lex self follow))
    end
  end
end)
