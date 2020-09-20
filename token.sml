structure Token = struct
  datatype token
    = ONE
    | CAP_TYPE
    | CAP_EXT
    | CAP_PI
    | CAP_SIGMA
    | S
    | FUN
    | FST
    | SND
    | FORALL
    | EXIST
    | POLY
    | PACK
    | UNPACK
    | AS
    | IN
    | FIX
    | LET
    | CIRC
    | RET
    | BIND
    | BOOL
    | INT

    | LOWER_IDENT of string
    | UPPER_IDENT of string
    | QUOTE_IDENT of string
    | NUMBER of int

    | LPAREN
    | RPAREN
    | LBRACK
    | RBRACK
    | LWHITEPAREN
    | RWHITEPAREN
    | LWHITEANGLE
    | RWHITEANGLE

    | COLON
    | SEAL
    | RARROW
    | LARROW
    | STAR
    | EQUAL
    | SLASH
    | DOT
    | COMMA

  val show =
    fn ONE       => "1"
     | CAP_TYPE  => "Type"
     | CAP_EXT   => "Ext"
     | CAP_PI    => "Π"
     | CAP_SIGMA => "Σ"
     | S         => "S"
     | FUN       => "fun"
     | FST       => "fst"
     | SND       => "snd"
     | FORALL    => "forall"
     | EXIST     => "exist"
     | POLY      => "poly"
     | PACK      => "pack"
     | UNPACK    => "unpack"
     | AS        => "as"
     | IN        => "in"
     | FIX       => "fix"
     | LET       => "let"
     | CIRC      => "circ"
     | RET       => "ret"
     | BIND      => "bind"
     | BOOL      => "bool"
     | INT       => "int"

     | LOWER_IDENT s => s
     | UPPER_IDENT s => s
     | QUOTE_IDENT s => "'" ^ s
     | NUMBER n      => Int.toString n (* What about negative integers? *)

     | LPAREN => "("
     | RPAREN => ")"
     | LBRACK => "["
     | RBRACK => "]"
     | LWHITEPAREN => "(|"
     | RWHITEPAREN => "|)"
     | LWHITEANGLE => "<|"
     | RWHITEANGLE => "|>"

     | COLON  => ":"
     | SEAL   => ":>"
     | RARROW => "->"
     | LARROW => "<-"
     | STAR   => "*"
     | EQUAL  => "="
     | SLASH  => "/"
     | DOT    => "."
     | COMMA  => ","
end
