// Signature file for parser generated by fsyacc
module Parser
type token = 
  | LAMBDA of (Info)
  | SEMICOLON of (Info)
  | DOT of (Info)
  | AT of (Info)
  | ARROW of (Info)
  | STAR of (Info)
  | LPAREN of (Info)
  | RPAREN of (Info)
  | COMMA of (Info)
  | EQUAL of (Info)
  | LESS of (Info)
  | GREATER of (Info)
  | LIN of (Info)
  | UN of (Info)
  | TRUE of (Info)
  | FALSE of (Info)
  | LET of (Info)
  | IN of (Info)
  | IF of (Info)
  | THEN of (Info)
  | ELSE of (Info)
  | LCID of (Info * string)
  | UCID of (Info * string)
  | EOF
type tokenId = 
    | TOKEN_LAMBDA
    | TOKEN_SEMICOLON
    | TOKEN_DOT
    | TOKEN_AT
    | TOKEN_ARROW
    | TOKEN_STAR
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_COMMA
    | TOKEN_EQUAL
    | TOKEN_LESS
    | TOKEN_GREATER
    | TOKEN_LIN
    | TOKEN_UN
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_LET
    | TOKEN_IN
    | TOKEN_IF
    | TOKEN_THEN
    | TOKEN_ELSE
    | TOKEN_LCID
    | TOKEN_UCID
    | TOKEN_EOF
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_qualifier
    | NONTERM_preType
    | NONTERM_type
    | NONTERM_boolValue
    | NONTERM_boolTerm
    | NONTERM_lambdaValue
    | NONTERM_lambdaTerm
    | NONTERM_pairValue
    | NONTERM_pairTerm
    | NONTERM_atomicTerm
    | NONTERM_appTerm
    | NONTERM_term
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (Term) 
