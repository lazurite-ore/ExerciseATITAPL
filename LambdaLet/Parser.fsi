// Signature file for parser generated by fsyacc
module Parser
type token = 
  | ONE of (Info)
  | TWO of (Info)
  | LSQUARE of (Info)
  | RSQUARE of (Info)
  | COMMA of (Info)
  | EQUAL of (Info)
  | LPAREN of (Info)
  | RPAREN of (Info)
  | SEMICOLON of (Info)
  | SEMICOLON2 of (Info)
  | LCURLY of (Info)
  | RCURLY of (Info)
  | MUL of (Info)
  | ARROW of (Info)
  | DARROW of (Info)
  | DOT of (Info)
  | STAR of (Info)
  | LAMBDA of (Info)
  | FORALL of (Info)
  | LET of (Info)
  | IN of (Info)
  | LCID of (Info * string)
  | UCID of (Info * string)
  | EOF
type tokenId = 
    | TOKEN_ONE
    | TOKEN_TWO
    | TOKEN_LSQUARE
    | TOKEN_RSQUARE
    | TOKEN_COMMA
    | TOKEN_EQUAL
    | TOKEN_LPAREN
    | TOKEN_RPAREN
    | TOKEN_SEMICOLON
    | TOKEN_SEMICOLON2
    | TOKEN_LCURLY
    | TOKEN_RCURLY
    | TOKEN_MUL
    | TOKEN_ARROW
    | TOKEN_DARROW
    | TOKEN_DOT
    | TOKEN_STAR
    | TOKEN_LAMBDA
    | TOKEN_FORALL
    | TOKEN_LET
    | TOKEN_IN
    | TOKEN_LCID
    | TOKEN_UCID
    | TOKEN_EOF
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_kind
    | NONTERM_atomicType
    | NONTERM_appType
    | NONTERM_type
    | NONTERM_absTerm
    | NONTERM_typeAbsTerm
    | NONTERM_atomicTerm
    | NONTERM_projTerm
    | NONTERM_appTerm
    | NONTERM_term
    | NONTERM_start
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (Start) 