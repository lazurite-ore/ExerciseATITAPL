﻿open FSharp.Text.Lexing
open Syntax


let parseString str =
    
    //let tokens =
    //    let lexbuf = LexBuffer<char>.FromString str
    //    seq {
    //        while not lexbuf.IsPastEndOfStream do
    //            yield (Lexer.token lexbuf).GetType().Name
    //    }
    
    //tokens
    //|> Seq.fold (fun s e -> s + " " + e) ""
    //|> printfn "%s"

    let lexbuf = LexBuffer<char>.FromString str

    Parser.start Lexer.token lexbuf

let test str =

    try
        let t = parseString str

        t
        |> Pretty.termToString []
        |> printfn "term: %s"

        let (ty, _) = Typing.typeOf [] t

        ty
        |> Pretty.typeToString
        |> printfn "type: %s"

        printfn ""
    with
    | CompilerError (fi, msg) ->
        printfn "[CompilerError] %s" msg
        match fi with
        | Some ti ->
            let len = max (ti.End.Column - ti.Start.Column) 1
            let line = str.Split('\n')[ti.Start.Line]
            printfn "%s" line
            printfn "%s%s" (String.init (ti.Start.Column) (fun _ -> " ")) (String.init len (fun _ -> "^"))
        | None ->
            printfn "%s" msg


test "lin \\x:lin Bool.x"

test "lin \\x:lin Bool.lin true"

test "lin \\x:lin Bool.(lin \\f:un (un Bool -> lin Bool).lin true) (un \\y:un Bool.x)"

test "lin \\x:lin Bool.((lin \\f:un (un Bool -> lin Bool).lin <f (un true),f (un true)>)) (un \\y:un Bool.x))"
