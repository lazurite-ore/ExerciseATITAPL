open System.IO
open FSharp.Text.Lexing
open Syntax

let parseString str =
    
    let tokens =
        let lexbuf = LexBuffer<char>.FromString str
        seq {
            while not lexbuf.IsPastEndOfStream do
                yield (Lexer.token lexbuf).GetType().Name
        }
    
    tokens
    |> Seq.fold (fun s e -> s + " " + e) ""
    |> printfn "%s"

    let lexbuf = LexBuffer<char>.FromString str

    Parser.start Lexer.token lexbuf

let test debug str =

    try
        let t = parseString str []

        t
        |> Pretty.tm2str []
        |> printfn "term: %s"

        let ty = Semantic.typeOf [] t

        let ctx = Semantic.collectOuterTypeDefs [] t

        ty
        |> Pretty.ty2str ctx
        |> printfn "type: %s"

        //let (s, et) = Evaluation.eval debug t

        //et
        //|> Pretty.evalToString []
        //|> printfn "eval: %s"

        //s
        //|> Pretty.storeToString
        //|> printfn "store: {\n%s}"

        //printfn ""
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

System.Console.OutputEncoding <- System.Text.Encoding.UTF8

// it doesn't work wtf
test false "let Pair = ∀X.∀Y.∀R.(X→Y→R)→R in λx:X.x"
