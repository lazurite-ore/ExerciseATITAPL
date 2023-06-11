open FSharp.Text.Lexing
open Syntax
open Semantic

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
        let ctx = List.rev [
            "A", TyVarBind (KdStar None)
            "Nat", TyVarBind (KdStar None)
            "zero", VarBind (TyVar (None, 0, 2))
            "succ", VarBind (TyPi (None, "n", TyVar (None, 1, 3), TyVar (None, 2, 4)))
            "Vector", TyVarBind (KdPi (None, "n", TyVar (None, 2, 4), KdStar None))
            "nil", VarBind (TyApp (None, TyVar (None, 0, 5), TmVar (None, 2, 5)))
            "cons", VarBind (TyPi (None, "n", TyVar (None, 4, 6),
                    TyPi (None, "x", TyVar (None, 6, 7),
                        TyPi (None, "v", TyApp (None, TyVar (None, 3, 8), TmVar (None, 1, 8)),
                            TyApp (None, TyVar (None, 4, 9), TmApp (None, TmVar (None, 5, 9), TmVar (None, 2, 9)))
                ))))
        ]

        let t = parseString str ctx

        t
        |> Pretty.termToString ctx
        |> printfn "term: %s"

        let ty = typeOf ctx t

        let ctx' = collectOutsideDef ctx t

        ty
        |> Pretty.typeToString ctx'
        |> printfn "type: %s"

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

test false "let mkthree = \\x:A.\\y:A.\\z:A.cons (succ (succ zero)) z (cons (succ zero) y (cons zero x nil)) in mkthree"