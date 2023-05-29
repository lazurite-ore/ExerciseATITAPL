module Pretty

open Syntax
open RuntimeData

let rec qualifierToString q =
    if q = Lin then "lin " else "" 

let rec typeToString ((q, pty): Type) =
    qualifierToString q
    +   match pty with
        | PTyBool -> "Bool"
        | PTyPair (t1, t2) -> sprintf "(%s * %s)" (typeToString t1) (typeToString t2)
        | PTyArr (t1, t2) -> sprintf "(%s -> %s)" (typeToString t1) (typeToString t2)

let rec termToString (ctx: Context) = function
    | TmVar (fi, i, n) ->
        if ctx.Length = n then
            Context.index2name fi i ctx
        else
            failwithf "bad index: %i in context: %A" i (List.map fst ctx)
    | TmBool (_, q, b) ->
        sprintf "%s%b" (qualifierToString q) b
    | TmAbs (_, q, x, tyT1, t2) ->
        let ctx' = Context.addName x ctx
        sprintf "%s(\\%s:%s.%s)" (qualifierToString q) x (typeToString tyT1) (termToString ctx' t2)
    | TmApp (_, t1, t2) ->
        sprintf "%s %s" (termToString ctx t1) (termToString ctx t2)
    | TmIfElse (_, t1, t2, t3) ->
        sprintf "(if %s then %s else %s)" (termToString ctx t1) (termToString ctx t2) (termToString ctx t3)
    | TmPair (_, q, t1, t2) ->
        sprintf "%s<%s,%s>" (qualifierToString q) (termToString ctx t1) (termToString ctx t2)
    | TmSplit (_, t1, x, y, t2) ->
        let ctx' = ctx |> Context.addName x |> Context.addName y
        sprintf "let (%s, %s) = %s in %s" x y (termToString ctx t1) (termToString ctx' t2)

let rec evalToString (ctx: Context) = function
    | ETmVar (i, n) ->
        if ctx.Length = n then
            Context.index2name None i ctx
        else
            failwithf "bad index: %i in context: %A" i (List.map fst ctx)
    | ETmBool (q, b) ->
        sprintf "%s%b" (qualifierToString q) b
    | ETmAbs (q, x, tyT1, t2) ->
        let ctx' = Context.addName x ctx
        sprintf "%s(\\%s:%s.%s)" (qualifierToString q) x (typeToString tyT1) (evalToString ctx' t2)
    | ETmApp (t1, t2) ->
        sprintf "%s %s" (evalToString ctx t1) (evalToString ctx t2)
    | ETmIfElse (t1, t2, t3) ->
        sprintf "(if %s then %s else %s)" (evalToString ctx t1) (evalToString ctx t2) (evalToString ctx t3)
    | ETmPair (q, t1, t2) ->
        sprintf "%s<%s, %s>" (qualifierToString q) (evalToString ctx t1) (evalToString ctx t2)
    | ETmSplit (t1, x, y, t2) ->
        let ctx' = ctx |> Context.addName x |> Context.addName y
        sprintf "let (%s, %s) = %s in %s" x y (evalToString ctx t1) (evalToString ctx' t2)
    | ETmPtr ptr ->
        sprintf "!%i" ptr

let rec storeToString (s: Store) =
    match s with
    | (ptr, v) :: s' -> sprintf "  [%i]: %s\n%s" ptr (evalToString [] v) (storeToString s')
    | [] -> ""