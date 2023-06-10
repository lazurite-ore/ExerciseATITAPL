module Pretty

open Syntax

let rec typeToString (ctx: Context) = function
    | TyUnit _ ->
        "Unit"
    | TyVar (fi, i, n) ->
        if ctx.Length = n then
            Context.index2name fi i ctx
        else
            failwithf "bad index: %i in context: %A" i (List.map fst ctx)
    | TyPi (_, x, tyT1, tyT2) ->
        let ctx' = Context.addName x ctx
        sprintf "(||%s:%s.%s)" x (typeToString ctx tyT1) (typeToString ctx' tyT2)
    | TyApp (_, ty, t) ->
        sprintf "%s (%s)" (typeToString ctx ty) (termToString ctx t)
and termToString (ctx: Context) = function
    | TmUnit _ ->
        "()"
    | TmVar (fi, i, n) ->
        if ctx.Length = n then
            Context.index2name fi i ctx
        else
            failwithf "bad index: %i in context: %A" i (List.map fst ctx)
    | TmAbs (_, x, tyT1, t2) ->
        let ctx' = Context.addName x ctx
        sprintf "(\\%s:%s.%s)" x (typeToString ctx tyT1) (termToString ctx' t2)
    | TmApp (_, t1, t2) ->
        sprintf "%s (%s)" (termToString ctx t1) (termToString ctx t2)
    | TmLet (_, x, t1, t2) ->
        let ctx' = Context.addName x ctx
        sprintf "let %s = %s in\n      %s" x (termToString ctx t1) (termToString ctx' t2)
and kindToString (ctx: Context) = function
    | KdStar _ -> "*"
    | KdPi (_, x, tyT1, k) -> sprintf "(||%s:%s.%s)" x (typeToString ctx tyT1) (kindToString ctx k)