module Typing

open Syntax



let rec typeOf (ctx1: Context) (t: Term) : Type * Context =
    match t with
    | TmBool (_, q, _) ->
        ((q, PTyBool), ctx1)
    | TmVar (fi, i, _) ->
        Context.getType fi i ctx1
    | TmIfElse (fi, t1, t2, t3) ->
        let ((q, ptyT1), ctx2) = typeOf ctx1 t1

        if ptyT1 = PTyBool then
            
            let (tyT, ctx3) = typeOf ctx2 t2
            let (tyT', ctx3') = typeOf ctx2 t3

            if tyT <> tyT' then
                error fi "mismatch type of branches"

            if ctx3 <> ctx3' then
                error fi "mismatch context of branches"
            
            (tyT, ctx3)
        else
            error fi "expect Bool type"

    | TmPair (fi, q, t1, t2) ->
        
        let (tyT1, ctx2) = typeOf ctx1 t1
        let (tyT2, ctx3) = typeOf ctx2 t2

        if Type.checkQ q tyT1 then
            if Type.checkQ q tyT2 then
                ((q, PTyPair (tyT1, tyT2)), ctx3)
            else
                error fi "q <t1, t2> fail to check qualifier q on t"2
        else
            error fi "q <t1, t2> fail to check qualifier q on t1"

    | TmSplit (fi, t1, x, y, t2) ->
        let (tyTPair, ctx2) = typeOf ctx1 t1
        
        match tyTPair with
        | (q, PTyPair (tyT1, tyT2)) ->
            let (tyT, ctx3) = typeOf (ctx2 |> Context.addVar x tyT1 |> Context.addVar y tyT2) t2
            (tyT, Context.difference fi ctx3 [(x, VarBind tyT1); (y, VarBind tyT2)])
        | _ ->
            error fi "expect Pair type"
        
    | TmAbs (fi, q, x, tyT1, t2) ->

        if x = "y" then
            ()

        let (tyT2, ctx2) = typeOf (Context.addVar x tyT1 ctx1) t2

        let ctx2' = Context.difference fi ctx2 [(x, VarBind tyT1)]

        if q = Un && ctx1 <> ctx2' then
            error fi "unrestricted function should not contain linear variables"

        ((q, PTyArr(tyT1, tyT2)), ctx2')

    | TmApp (fi, t1, t2) ->
        let (tyT1, ctx2) = typeOf ctx1 t1
        match tyT1 with
        | (q, PTyArr (tyT11, tyT12)) ->
            
            let (tyT2, ctx3) = typeOf ctx2 t2
            if tyT2 = tyT11 then
                (tyT12, ctx3)
            else
                error fi "mismatch argument type"
        | _ ->
            error fi "expect Arr type"