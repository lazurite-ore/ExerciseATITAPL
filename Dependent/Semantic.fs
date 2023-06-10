module Semantic

open Syntax

let rec whnf1 = function
    | TmApp (fi, TmAbs (fi', x, tyT1, t1), t2) ->
        tmSubstTop t2 t1
    | TmApp (fi, t1, t2) ->
        let t1' = whnf1 t1
        TmApp (fi, t1', t2)
    | term ->
        term
and whnf (term: Term) : Term =
    let term' = whnf1 term
    if term' = term then
        term'
    else
        whnf term'

let rec whnfType1 ctx = function
    | TyApp (fi, TyPi (fi', x, tyT11, tyT12), t2) ->
        let tyT2 = typeOf ctx t2
        if tyEquiv ctx tyT11 tyT2 then
            tyTermSubstTop t2 tyT12
        else
            error fi "mismatch type"
    | TyApp (fi, ty, t) ->
        let ty' = whnfType1 ctx ty
        TyApp (fi, ty', t)
    | ty ->
        ty
and whnfType ctx ty =
    let ty' = whnfType1 ctx ty
    if ty' = ty then
        ty'
    else
        whnfType1 ctx ty'

and tmWhEquiv (ctx: Context) (term1: Term) (term2: Term) : bool =
    match term1, term2 with
    | TmUnit _, TmUnit _ ->
        true
    | TmVar (_, i, n), TmVar (_, i', n') ->
        i = i' && n = n'
    | TmApp (_, s1, t1), TmApp (_, s2, t2) ->
        tmWhEquiv ctx s1 s2 && tmWhEquiv ctx t1 t2
    | TmAbs (_, x, tyS, t1), TmAbs (_, x', tyS', t2) ->
        x = x' && tyEquiv ctx tyS tyS' && tmEquiv ctx t1 t2
    | s, TmAbs (fi, x, tyS, t) ->
        let ctx' = Context.addVar x tyS ctx
        tmEquiv ctx' (TmApp (None, s, TmVar (None, 0, ctx'.Length))) t
    | TmAbs (_, x, tyS, s), t ->
        let ctx' = Context.addVar x tyS ctx
        tmEquiv ctx' s (TmApp (None, t, TmVar (None, 0, ctx'.Length)))
    | _ ->
        false
and tmEquiv (ctx: Context) (t1: Term) (t2: Term) : bool =
    tmWhEquiv ctx (whnf t1) (whnf t2)
and tyEquiv (ctx: Context) (type1: Type) (type2: Type) : bool =
    match type1, type2 with
    | TyUnit _, TyUnit _ ->
        true
    | TyVar (_, i, n), TyVar (_, i', n') ->
        i = i' && n = n'
    | TyPi (_, x, tyS1, tyS2), TyPi (_, x', tyT1, tyT2) ->
        x = x' && tyEquiv ctx tyS1 tyT1 && tyEquiv (Context.addVar x tyT1 ctx) tyS2 tyT2
    | TyApp (_, tyS1, t1), TyApp (_, tyS2, t2) ->
        tyEquiv ctx tyS1 tyS2 && tmEquiv ctx t1 t2
    | _ ->
        false
and kdEquiv (ctx: Context) (kind1: Kind) (kind2: Kind) : bool =
    match kind1, kind2 with
    | KdStar _, KdStar _ ->
        true
    | KdPi (_, x, tyT1, k1), KdPi (_, x', tyT2, k2) ->
        x = x' && tyEquiv ctx tyT1 tyT2 && kdEquiv (Context.addVar x tyT1 ctx) k1 k2
    | _ ->
        false

and typeOf1 (ctx: Context) (t: Term) : Type =
    match t with
    | TmUnit fi ->
        TyUnit fi
    | TmVar (fi, i, n) ->
        Context.getType fi i ctx
    | TmAbs (fi, x, tyT1, t2) ->
        if isProperType ctx tyT1 then
            let tyT2 = typeOf (Context.addVar x tyT1 ctx) t2
            TyPi (fi, x, tyT1, tyT2)
        else
            error (tyInfo tyT1) "expect proper type"
    | TmApp (fi, t1, t2) ->
        match typeOf ctx t1 with
        | TyPi (fi, x, tyS1, tyT) ->
            let tyS1' = whnfType ctx tyS1
            let tyS2 = whnfType ctx (typeOf ctx t2)
            if tyEquiv ctx tyS1' tyS2 then
                tyTermSubstTop t2 tyT
            else
                error fi "mismatch type"
        | _ ->
            error fi "expect pi type"
    | TmLet (fi, x, t1, t2) ->
        let tyT1 = typeOf ctx t1
        if isProperType ctx tyT1 then
            typeOf (Context.addVar x tyT1 ctx) t2
        else
            error (tmInfo t1) "expect proper type"
and typeOf (ctx: Context) (t: Term) : Type =
    whnfType ctx (typeOf1 ctx t)
and kindOf (ctx: Context) (ty: Type) : Kind =
    match ty with
    | TyUnit fi ->
        KdStar fi
    | TyVar (fi, i, n) ->
        Context.getKind fi i ctx
    | TyPi (fi, x, tyT1, tyT2) ->
        let str = Pretty.typeToString ctx tyT1
        if isProperType ctx tyT1 then
            kindOf (Context.addVar x tyT1 ctx) tyT2
        else
            error fi "expect proper type"
    | TyApp (fi, tyS1, t2) ->
        match kindOf ctx tyS1 with
        | KdPi (fi, x, tyT1, k) ->
            let tyT2 = typeOf ctx t2
            if tyEquiv ctx tyT1 tyT2 then
                kdTermSubstTop t2 k
            else
                error fi "mismatch type"
        | _ ->
            error fi "expect Kind Pi"

and isProperType ctx ty =
    match kindOf ctx ty with
    | KdStar _ -> true
    | KdPi _ -> false
and isWellFormed (ctx: Context) (k: Kind) : bool =
    match k with
    | KdStar _ ->
        true
    | KdPi (_, x, tyT1, k2) when isProperType ctx tyT1 ->
        isWellFormed (Context.addVar x tyT1 ctx) k2
    | KdPi _ ->
        false

