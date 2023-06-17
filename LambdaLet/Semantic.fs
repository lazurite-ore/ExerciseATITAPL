module Semantic

open Syntax

exception NoRuleApply

let rec weakHead (ctx: Context) = function
    | TyApp (_, TyAbs (_, tyX, k11, tyT12), tyT2) ->
        Type.substTop tyT2 tyT12
    | TyVar (fi, i, n) ->
        let (k, tyT) = Context.getDef fi i ctx
        tyT
    | TyApp (fi, tyT1, tyT2) ->
        let tyT1' = whn ctx tyT1
        weakHead ctx (TyApp (fi, tyT1', tyT2))
    | _ ->
        raise NoRuleApply

and whn (ctx: Context) (ty: Type) : Type =
    try
        whn ctx (weakHead ctx ty)
    with
    | NoRuleApply ->
        ty
    

let rec ctxValid : Context -> bool = function
    | [] ->
        true
    | (x, VarBind ty) :: ctx ->
        Kind.isStar (kindOf ctx ty) && not (Context.contains x ctx)
    | (tyX, TyVarBind _) :: ctx ->
        not (Context.contains tyX ctx) && ctxValid ctx
    | (tyX, TyDefBind (k, tyT)) :: ctx ->
        kdEqv ctx k (kindOf ctx tyT) && not (Context.contains tyX ctx)
    | (_, NameBind) :: _ ->
        failwith "invalid context with name binding"
and kdEqv (ctx: Context) (k1: Kind) (k2: Kind) : bool =
    match k1, k2 with
    | KdStar _, KdStar _ -> true
    | KdOp (_, k11, k12), KdOp (_, k21, k22) -> kdEqv ctx k11 k21 && kdEqv ctx k12 k22
    | _ -> false
and structuralTyEqv (ctx: Context) (tyS: Type) (tyT: Type) : Kind =
    match tyS, tyT with
    | TyVar (_, i, n), TyVar (_, i', n') when i = i' && n = n' ->
        Context.getKind None i ctx
    | TyFun (fi, tyS1, tyS2), TyFun (_, tyT1, tyT2)
    | TyPair (fi, tyS1, tyS2), TyPair (_, tyT1, tyT2) ->
        let k1 = tyEqv ctx tyS1 tyT1
        let k2 = tyEqv ctx tyS2 tyT2
        if Kind.isStar k1 && Kind.isStar k2 then
            k1
        else
            error fi "ill-kinding type"
    | TyAll (_, tyX, k1, tyS2), TyAll (_, tyX', k1', tyT2)
        when tyX = tyX' && kdEqv ctx k1 k1' && not (Context.contains tyX ctx) ->
            tyEqv (Context.addTyVar tyX k1 ctx) tyS2 tyT2
    | TyApp (fi, tyS1, tyS2), TyApp (_, tyT1, tyT2) ->
        match structuralTyEqv ctx tyS1 tyT1 with
        | KdOp (fi, k1, k2) ->
            if kdEqv ctx k1 (tyEqv ctx tyS2 tyT2) then
                k2
            else
                error fi "ill-kinding type"
        | _ ->
            error fi "ill-kinding type"
    | _ ->
        error None "not supported"

    
and tyEqv (ctx: Context) (tyS: Type) (tyT: Type) : Kind =
    let tyS' = whn ctx tyS
    let tyT' = whn ctx tyT
    let k = structuralTyEqv ctx tyS' tyT'
    match k with
    | KdStar _ ->
        k
    | KdOp (_, k1, k2) ->
        let randomX = System.Guid.NewGuid().ToString()
        let x = TyVar (None, 0, ctx.Length + 1)
        tyEqv (Context.addTyVar randomX k1 ctx) (TyApp (None, Type.shift 1 tyS, x)) (TyApp (None, Type.shift 1 tyT, x))
and kindOf (ctx: Context) (ty: Type) : Kind =
    match ty with
    | TyVar (fi, i, n) ->
        if ctxValid ctx then
            Context.getKind fi i ctx
        else
            error fi "invalid context"
    | TyAbs (fi, tyX, k1, tyT2) ->
        let k2 = kindOf (Context.addTyVar tyX k1 ctx) tyT2
        KdOp (fi, k1, k2)
    | TyApp (fi, tyT1, tyT2) ->
        match kindOf ctx tyT1 with
        | KdOp (_, k11, k12) when kdEqv ctx (kindOf ctx tyT2) k11 ->
            k12
        | _ ->
            error fi "mismatch type constructor and type argument"
    | TyFun (fi, tyT1, tyT2)
    | TyPair (fi, tyT1, tyT2) ->
        if Kind.isStar (kindOf ctx tyT1) then
            if Kind.isStar (kindOf ctx tyT2) then
                KdStar fi
            else
                error (Type.info tyT2) "should be a proper type"
        else
            error (Type.info tyT1) "should be a proper type"
    | TyAll (fi, tyX, k1, tyT2) ->
        if Kind.isStar (kindOf (Context.addTyVar tyX k1 ctx) tyT2) then
            KdStar fi
        else
            error (Type.info tyT2) "should be a proper type"
and typeOf (ctx: Context) (t: Term) : Type =
    match t with
    | TmVar (fi, i, n) ->
        if ctxValid ctx then
            Context.getType fi i ctx
        else
            error fi "invalid context"
    | TmAbs (fi, x, tyT1, t2) ->
        let tyT2 = typeOf (Context.addVar x tyT1 ctx) t2
        TyFun (fi, tyT1, tyT2)
    | TmApp (fi, t1, t2) ->
        match typeOf ctx t1 with
        | TyFun (_, tyT11, tyT12) when Kind.isStar (tyEqv ctx (typeOf ctx t2) tyT11) ->
            tyT12
        | _ ->
            error fi "mismatch function and argument"
    | TmTAbs (fi, tyX, k1, t2) ->
        let tyT2 = typeOf (Context.addTyVar tyX k1 ctx) t2
        TyAll (fi, tyX, k1, tyT2)
    | TmTApp (fi, t1, tyT2) ->
        match typeOf ctx t1 with
        | TyAll (fi, tyX, k11, tyT12) when kdEqv ctx (kindOf ctx tyT2) k11 ->
            Type.substTop tyT2 tyT12
        | _ ->
            error fi "mismatch type abstraction and arugment"
    | TmPair (fi, t1, t2) ->
        let (tyT1, tyT2) = typeOf ctx t1, typeOf ctx t2
        TyPair (fi, tyT1, tyT2)
    | TmFst (fi, t1) ->
        match typeOf ctx t1 with
        | TyPair (fi, tyT11, tyT12) ->
            tyT11
        | _ ->
            error (Term.info t1) "should be a pair"
    | TmSnd (fi, t1) ->
        match typeOf ctx t1 with
        | TyPair (fi, tyT11, tyT12) ->
            tyT12
        | _ ->
            error (Term.info t1) "should be a pair"
    | TmTDef (fi, tyX, tyT1, t2) ->
        let k1 = kindOf ctx tyT1
        let ctx' = Context.addTyDef tyX k1 tyT1 ctx
        let tyT2 = typeOf ctx' t2
        let str = Pretty.ty2str ctx' tyT2
        if Kind.isStar (kindOf ctx' tyT2) then
            tyT2
        else
            error (Term.info t2) "should be a proper type"

let rec collectOuterTypeDefs : Context -> Term -> Context = fun ctx -> function
    | TmTDef (fi, tyX, tyT1, t2) ->
        let k1 = kindOf ctx tyT1
        let ctx' = Context.addTyDef tyX k1 tyT1 ctx
        collectOuterTypeDefs ctx' t2 
    | _ ->
        ctx
