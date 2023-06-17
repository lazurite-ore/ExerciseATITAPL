module Pretty

open Syntax

let rec kd2str (ctx: Context) = function
    | KdStar _ -> "*"
    | KdOp (_, KdStar _, k2) -> sprintf "*⇒%s" (kd2str ctx k2)
    | KdOp (_, k1, k2) -> sprintf "(%s)⇒%s" (kd2str ctx k1) (kd2str ctx k2)

let rec ty2str (ctx: Context) = function
    | TyVar (fi, i, n) ->
        if ctx.Length = n then
            Context.index2name fi i ctx
        else
            error fi (sprintf "bad index: %i in context: %A" i (List.map fst ctx))
    | TyFun (_, (TyFun _ as ty1), ty2) ->
        sprintf "(%s)→%s" (ty2str ctx ty1) (ty2str ctx ty2)
    | TyFun (_, ty1, ty2) ->
        sprintf "%s→%s" (ty2str ctx ty1) (ty2str ctx ty2)
    | TyPair (_, ty1, ty2) ->
        sprintf "(%s)×(%s)" (ty2str ctx ty1) (ty2str ctx ty2)
    | TyAll (_, tyX, KdStar _, ty) ->
        let ctx' = Context.addName tyX ctx
        sprintf "∀%s.%s" tyX (ty2str ctx' ty)
    | TyAll (_, tyX, k, ty) ->
        let ctx' = Context.addName tyX ctx
        sprintf "∀%s::%s.%s" tyX (kd2str ctx k) (ty2str ctx' ty)
    | TyAbs (_, tyX, KdStar _, tyT2) ->
        let ctx' = Context.addName tyX ctx
        sprintf "λ%s.%s" tyX (ty2str ctx' tyT2)
    | TyAbs (_, tyX, k, ty) ->
        let ctx' = Context.addName tyX ctx
        sprintf "λ%s::%s.%s" tyX (kd2str ctx k) (ty2str ctx' ty)
    | TyApp (_, ty1, ty2) ->
        sprintf "(%s) (%s)" (ty2str ctx ty1) (ty2str ctx ty2)
        
let rec tm2str (ctx: Context) = function
    | TmVar (fi, i, n) ->
        if ctx.Length = n then
            Context.index2name fi i ctx
        else
            error fi (sprintf "bad index: %i in context: %A" i (List.map fst ctx))
    | TmAbs (_, x, tyT1, t2) ->
        let ctx' = Context.addName x ctx
        sprintf "λ%s:%s.%s" x (ty2str ctx tyT1) (tm2str ctx' t2)
    | TmApp (_, t1, t2) ->
        sprintf "(%s) %s" (tm2str ctx t1) (tm2str ctx t2)
    | TmTAbs (_, tyX, k, t) ->
        let ctx' = Context.addName tyX ctx
        sprintf "λ%s::%s.%s" tyX (kd2str ctx k) (tm2str ctx' t)
    | TmTApp (_, t, ty) ->
        sprintf "(%s) [%s]" (tm2str ctx t) (ty2str ctx ty)
    | TmPair (_, t1, t2) ->
        sprintf "<%s, %s>" (tm2str ctx t1) (tm2str ctx t2)
    | TmFst (_, t) ->
        sprintf "(%s).1" (tm2str ctx t)
    | TmSnd (_, t) ->
        sprintf "(%s).2" (tm2str ctx t)
    | TmTDef (_, tyX, tyT, t) ->
        let ctx' = Context.addName tyX ctx
        sprintf "let %s = %s in %s" tyX (ty2str ctx tyT) (tm2str ctx' t)
    
