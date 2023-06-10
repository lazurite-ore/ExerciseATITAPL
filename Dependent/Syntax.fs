module Syntax

type TokenInfo = {
    Start: FSharp.Text.Lexing.Position
    End: FSharp.Text.Lexing.Position
}

type Info = TokenInfo option

type Type =
    | TyUnit of Info
    | TyVar of Info * int * int
    | TyPi  of Info * string * Type * Type
    | TyApp of Info * Type * Term
and Term =
    | TmUnit of Info
    | TmVar of Info * int * int
    | TmAbs of Info * string * Type * Term
    | TmApp of Info * Term * Term
    | TmLet of Info * string * Term * Term
and Kind =
    | KdStar of Info
    | KdPi of Info * string * Type * Kind

type Binding =
    | NameBind
    | VarBind of Type
    | TyVarBind of Kind

type Context = (string * Binding) list

exception CompilerError of Info * string

let inline error (fi: Info) msg =
    raise (CompilerError (fi, msg))

let rec tyMap onType onTerm c = function
    | TyUnit fi -> TyUnit fi
    | TyVar (fi, x, n) as tyT -> onType fi c x n tyT
    | TyPi  (fi, x, tyT1, tyT2) -> TyPi (fi, x, tyMap onType onTerm c tyT1, tyMap onType onTerm (c + 1) tyT2)
    | TyApp (fi, ty, t) -> TyApp (fi, tyMap onType onTerm c ty, tmMap onType onTerm c t)
and tmMap onType onTerm c = function
    | TmUnit fi -> TmUnit fi
    | TmVar (fi, x, n) as t -> onTerm fi c x n t
    | TmAbs (fi, x, tyT1, t2) -> TmAbs (fi, x, tyMap onType onTerm c tyT1, tmMap onType onTerm (c + 1) t2)
    | TmApp (fi, t1, t2) -> TmApp (fi, tmMap onType onTerm c t1, tmMap onType onTerm c t2)
    | TmLet (fi, x, t1, t2) -> TmLet (fi, x, tmMap onType onTerm c t1, tmMap onType onTerm (c + 1) t2)
let rec kdMap onType onTerm c = function
    | KdStar fi -> KdStar fi
    | KdPi (fi, x, tyT, k) -> KdPi (fi, x, tyMap onType onTerm c tyT, kdMap onType onTerm (c + 1) k)

let tyShiftAbove d c ty =
    tyMap
        (fun fi c x n tyT ->
            if x >= c then TyVar (fi, x + d, n + d) else TyVar (fi, x, n + d))
        (fun fi c x n t ->
            if x >= c then TmVar (fi, x + d, n + d) else TmVar (fi, x, n + d))
        c ty
let tmShiftAbove d c t =
    tmMap
        (fun fi c x n tyT ->
            if x >= c then TyVar (fi, x + d, n + d) else TyVar (fi, x, n + d))
        (fun fi c x n t ->
            if x >= c then TmVar (fi, x + d, n + d) else TmVar (fi, x, n + d))
        c t
let kdShiftAbove d c t =
    kdMap
        (fun fi c x n tyT ->
            if x >= c then TyVar (fi, x + d, n + d) else TyVar (fi, x, n + d))
        (fun fi c x n t ->
            if x >= c then TmVar (fi, x + d, n + d) else TmVar (fi, x, n + d))
        c t


let tyShift d ty = tyShiftAbove d 0 ty
let tmShift d t = tmShiftAbove d 0 t
let kdShift d k = kdShiftAbove d 0 k

let tySubst j tyS tyT =
    tyMap
        (fun fi j x n ty -> if x = j then tyShift j tyS else ty)
        (fun fi j x n t -> t)
        j tyT
let tmSubst j s t =
    tmMap
        (fun fi j x n tyT -> tyT)
        (fun fi j x n t -> if x = j then tmShift j s else t)
        j t
let tyTermSubst j s ty =
    tyMap
        (fun fi j x n tyT -> tyT)
        (fun fi j x n t -> if x = j then tmShift j s else t)
        j ty
let kdTermSubst j s k =
    kdMap
        (fun fi j x n tyT -> tyT)
        (fun fi j x n t -> if x = j then tmShift j s else t)
        j k

let tySubstTop tyS tyT =
    tyShift (-1) (tySubst 0 (tyShift 1 tyS) tyT)
let tmSubstTop s t =
    tmShift (-1) (tmSubst 0 (tmShift 1 s) t)
let tyTermSubstTop s ty =
    tyShift (-1) (tyTermSubst 0 (tmShift 1 s) ty)
let kdTermSubstTop s k =
    kdShift (-1) (kdTermSubst 0 (tmShift 1 s) k)

let tmInfo = function
    | TmUnit fi
    | TmVar (fi, _, _)
    | TmAbs (fi, _, _, _)
    | TmApp (fi, _, _)
    | TmLet (fi, _, _, _) ->
        fi

let tyInfo = function
    | TyUnit fi
    | TyVar (fi, _, _)
    | TyPi (fi, _, _, _)
    | TyApp (fi, _, _) ->
        fi

let kdInfo = function
    | KdStar fi
    | KdPi (fi, _, _, _) ->
        fi

let conInfo fi1 fi2 =
    match fi1, fi2 with
    | Some { Start = s1; End = _ }, Some { Start = _; End = e2} -> Some { Start = s1; End = e2 }
    | (None, Some fi)
    | (Some fi, None) -> Some fi
    | (None, None) -> None
        
module Context =

    let len (ctx: Context) = List.length ctx

    let bindingShift d bind =
        match bind with
        | NameBind -> NameBind
        | VarBind ty -> VarBind (tyShift d ty)
        | TyVarBind kd -> TyVarBind (kdShift d kd)

    let addBinding x bind (ctx: Context) = (x, bind) :: ctx
    
    let addName x ctx = addBinding x NameBind ctx

    let addVar x ty ctx = addBinding x (VarBind ty) ctx

    let addTypeVar x kd ctx = addBinding x (TyVarBind kd) ctx

    let index2name fi i (ctx: Context) =
        match List.tryItem i ctx with
        | Some (x, _) -> x
        | None -> error fi (sprintf "unbound variable of index: %i, context size: %i" i ctx.Length)

    let name2index fi x (ctx: Context) =
        match List.tryFindIndex (fun (x', _) -> x = x') ctx with
        | Some i -> i
        | None -> error fi (sprintf "unbound variable: %s" x)

    let rec getBinding fi i (ctx: Context) =
        match List.tryItem i ctx with
        | Some (_, bind) -> bindingShift (i + 1) bind
        | None -> error fi (sprintf "unbound binding of index: %i, context size: %i" i ctx.Length)

    let getType fi i ctx =
        match getBinding fi i ctx with
        | VarBind tyT -> tyT
        | _ -> error fi (sprintf "unbound var: %s, context size: %i" (index2name fi i ctx) ctx.Length)

    let getKind fi i ctx =
        match getBinding fi i ctx with
        | TyVarBind kd -> kd
        | _ -> error fi (sprintf "no such kind: %s, context length: %d" (index2name fi i ctx) (len ctx))

let rec collectOutsideDef (ctx: Context) = function
    | TmLet (_, x, t1, t2) ->
        collectOutsideDef (Context.addName x ctx) t2
    | _ ->
        ctx