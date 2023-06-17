module Syntax

type TokenInfo = {
    Start: FSharp.Text.Lexing.Position
    End: FSharp.Text.Lexing.Position
}

type Info = TokenInfo option

type Kind =
    | KdStar of Info
    | KdOp   of Info * Kind * Kind

type Type =
    | TyVar  of Info * int * int
    | TyFun  of Info * Type * Type
    | TyPair of Info * Type * Type
    | TyAll  of Info * string * Kind * Type
    | TyAbs  of Info * string * Kind * Type
    | TyApp  of Info * Type * Type

type Term =
    | TmVar   of Info * int * int
    | TmAbs   of Info * string * Type * Term
    | TmApp   of Info * Term * Term
    | TmTAbs  of Info * string * Kind * Term
    | TmTApp  of Info * Term * Type
    | TmPair  of Info * Term * Term
    | TmFst   of Info * Term
    | TmSnd   of Info * Term
    | TmTDef  of Info * string * Type * Term

type Binding =
    | NameBind                 // only on parsing or printing
    | VarBind   of Type        // x:T
    | TyVarBind of Kind        // X::K
    | TyDefBind of Kind * Type // X::K=T

type Context = (string * Binding) list

exception CompilerError of Info * string

let inline error (fi: Info) msg = raise (CompilerError (fi, msg))

module Info =

    let con (fi1: Info) (fi2: Info) : Info =
        match fi1, fi2 with
        | None, None -> None
        | fi, None | None, fi -> fi
        | Some tk1, Some tk2 -> Some { Start = tk1.Start; End = tk2.Start }

module Kind =

    let info = function
        | KdStar fi
        | KdOp (fi, _, _) ->
            fi

    let isStar = function
        | KdStar _ -> true
        | KdOp _ -> false

module Type =

    let info = function
        | TyVar  (fi, _, _)
        | TyFun  (fi, _, _) 
        | TyPair (fi, _, _) 
        | TyAll  (fi, _, _, _)
        | TyAbs  (fi, _, _, _)
        | TyApp  (fi, _, _) ->
            fi

    let rec map onType c = function
        | TyVar  (fi, x, n) -> onType fi c x n
        | TyFun  (fi, tyT1, tyT2) -> TyFun (fi, map onType c tyT1, map onType c tyT2)
        | TyPair (fi, tyT1, tyT2) -> TyPair (fi, map onType c tyT1, map onType c tyT2)
        | TyAll  (fi, tyX, k, tyT) -> TyAll (fi, tyX, k, map onType (c + 1) tyT)
        | TyAbs  (fi, tyX, k, tyT) -> TyAbs (fi, tyX, k, map onType (c + 1) tyT)
        | TyApp  (fi, tyT1, tyT2) -> TyApp (fi, map onType c tyT1, map onType c tyT2)

    let shiftAbove d c tyT =
        map
            (fun fi c x n -> if x >= c then TyVar (fi, x + d, n + d) else TyVar (fi, x, n + d))
            c tyT
    
    let shift d tyT = shiftAbove d 0 tyT

    let subst tyS j tyT =
        map
            (fun fi j x n -> if x = j then shift j tyS else TyVar (fi, x, n))
            j tyT

    let substTop tyS tyT = shift (-1) (subst (shift 1 tyS) 0 tyT)

module Term =

    let info = function
        | TmVar  (fi, _, _)
        | TmAbs  (fi, _, _, _)
        | TmApp  (fi, _, _)
        | TmTAbs (fi, _, _, _)
        | TmTApp (fi, _, _)
        | TmPair (fi, _, _)
        | TmFst  (fi, _)
        | TmSnd  (fi, _)
        | TmTDef (fi, _, _, _) ->
            fi

    let rec map onType onTerm c = function
        | TmVar  (fi, x, n) -> onTerm fi c x n
        | TmAbs  (fi, x, ty, t) -> TmAbs (fi, x, Type.map onType c ty, map onType onTerm (c + 1) t)
        | TmApp  (fi, t1, t2) -> TmApp (fi, map onType onTerm c t1, map onType onTerm c t2)
        | TmTAbs (fi, x, k, t) -> TmTAbs (fi, x, k, map onType onTerm (c + 1) t)
        | TmTApp (fi, t, ty) -> TmTApp (fi, map onType onTerm c t, Type.map onType c ty)
        | TmPair (fi, t1, t2) -> TmPair (fi, map onType onTerm c t1, map onType onTerm c t2)
        | TmFst  (fi, t) -> TmFst (fi, map onType onTerm c t)
        | TmSnd  (fi, t) -> TmSnd (fi, map onType onTerm c t)
        | TmTDef (fi, tyX, tyT, t) -> TmTDef (fi, tyX, Type.map onType c tyT, map onType onTerm (c + 1) t)

    let shiftAbove d c t =
        map
            (fun fi c x n ->
                if x >= c then TyVar (fi, x + d, n + d) else TyVar (fi, x, n + d))
            (fun fi c x n ->
                if x >= c then TmVar (fi, x + d, n + d) else TmVar (fi, x, n + d))
            c t

    let shift d t = shiftAbove d 0 t
    
    let subst s j t =
        map
            (fun fi j x n -> TyVar (fi, x, n))
            (fun fi j x n -> if x = j then shift j s else TmVar (fi, x, n))
            j t
    
    let substTop s t = shift (-1) (subst (shift 1 s) 0 t)

    let substTy tyS j t =
        map
            (fun fi j x n -> if x = j then Type.shift j tyS else TyVar (fi, x, n))
            (fun fi j x n -> TmVar (fi, x, n))
            j t
    
    let substTyTop tyS t = shift (-1) (substTy (Type.shift 1 tyS) 0 t)

module Context =
    
    let len (ctx: Context) = List.length ctx

    let bindingShift d bind =
        match bind with
        | NameBind -> NameBind
        | VarBind ty -> VarBind (Type.shift d ty)
        | TyVarBind k -> TyVarBind k
        | TyDefBind (k, ty) -> TyDefBind (k, Type.shift d ty)

    let addBinding x bind (ctx: Context) : Context = (x, bind) :: ctx
    
    let addName x ctx = addBinding x NameBind ctx

    let addVar x ty ctx = addBinding x (VarBind ty) ctx

    let addTyVar x k ctx = addBinding x (TyVarBind k) ctx

    let addTyDef x k ty ctx = addBinding x (TyDefBind (k, ty)) ctx

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
        | Some (_, bind) -> bindingShift i bind//bindingShift (i + 1) bind
        | None -> error fi (sprintf "unbound binding of index: %i, context size: %i" i ctx.Length)

    let getType fi i ctx =
        match getBinding fi i ctx with
        | VarBind tyT -> tyT
        | _ -> error fi (sprintf "unbound var: %s, context size: %i" (index2name fi i ctx) ctx.Length)

    let getKind fi i ctx =
        match getBinding fi i ctx with
        | TyVarBind kd -> kd
        | _ -> error fi (sprintf "no such kind: %s, context length: %d" (index2name fi i ctx) ctx.Length)

    let getDef fi i ctx =
        match getBinding fi i ctx with
        | TyDefBind (k, ty) -> (k, ty)
        | _ -> error fi (sprintf "no such type def: %s, context length: %d" (index2name fi i ctx) ctx.Length)

    let contains x (ctx: Context) =
        List.exists (fun (x', _) -> x' = x) ctx