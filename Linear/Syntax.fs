module Syntax


type TokenInfo = {
    Start: FSharp.Text.Lexing.Position
    End: FSharp.Text.Lexing.Position
}

type Info = TokenInfo option

exception CompilerError of Info * string

type Qualifier =
    | Lin
    | Un

type PreType =
    | PTyBool
    | PTyPair of Type * Type
    | PTyArr  of Type * Type
and Type = Qualifier * PreType

type Term =
    | TmVar    of Info * int * int
    | TmBool   of Info * Qualifier * bool
    | TmIfElse of Info * Term * Term * Term
    | TmPair   of Info * Qualifier * Term * Term
    | TmSplit  of Info * Term * string * string * Term
    | TmAbs    of Info * Qualifier * string * Type * Term
    | TmApp    of Info * Term * Term

type Binding =
    | NameBind
    | VarBind of Type

type Context = (string * Binding) list

let inline error (fi: Info) msg =
    raise (CompilerError (fi, msg))

module Qualifier =
    let subeq q1 q2 =
        match q1, q2 with
        | Lin, Un -> true
        | q1, q2 when q1 = q2 -> true
        | _ -> false

module Info =
    let getStart (fi: Info) =
        match fi with
        | Some ti -> ti.Start
        | _ -> failwith "no information"

    let getEnd (fi: Info) =
        match fi with
        | Some ti -> ti.End
        | _ -> failwith "no information"

    let combine (fi1: Info) (fi2: Info) : Info =
        Some { Start = getStart fi1; End = getEnd fi2 }

module Type =

    let map onvar c tyT =
        let rec walk c (q, pty) =
            let pty' =
                match pty with
                | PTyBool -> PTyBool
                | PTyPair (tyT1, tyT2) -> PTyPair (walk c tyT1, walk c tyT2)
                | PTyArr (tyT1, tyT2) -> PTyArr (walk c tyT1, walk c tyT2)
            (q, pty')
        walk c tyT

    let shiftAbove d c tyT =
        map
            ()//(fun c x n -> if x >= c then TyVar (x + d, n + d) else TyVar (x, n + d))
            c tyT

    let shift d tyT = shiftAbove d 0 tyT

    //let subst tyS j tyT =
    //  map (fun j x n -> if x = j then shift j tyS else TyVar (x, n)) j tyT
      
    //let typeSubstTop tyS tyT = typeShift (-1) (typeSubst (typeShift 1 tyS) 0 tyT)

    let rec checkQ q ((q', _): Type) =
        Qualifier.subeq q q'

module Term =

    let map onvar ontype c t =
        let rec walk c t =
            match t with
            | TmVar (fi, x, n) -> onvar fi c x n
            | TmAbs (fi, q, x, tyT1, t2) ->
                TmAbs (fi, q, x, ontype c tyT1, walk (c + 1) t2)
            | TmApp (fi, t1, t2) -> TmApp (fi, walk c t1, walk c t2)
            | TmIfElse (fi, t1, t2, t3) -> TmIfElse (fi, walk c t1, walk c t2, walk c t3)
            | TmBool (fi, q, b) -> TmBool (fi, q, b)
            | TmPair (fi, q, t1, t2) -> TmPair (fi, q, walk c t1, walk c t2)
            | TmSplit (fi, t1, x, y, t2) -> TmSplit (fi, walk c t1, x, y, walk (c + 2) t2)
        walk c t

    let shiftAbove d c t =
      map
        (fun fi c x n ->
           if x >= c then TmVar (fi, x + d, n + d) else TmVar (fi, x, n + d))
        (Type.shiftAbove d) c t
      
    let shift d t = shiftAbove d 0 t

    let subst j s t =
      map
        (fun fi j x n -> if x = j then shift j s else TmVar (fi, x, n))
        (fun j tyT -> tyT)
        j t
      
    let substTop s t = shift (-1) (subst 0 (shift 1 s) t)

    let info = function
        | TmVar    (fi, _, _)
        | TmBool   (fi, _, _)
        | TmIfElse (fi, _, _, _)
        | TmPair   (fi, _, _, _)
        | TmSplit  (fi, _, _, _, _)
        | TmAbs    (fi, _, _, _, _)
        | TmApp    (fi, _, _) ->
            fi

module Context =

    let len (ctx: Context) = List.length ctx

    let bindingShift d bind =
        //match bind with
        //| NameBind -> NameBind
        //| VarBind ty -> VarBind (Type.shift d ty)
        bind

    let addBinding x bind (ctx: Context) = (x, bind) :: ctx
    
    let addName x ctx = addBinding x NameBind ctx

    let addVar x ty ctx = addBinding x (VarBind ty) ctx

    let rec checkQ q = function
        | (x, VarBind ty) :: ctx -> Type.checkQ q ty && checkQ q ctx
        | _ -> true

    let isLinBind ctx = function
        | VarBind (Lin, _) -> true
        | _ -> false

    let rec getBinding fi i (ctx: Context) : (Binding * Context) =
        match List.splitAt i ctx with
        | (ctx1, (_, (VarBind (Lin, _) as bind)) :: ctx2) ->
            (bindingShift (i + 1) bind, ctx1 @ ctx2)
        | (ctx1, (_, bind) :: ctx2) ->
            (bindingShift (i + 1) bind, ctx)
        | _ ->
            error fi (sprintf "no such binding: %d, context length: %d" i (len ctx))

    let index2name fi i ctx =
        match List.tryItem i ctx with
        | Some (x, _) -> x
        | None -> error fi (sprintf "no such binding: %d, context length: %d" i (len ctx))

    let name2index fi x ctx =
        match List.tryFindIndex (fun (y, _) -> x = y) ctx with
        | Some i -> i
        | None -> error fi (sprintf "unbound identifier: %s" x)
      
    let getType fi i ctx =
        match getBinding fi i ctx with
        | VarBind tyT, ctx' -> tyT, ctx'
        | _ -> error fi (sprintf "no such var: %s, context length: %d" (index2name fi i ctx) (len ctx))

    let remove x ty ctx : Context =
        List.filter (fun e -> e <> (x, VarBind ty)) ctx

    let notIn x ty ctx = not (List.contains (x, VarBind ty) ctx)

    let rec difference fi (ctx1: Context) (ctx: Context) =
        match ctx with
        | (x, VarBind (Lin, p)) :: ctx2 ->
            let ctx3 = difference fi ctx1 ctx2
            if notIn x (Lin, p) ctx3 then
                ctx3
            else
                error fi "fail to check context difference"
        
        | (x, VarBind (Un, p)) :: ctx2 ->
            let ctx3 = difference fi ctx1 ctx2
            let ctx45 = remove x (Un, p) ctx3
            ctx45
        | (x, NameBind) :: _ ->
            failwith "unsupported operation"
        | [] ->
            ctx1

module Pretty =

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