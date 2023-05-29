module RuntimeData

open Syntax

type Ptr = int

type EvalTerm =
    | ETmVar    of int * int
    | ETmBool   of Qualifier * bool
    | ETmPair   of Qualifier * EvalTerm * EvalTerm
    | ETmAbs    of Qualifier * string * Type * EvalTerm
    | ETmIfElse of EvalTerm * EvalTerm * EvalTerm
    | ETmSplit  of EvalTerm * string * string * EvalTerm
    | ETmApp    of EvalTerm * EvalTerm
    | ETmPtr    of Ptr

type Store = (Ptr * EvalTerm) list



module EvalTerm =

    let rec termToEval = function
        | TmVar (_, i, n) -> ETmVar (i, n)
        | TmApp (_, t1, t2) -> ETmApp (termToEval t1, termToEval t2)
        | TmBool (_, q, b) -> ETmBool (q, b)
        | TmPair (_, q, t1, t2) -> ETmPair (q, termToEval t1, termToEval t2)
        | TmAbs (_, q, x, ty, t) -> ETmAbs (q, x, ty, termToEval t)
        | TmIfElse (_, t1, t2, t3) -> ETmIfElse (termToEval t1, termToEval t2, termToEval t3)
        | TmSplit (_, t1, x, y, t2) -> ETmSplit (termToEval t1, x, y, termToEval t2)

    let map onvar ontype c t =
        let rec walk c t =
            match t with
            | ETmVar (x, n) -> onvar c x n
            | ETmAbs (q, x, tyT1, t2) ->
                ETmAbs (q, x, ontype c tyT1, walk (c + 1) t2)
            | ETmApp (t1, t2) -> ETmApp (walk c t1, walk c t2)
            | ETmIfElse (t1, t2, t3) -> ETmIfElse (walk c t1, walk c t2, walk c t3)
            | ETmBool (q, b) -> ETmBool (q, b)
            | ETmPair (q, t1, t2) -> ETmPair (q, walk c t1, walk c t2)
            | ETmSplit (t1, x, y, t2) -> ETmSplit (walk c t1, x, y, walk (c + 2) t2)
            | ETmPtr ptr -> ETmPtr ptr
        walk c t

    let shiftAbove d c t =
      map
        (fun c x n ->
           if x >= c then ETmVar (x + d, n + d) else ETmVar (x, n + d))
        (Type.shiftAbove d) c t
      
    let shift d t = shiftAbove d 0 t

    let subst j s t =
      map
        (fun j x n -> if x = j then shift j s else ETmVar (x, n))
        (fun j tyT -> tyT)
        j t
      
    let substTop s t = shift (-1) (subst 0 (shift 1 s) t)
        

module Store =

    let malloc ev (s: Store) : Ptr * Store =
        match s with
        | [] -> (0, [(0, ev)])
        | (ptr, _) :: _ -> (ptr + 1, (ptr + 1, ev) :: s)
    
    let rec read ptr (s: Store) : EvalTerm =
        match s with
        | (ptr', v) :: _ when ptr = ptr' -> v
        | _ :: s' -> read ptr s'
        | [] -> failwithf "wild pointer error"
    
    /// only free linear value
    let rec free ptr (s: Store) : Store =
        List.filter (function
                     | ptr', ETmBool (q, _)
                     | ptr', ETmPair (q, _, _)
                     | ptr', ETmAbs (q, _, _, _) -> not (q = Lin && ptr = ptr')
                     | _ -> true) s