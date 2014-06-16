(*
  Parser for SMTLib-based program format

  @author Marc Brockschmidt

  Copyright 2014 Microsoft Research

  All rights reserved.

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the ""Software""), to
  deal in the Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
  sell copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included
  in all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
  THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.
*)

open Sexplib.Sexp
open Printf
open Program
open Utils
open Term
open Term.Sort
open Term.BoolTerm
open Term.IntTerm

module VarMap = Map.Make(String)
module ProcedureMap = Map.Make(String)
module LocMap = Map.Make(String)

exception ParseException of string

let sortOfSexp s =
  match s with
  | Atom "Int" -> SInt
  | Atom "Bool" -> SBool
  | Atom "Loc"  -> SLoc
  | _ -> raise (ParseException (sprintf "Do not know how to handle sort '%s'." (to_string_hum s)))

let parseSortedVar t =
  match t with
  | List [ (Atom id) ; sort ] ->
      (id, sortOfSexp sort)
  | _ ->
      raise (ParseException (sprintf "Expected sorted variable '(var sort)', got '%s'." (to_string_hum t)))

let parseVarBinding t =
  match t with
  | List [ (Atom id) ; term ] ->
      (id, term)
  | _ ->
      raise (ParseException (sprintf "Expected var binding '(var term)', got '%s'." (to_string_hum t)))

exception NoIntArithTerm of Sexplib.Sexp.t
exception NoIntConstrTerm of Sexplib.Sexp.t

let rec parseIntArithTerm t =
  match t with
  | Atom a ->
      (
        try (Const (Big_int.big_int_of_string a)) with
        | Failure _ -> IId(a)
      )
  | List [ (Atom "-") ; a ] -> 
      Neg (parseIntArithTerm a)
  | List [ (Atom "-") ; a ; b ] -> 
      Sub (parseIntArithTerm a, parseIntArithTerm b)
  | List [ (Atom "+") ; a ; b ] -> 
      Add (parseIntArithTerm a, parseIntArithTerm b)
  | List [ (Atom "*") ; a ; b ] -> 
      Mul (parseIntArithTerm a, parseIntArithTerm b)
  | _ -> raise (NoIntArithTerm t)

let parseIntConstrTerm t =
  match t with
  | List [ (Atom "<") ; a ; b ] -> 
      Lt (parseIntArithTerm a, parseIntArithTerm b)
  | List [ (Atom "<=") ; a ; b ] -> 
      Le (parseIntArithTerm a, parseIntArithTerm b)
  | List [ (Atom ">") ; a ; b ] -> 
      Gt (parseIntArithTerm a, parseIntArithTerm b)
  | List [ (Atom ">=") ; a ; b ] -> 
      Ge (parseIntArithTerm a, parseIntArithTerm b)
  | List ((Atom "=") :: args) -> 
      Eq (List.map parseIntArithTerm args)
  | _ -> raise (NoIntConstrTerm t)

let rec parseBoolTerm t =
  match t with
  | Atom "true" ->
      True
  | Atom "false" ->
      False
  | Atom id ->
      BId id
  | List [ (Atom "not") ; a ] -> 
      Not (parseBoolTerm a)

  | List ((Atom "and")::args) -> 
      And (List.map parseBoolTerm args)
  | List ((Atom "or")::args) -> 
      Or (List.map parseBoolTerm args)
  (* TODO: Support these?
     | List ((Atom "xor")::args) -> 
     Xor (List.map parseBoolTerm args)
     | List [ (Atom "=>") ; a ; b ] -> 
     Impl (parseBoolTerm a, parseBoolTerm b)
  *)
  | List [ (Atom "forall") ; List bindings ; body ] ->
    Forall (List.map parseSortedVar bindings, parseBoolTerm body)
  | List [ (Atom "exists") ; List bindings ; body ] ->
    Exists (List.map parseSortedVar bindings, parseBoolTerm body)
  | e ->
      try parseIntConstrTerm e with
      | NoIntArithTerm s
      | NoIntConstrTerm s ->
          raise (ParseException (sprintf "Cannot parse bool term '%s' at subterm '%s'." (to_string_hum t) (to_string_hum s)))

let rec substitute map e =
  match e with
  | List [(Atom "forall") ; (List boundVars) ; t] ->
      let boundVars' = List.map (fun v -> fst (parseSortedVar v)) boundVars in
      let map' = List.fold_left (fun map var -> VarMap.remove var map) map boundVars' in
      List [ (Atom "forall") ; (List boundVars) ; (substitute map' t) ]
  | List [(Atom "exists") ; (List boundVars) ; t] ->
      let boundVars' = List.map (fun v -> fst (parseSortedVar v)) boundVars in
      let map' = List.fold_left (fun map var -> VarMap.remove var map) map boundVars' in
      List [ (Atom "exists") ; (List boundVars) ; (substitute map' t) ]
  | List [(Atom "let") ; (List bindings) ; t] ->
      let bindings = List.map parseVarBinding bindings in
      let map' = List.fold_left (fun map (var, binding) -> VarMap.add var binding map) map bindings in
      substitute map' t
  | List args ->
      List (List.map (fun t -> substitute map t) args) 
  | Atom id ->
      if VarMap.mem id map then
        VarMap.find id map
      else
        Atom id

let rec betaNormalize funBindings e =
  match e with
  | List ((Atom id)::args) -> 
      (
        match Utils.tryFind (function (n, _, _, _) -> n = id) funBindings with
        | Some (_, pars, _, term) ->
            if (List.length args) <> (List.length pars) then
              raise (ParseException (sprintf "Function '%s' applied to wrong number of arguments in '%s'." id (to_string_hum e)))
            else
              let substMap = List.fold_left (fun map (var, t) -> VarMap.add (fst var) t map) VarMap.empty (List.combine pars args) in
              let instantiatedTerm = betaNormalize funBindings (substitute substMap term) in
              instantiatedTerm
        | None ->
            List ((Atom id)::(List.map (fun t -> betaNormalize funBindings t) args))
      )
  | _ -> e

let checkCFGInitDef definedFuns = 
  match Utils.tryFind (fun (n, _, _, _) -> n = "cfg_init") definedFuns with
  | None ->
      raise (ParseException (sprintf "Could not find definition of 'cfg_init' function."))
  | Some (_, [ ("pc", SLoc) ; ("src", SLoc) 
             ; ("rel", SBool)], initSort, initDef) ->
      (
        if initSort <> SBool then
          raise (ParseException (sprintf "Function 'cfg_init' must have sort 'Bool'."));
        match parseBoolTerm initDef with
        | And [ Eq [ IId "pc" ; IId "src" ]
              ; BId "rel" ] ->
            ()
        | _ ->
            raise (ParseException (sprintf "Function 'cfg_init' must be defined as '(and (= pc src) rel)'."));
      )
  | Some (_, _, _, _) ->
      raise (ParseException (sprintf "Function 'cfg_init' must have parameters '(pc Loc) (src Loc) (rel Bool)'."))

let checkCFGTrans2Def definedFuns = 
  match Utils.tryFind (fun (n, _, _, _) -> n = "cfg_trans2") definedFuns with
  | None ->
      raise (ParseException (sprintf "Could not find definition of 'cfg_trans2' function."))
  | Some (_, [ ("pc", SLoc) ; ("src", SLoc) 
             ; ("pc1", SLoc) ; ("dst", SLoc) 
             ; ("rel", SBool) ], trans2Sort, trans2Def) ->
      (
        if trans2Sort <> SBool then
          raise (ParseException (sprintf "Function 'cfg_trans2' must have sort 'Bool'."));
        match parseBoolTerm trans2Def with
        | And [ (Eq [IId "pc" ; IId "src"])
              ; (Eq [IId "pc1" ; IId "dst"])
              ; BId "rel" ] ->
            ()
        | _ ->
            raise (ParseException (sprintf "Function 'cfg_trans2' must be defined as '(and (= pc src) (= pc1 dst) rel)'."));
      )
  | Some (_, _, _, _) ->
      raise (ParseException (sprintf "Function 'cfg_trans2' must have parameters '(pc Loc) (src Loc) (pc1 Loc) (dst Loc) (rel Bool)'."))

let checkCFGTrans3Def definedFuns = 
  match Utils.tryFind (fun (n, _, _, _) -> n = "cfg_trans3") definedFuns with
  | None ->
      raise (ParseException (sprintf "Could not find definition of 'cfg_trans3' function."))
  | Some (_, [ ("pc", SLoc)  ; ("exit", SLoc) 
             ; ("pc1", SLoc) ; ("call", SLoc) 
             ; ("pc2", SLoc) ; ("return", SLoc) 
             ; ("rel", SBool)], trans3Sort, trans3Def) ->
      (
        if trans3Sort <> SBool then
          raise (ParseException (sprintf "Function 'cfg_trans3' must have sort 'Bool'."));
        match parseBoolTerm trans3Def with
        | And [ (Eq [IId "pc"; IId "exit"]) 
              ; (Eq [IId "pc1"; IId "call"])
              ; (Eq [IId "pc2"; IId "return"])
              ; BId "rel" ] ->
            ()
        | _ ->
            raise (ParseException (sprintf "Function 'cfg_trans3' must be defined as '(and (= pc exit) (= pc1 call) (= pc2 return) rel)'."));
      )
  | Some (_, _, _, _) ->
      raise (ParseException (sprintf "Function 'cfg_trans3' must have parameters '(pc Loc) (exit Loc) (pc1 Loc) (call Loc) (pc2 Loc) (return Loc) (rel Bool)'."))

let parseLocations declaredSorts declaredConsts distinctIDs =
  match Utils.tryFind (fun (sortName, _) -> sortName = "Loc") declaredSorts with
  | None ->
      raise (ParseException (sprintf "Sort 'Loc' was not declared."))
  | Some (_, locArity) ->
      (
        if locArity <> 0 then
          raise (ParseException (sprintf "Sort 'Loc' must have arity 0."));
        
        let declaredLocs = 
          Utils.concatMap
            (fun (id, sort) -> if sort = SLoc then [id] else [])
            declaredConsts
        in
        match Utils.tryFind (fun loc -> not(Utils.contains (=) distinctIDs loc)) declaredLocs with
        | Some loc ->
            raise (ParseException (sprintf "Location '%s' is not distinct from other locations." loc))
        | None ->
            declaredLocs
      )

let parseInitDef definedFuns declaredConsts =
  let initRE = Str.regexp "^init_\\(.+\\)" in
  let isInitName (n, _, _, _) = Str.string_match initRE n 0 in
  let initDefs = List.filter isInitName definedFuns in
  if List.length initDefs = 0 then
    raise (ParseException (sprintf "Could not find definition of a 'init_*' function."))
  else if List.length initDefs > 1 then
    raise (ParseException (sprintf "May not have more than one 'init_*' function."))
  else
    match (List.hd initDefs) with
    | (n, [], _, _) ->
      raise (ParseException (sprintf "Function '%s' must have at least one parameter (pc)." n))
    | (n, ((firstId, firstSort)::initPars), initSort, initDef) ->
      (
        if initSort <> SBool then
          raise (ParseException (sprintf "Function '%s' must have sort 'Bool'." n));

        if firstSort <> SLoc then
          raise (ParseException (sprintf "First parameter of function '%s' must have sort 'Loc'." n));

        match parseBoolTerm initDef with
        | And [Eq [arg1 ; arg2] ; initConstraint] ->
          (
            if arg1 <> IId firstId && arg2 <> IId firstId then
              raise (ParseException (sprintf "Definition of '%s' has to be of form '(cfg_init pc locID rel)', not '%s'." n (to_string_hum initDef)))
            else
              let initVarSet = varListToSet (List.map (fun (v,_) -> v) initPars) in
              let declaredConstSet = varListToSet (List.map (fun (v,_) -> v) declaredConsts) in
              let definedIDs = VarSet.union declaredConstSet initVarSet in

              let undeclVar = VarSet.fold (fun v acc -> VarSet.remove v acc) definedIDs (BoolTerm.getFreeVars initConstraint) in
              if not(VarSet.is_empty undeclVar) then
                raise (ParseException (sprintf "Definition of '%s' uses undeclared variable '%s' in relation '%s'" n (VarSet.choose undeclVar) (BoolTerm.to_string_SMTLIB initConstraint)));

              ignore (Str.search_forward initRE n 0);
              let initProcedureName = Str.matched_group 1 n in
              (* The thing we compared pc to is the init location *)
              let initLoc = if arg1 = IId firstId then arg2 else arg1 in
              match initLoc with
              | IId initLoc ->
                { name = initProcedureName ;
                  location = initLoc ;
                  initVars = initPars ;
                  constr = initConstraint ;
                };
              | _ ->
                raise (ParseException (sprintf "Could not identify init location."));
          )
        | _ ->
            raise (ParseException (sprintf "Definition of '%s' has to be of form '(cfg_init pc locID rel)', not '%s'." n (to_string_hum initDef)))
      )

let parseNextDefs definedFuns declaredConsts initVars =
  let nextRE = Str.regexp "^next_\\(.+\\)" in
  let isNextProcedureName (n, _, _, _) = Str.string_match nextRE n 0 in
  let getNextProcedureName n = 
    ignore (Str.search_forward nextRE n 0);
    Str.matched_group 1 n in
  let parseNextDef funDef =
    match funDef with
    | (n, [], _, _) ->
      raise (ParseException (sprintf "Function '%s' must have at least two parameters (pc, pc1)." n));
    | (n, nextPars, nextSort, nextDef) ->
      (
        if nextSort <> SBool then
          raise (ParseException (sprintf "Function '%s' must have sort 'Bool'." n));

        let parNum = List.length nextPars in
        if parNum mod 2 = 1 then
          raise (ParseException (sprintf "Function '%s' must have even number of parameters." n));
        let preVars = Utils.take (parNum / 2) nextPars in
        let postVars = Utils.drop (parNum / 2) nextPars in

        if snd (List.hd preVars) <> SLoc then
          raise (ParseException (sprintf "Function '%s' must have first parameter with sort 'Loc'." n));
        if snd (List.hd postVars) <> SLoc then
          raise (ParseException (sprintf "Function '%s' must have middle parameter with sort 'Loc'." n));

        (* pc is special-cased, drop from standard var list *)
        let preVars = List.tl preVars in
        let postVars = List.tl postVars in

        (* check sorts *)
        List.iteri
          (fun i ((_, s1), (_, s2)) ->
            if s1 <> s2 then raise (ParseException (sprintf "Function '%s' uses sort '%s' for %i-th argument in pre-vars, but '%s' in post-vars." n (Sort.to_string s1) (i+2) (Sort.to_string s2))))
          (List.combine preVars postVars);

        let preVarSet = varListToSet (List.map (fun (v,_) -> v) preVars) in
        let postVarSet = varListToSet (List.map (fun (v,_) -> v) postVars) in
        let declaredConstSet = varListToSet (List.map (fun (v,_) -> v) declaredConsts) in
        let definedIDs = VarSet.union declaredConstSet (VarSet.union preVarSet postVarSet) in

        match parseBoolTerm nextDef with
        | Or transitions ->
          let parseTrans t = 
            match t with
            | And [ Eq [IId "pc" ; IId src]
                  ; Eq [IId "pc1" ; IId dst]
                  ; rel ] ->
              let undeclVar = VarSet.fold (fun v acc -> VarSet.remove v acc) definedIDs (BoolTerm.getFreeVars rel) in
              if not(VarSet.is_empty undeclVar) then
                raise (ParseException (sprintf "Transition from '%s' to '%s' uses undeclared variable '%s' in relation '%s'" src dst (VarSet.choose undeclVar) (BoolTerm.to_string_SMTLIB rel)));
              (src, rel, dst)
            | _ ->
              raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans-decl>*)'." n));
          in
          { name = getNextProcedureName n ;
            preVars = preVars ;
            postVars = postVars;
            transitions = List.map parseTrans transitions;
          }
        | _ ->
          raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans-decl>*)'." n));
      )
  in
  List.map parseNextDef (List.filter isNextProcedureName definedFuns)

let parseCallDefs definedFuns declaredConsts initVars =
  let callRE = Str.regexp "^\\(.+\\)_call_\\(.+\\)" in
  let isCallName (n, _, _, _) = Str.string_match callRE n 0 in
  let usedProcedureName n = 
    ignore (Str.search_forward callRE n 0);
    (Str.matched_group 1 n, Str.matched_group 2 n)
  in
  let parseCallDef funDef =
    match funDef with
    | (n, [], _, _)
    | (n, [_], _, _) ->
      raise (ParseException (sprintf "Function '%s' must have at least two parameters (pc, pc1)." n));
    | (n, callPars, callSort, callDef) ->
      (
        if callSort <> SBool then
          raise (ParseException (sprintf "Function '%s' must have sort 'Bool'." n));

        let splittedPars = Utils.splitListBefore (fun (_, sort) -> sort = SLoc) callPars in
        if List.length splittedPars <> 2 then
          raise (ParseException (sprintf "Function '%s' must have two parameters of sort 'Loc'." n));

        let callerVars = List.hd splittedPars in
        let calleeVars = List.hd (List.tl splittedPars) in

        (* pc is special-cased, drop from standard var list *)
        let callerVars = List.tl callerVars in
        let calleeVars = List.tl calleeVars in

        let callerVarSet = varListToSet (List.map (fun (v,_) -> v) callerVars) in
        let calleeVarSet = varListToSet (List.map (fun (v,_) -> v) calleeVars) in
        let declaredConstSet = varListToSet (List.map (fun (v,_) -> v) declaredConsts) in
        let definedIDs = VarSet.union declaredConstSet (VarSet.union callerVarSet calleeVarSet) in

        let (callerName, calleeName) = usedProcedureName n in
        
        match parseBoolTerm callDef with
        | Or transitions ->
          let parseTrans t = 
            match t with
            | And [ Eq [IId "pc" ; IId src] 
                  ; Eq [IId "pc1" ; IId dst]
                  ; rel ] ->
              let undeclVar = VarSet.fold (fun v acc -> VarSet.remove v acc) definedIDs (BoolTerm.getFreeVars rel) in
              if not(VarSet.is_empty undeclVar) then
                raise (ParseException (sprintf "Call from '%s/%s' to '%s/%s' uses undeclared variable '%s' in relation '%s'" callerName src calleeName dst (VarSet.choose undeclVar) (BoolTerm.to_string_SMTLIB rel)));
              (src, rel, dst)
            | _ ->
              raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans-decl>*)'." n));
          in
          { callerName = callerName ;
            callerVars = callerVars ;
            calleeName = calleeName ;
            calleeVars = calleeVars ;
            callTrans = List.map parseTrans transitions;
          }
        | _ ->
          raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans-decl>*)'." n));
      )
  in
  List.map parseCallDef (List.filter isCallName definedFuns)

let parseReturnDefs definedFuns declaredConsts initVars =
  let returnRE = Str.regexp "^\\(.+\\)_ret_\\(.+\\)" in
  let isReturnName (n, _, _, _) = Str.string_match returnRE n 0 in
  let usedProcedureName n = 
    ignore (Str.search_forward returnRE n 0);
    (Str.matched_group 1 n, Str.matched_group 2 n)
  in
  let parseReturnDef funDef =
    match funDef with
    | (n, [], _, _)
    | (n, [_], _, _)
    | (n, [_;_], _, _) ->
      raise (ParseException (sprintf "Function '%s' must have at least three parameters (pc, pc1, pc2)." n));
    | (n, returnPars, returnSort, returnDef) ->
      (
        if returnSort <> SBool then
          raise (ParseException (sprintf "Function '%s' must have sort 'Bool'." n));

        let splittedPars = Utils.splitListBefore (fun (_, sort) -> sort = SLoc) returnPars in
        if List.length splittedPars <> 3 then
          raise (ParseException (sprintf "Function '%s' must have three parameters of sort 'Loc'." n));

        let calleeVars = List.hd splittedPars in
        let callerPreVars = List.hd (List.tl splittedPars) in
        let callerPostVars = List.hd (List.tl (List.tl splittedPars)) in

        (* pc is special-cased, drop from standard var list *)
        let callerPreVars = List.tl callerPreVars in
        let callerPostVars = List.tl callerPostVars in
        let calleeVars = List.tl calleeVars in

        let callerPreVarSet = varListToSet (List.map (fun (v,_) -> v) callerPreVars) in
        let callerPostVarSet = varListToSet (List.map (fun (v,_) -> v) callerPostVars) in
        let calleeVarSet = varListToSet (List.map (fun (v,_) -> v) calleeVars) in
        let declaredConstSet = varListToSet (List.map (fun (v,_) -> v) declaredConsts) in
        let definedIDs = VarSet.union declaredConstSet (VarSet.union callerPreVarSet (VarSet.union callerPostVarSet calleeVarSet)) in

        let (calleeName, callerName) = usedProcedureName n in

        match parseBoolTerm returnDef with
        | Or transitions ->
          let parseTrans t = 
            match t with
            | And [ Eq [IId "pc"; IId exitL] 
                  ; Eq [IId "pc1"; IId callL]
                  ; Eq [IId "pc2"; IId returnL]
                  ; rel ] ->
              let undeclVar = VarSet.fold (fun v acc -> VarSet.remove v acc) definedIDs (BoolTerm.getFreeVars rel) in
              if not(VarSet.is_empty undeclVar) then
                raise (ParseException (sprintf "Return from '%s/%s' to '%s/%s' uses undeclared variable '%s' in relation '%s'" calleeName exitL callerName callL (VarSet.choose undeclVar) (BoolTerm.to_string_SMTLIB rel)));
              (exitL, callL, rel, returnL)
            | _ ->
              raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans3-decl>*)'." n));
          in
          { callerName = callerName ;
            callerPreVars = callerPreVars ;
            callerPostVars = callerPostVars ;
            calleeName = calleeName ;
            calleeVars = calleeVars ;
            returnTrans = List.map parseTrans transitions;
          }
        | _ ->
          raise (ParseException (sprintf "Function '%s' must be defined as '(or <trans3-decl>*)'." n));
      )
  in
  List.map parseReturnDef (List.filter isReturnName definedFuns)

let parse filename showWarnings warningsAreErrors = 
  let warn s = 
    if (showWarnings || warningsAreErrors) then 
      eprintf "%s\n" s;
    if warningsAreErrors then 
      (
        eprintf "Treating warnings as errors, exiting.\n"; 
        exit 2
      )
  in

  (* Slurp in everything: *)
  let declaredSorts = ref [] in
  let declaredConsts = ref [] in
  let definedFuns = ref [] in
  let distinctIDs = ref [] in

  let rec handleTopSexp s =
    match s with
    | List ((Atom "declare-sort")::args) ->
        handleSortDecl s args
    | List ((Atom "declare-const")::args) ->
        handleConstDecl s args
    | List ((Atom "assert")::args) ->
        handleAssert s args
    | List ((Atom "define-fun")::args) ->
        handleFunDecl s args
    | Atom a -> 
        raise (ParseException (sprintf "Atom '%s' not allowed on top level." a))
    | _ ->
        warn (sprintf "Unknown top-level atom '%s'." (to_string_hum s))
  and handleSortDecl s args =
    match args with
    | [Atom id; Atom num] ->
        declaredSorts := (id, int_of_string num)::!declaredSorts
    | _ -> 
        raise (ParseException (sprintf "Cannot parse sort declaration '%s'." (to_string_hum s)))
  and handleConstDecl s args =
    match args with
    | [Atom id; sort] ->
        declaredConsts := (id, sortOfSexp sort)::!declaredConsts
    | _ -> 
        raise (ParseException (sprintf "Cannot parse constant declaration '%s'." (to_string_hum s)))
  and handleAssert s args =
    match args with
    | [List ((Atom "distinct")::args)] ->
        distinctIDs :=
          List.map
          (function | Atom id -> id
          | l -> raise (ParseException (sprintf "Cannot parse sexp '%s' in distinct statement '%s'." (to_string_hum l) (to_string_hum s))))
          args
    | _ -> 
        warn (sprintf "Unknown assertion '%s'." (to_string_hum s))
  and handleFunDecl s args =
    match args with
    | [(Atom funName) ; (List pars) ; sort ; defTerm ] ->
        let defTerm = betaNormalize !definedFuns defTerm in
        if List.exists (fun (n, _, _, _) -> n = funName) !definedFuns then
          raise (ParseException (sprintf "Function '%s' defined twice." funName))
        else 
          let pars = List.map parseSortedVar pars in
          let rec checkForDups l =
            match l with
            | [] -> ()
            | x::xs -> 
              if List.exists (fun v -> v = x) xs then
                raise (ParseException (sprintf "Function declaration for '%s' uses parameter name '%s' twice." funName x))
              else
                checkForDups xs
          in 
          checkForDups (List.map fst pars);
          definedFuns := (funName, pars, sortOfSexp sort, defTerm)::!definedFuns
    | _ ->
        raise (ParseException (sprintf "Cannot parse function declaration '%s'." (to_string_hum s)))
  in

  let sexps = load_sexps filename in
  List.iter handleTopSexp sexps;

  checkCFGInitDef !definedFuns;
  checkCFGTrans2Def !definedFuns;

  let declaredLocations = parseLocations !declaredSorts !declaredConsts !distinctIDs in
  let initInfo = parseInitDef !definedFuns !declaredConsts in
  let procedureInfos = parseNextDefs !definedFuns !declaredConsts declaredLocations in
  let callInfos = parseCallDefs !definedFuns !declaredConsts declaredLocations in
  let returnInfos = parseReturnDefs !definedFuns !declaredConsts declaredLocations in

  if List.length returnInfos > 0 then
    checkCFGTrans3Def !definedFuns;

  (* Check global things, such that locations are associated to one procedure, and that arities and sorts for procedures appearing in several places match. *)

  let locMap =
    List.fold_left 
      (fun acc pInfo -> 
        List.fold_left (fun acc loc ->
          if LocMap.mem loc acc then
            let oName = LocMap.find loc acc in
            if oName <> pInfo.name then
              raise (ParseException (sprintf "Location '%s' is used both in procedures '%s' and '%s'." loc oName pInfo.name))
            else
              acc
          else
            LocMap.add loc pInfo.name acc)
          acc
          (Utils.concatMap (fun (l, _, l') -> [l ; l']) pInfo.transitions))
      LocMap.empty 
      procedureInfos
  in

  let sortMap =
    List.fold_left (fun acc pInfo -> ProcedureMap.add pInfo.name (List.map snd pInfo.preVars) acc) ProcedureMap.empty procedureInfos
  in
  let checkSortLists l1 l2 explString =
    List.iteri
      (fun i (s1, s2) ->
        if s1 <> s2 then raise (ParseException (sprintf "%s: %n-th variable has conflicting sorts '%s', '%s'." explString (i+2) (Sort.to_string s1) (Sort.to_string s2))))
      (List.combine l1 l2);
  in

  let checkInitInfo (i : initInfo) =
    if not(ProcedureMap.mem i.name sortMap) then
      warn (sprintf "Init in undefined procedure '%s'." i.name)
    else
      (
        if not(LocMap.mem i.location locMap) then
          warn (sprintf "Init in undefined location '%s'." i.location)
        else
          (
            let initLocProcedure = LocMap.find i.location locMap in
            if initLocProcedure <> i.name then
              raise (ParseException (sprintf "Init starts in procedure '%s', but init location '%s' belongs to procedure '%s'." i.name i.location initLocProcedure));
          );

        let initNextSorts = ProcedureMap.find i.name sortMap in
        if (List.length initNextSorts) <> (List.length i.initVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but init assumes %i vars." i.name (List.length initNextSorts) (List.length i.initVars)));
        checkSortLists 
          initNextSorts (List.map snd i.initVars)
          (sprintf "Procedure '%s': Conflict between next and init definition" i.name)
      )
  in

  let checkCallInfo (c : callInformation) =
    if not(ProcedureMap.mem c.callerName sortMap) then
      warn (sprintf "Call from undefined procedure '%s' to '%s' seen." c.callerName c.calleeName)
    else if not(ProcedureMap.mem c.calleeName sortMap) then
      warn (sprintf "Call from procedure '%s' to undefined '%s' seen." c.callerName c.calleeName)
    else
      (
        let checkCallLocations (callerLoc, _, calleeLoc) =
          if not(LocMap.mem callerLoc locMap) then
            warn (sprintf "Call from '%s' to '%s' starting in undefined location '%s'." c.callerName c.calleeName callerLoc)
          else
            (
              let callerLocProcedure = LocMap.find callerLoc locMap in
              if callerLocProcedure <> c.callerName then
                raise (ParseException (sprintf "Call from '%s' to '%s' in location '%s', which belongs to procedure '%s'." c.callerName c.calleeName callerLoc callerLocProcedure));
            );
          if not(LocMap.mem calleeLoc locMap) then
            warn (sprintf "Call from '%s' to '%s' ending in undefined location '%s'." c.callerName c.calleeName calleeLoc)
          else
            (
              let calleeLocProcedure = LocMap.find calleeLoc locMap in
              if calleeLocProcedure <> c.calleeName then
                raise (ParseException (sprintf "Call from '%s' to '%s' ending in location '%s', which belongs to procedure '%s'." c.callerName c.calleeName callerLoc calleeLocProcedure));
            );
        in
        List.iter checkCallLocations c.callTrans;

        let callerNextSorts = ProcedureMap.find c.callerName sortMap in
        if (List.length callerNextSorts) <> (List.length c.callerVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but a call to '%s' with %i vars is defined." c.callerName (List.length callerNextSorts) c.calleeName (List.length c.callerVars)));
        checkSortLists 
          callerNextSorts (List.map snd c.callerVars)
          (sprintf "Procedure '%s': Conflict between next and call to '%s' definition" c.callerName c.calleeName);

        let calleeNextSorts = ProcedureMap.find c.calleeName sortMap in
        if (List.length calleeNextSorts) <> (List.length c.calleeVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but a call from '%s' with %i vars is defined." c.calleeName (List.length calleeNextSorts) c.callerName (List.length c.calleeVars)));
        checkSortLists 
          calleeNextSorts (List.map snd c.calleeVars)
          (sprintf "Procedure '%s': Conflict between next and call from location '%s' definition" c.calleeName c.callerName);
      )
  in

  let checkReturnInfo r =
    if not(ProcedureMap.mem r.calleeName sortMap) then
      warn (sprintf "Return from undefined procedure '%s' to '%s' seen." r.calleeName r.callerName)
    else if not(ProcedureMap.mem r.callerName sortMap) then
      warn (sprintf "Return from procedure '%s' to undefined '%s' seen." r.calleeName r.callerName)
    else
      (
        let checkReturnLocations (exitLoc, callLoc, _, returnLoc) =
          if not(LocMap.mem exitLoc locMap) then
            warn (sprintf "Return from '%s' to '%s' in undefined location '%s'." r.calleeName r.callerName exitLoc)
          else
            (
              let exitLocProcedure = LocMap.find exitLoc locMap in
              if exitLocProcedure <> r.calleeName then
                raise (ParseException (sprintf "Return from '%s' to '%s' in location '%s', which belongs to procedure '%s'." r.calleeName r.callerName exitLoc exitLocProcedure));
            );

          if not(LocMap.mem callLoc locMap) then
            warn (sprintf "Return from '%s' to '%s' for call in undefined location '%s'." r.calleeName r.callerName callLoc)
          else
            (
              let callLocProcedure = LocMap.find callLoc locMap in
              if callLocProcedure <> r.callerName then
                raise (ParseException (sprintf "Return from '%s' to '%s' for call in location '%s', which belongs to procedure '%s'." r.calleeName r.callerName callLoc callLocProcedure));
            );

          if not(LocMap.mem returnLoc locMap) then
            warn (sprintf "Return from '%s' to '%s' to undefined location '%s'." r.calleeName r.callerName returnLoc)
          else
            (
              let returnLocProcedure = LocMap.find returnLoc locMap in
              if returnLocProcedure <> r.callerName then
                raise (ParseException (sprintf "Return from '%s' to '%s' to location '%s', which belongs to procedure '%s'." r.calleeName r.callerName returnLoc returnLocProcedure));
            );
        in
        List.iter checkReturnLocations r.returnTrans;

        let callerNextSorts = ProcedureMap.find r.callerName sortMap in
        if (List.length callerNextSorts) <> (List.length r.callerPreVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but a return from '%s' with %i pre-vars is defined." r.callerName (List.length callerNextSorts) r.calleeName (List.length r.callerPreVars)));
        checkSortLists 
          callerNextSorts (List.map snd r.callerPreVars)
          (sprintf "Procedure '%s': Conflict between next and pre-vars of return from '%s'" r.callerName r.calleeName);

        if (List.length callerNextSorts) <> (List.length r.callerPostVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but a return from '%s' with %i post-vars is defined." r.callerName (List.length callerNextSorts) r.calleeName (List.length r.callerPostVars)));
        checkSortLists 
          callerNextSorts (List.map snd r.callerPostVars)
          (sprintf "Procedure '%s': Conflict between next and post-vars of return from '%s'" r.callerName r.calleeName);

        let calleeNextSorts = ProcedureMap.find r.calleeName sortMap in
        if (List.length calleeNextSorts) <> (List.length r.calleeVars) then
          raise (ParseException (sprintf "Procedure '%s' has %i vars, but a return to '%s' with %i vars is defined." r.calleeName (List.length calleeNextSorts) r.callerName (List.length r.calleeVars)));
        checkSortLists 
          calleeNextSorts (List.map snd r.calleeVars)
          (sprintf "Procedure '%s': Conflict between next and vars of return to '%s'" r.calleeName r.callerName);
      )
  in

  let usedLocations = Utils.concatMap (fun (l, _, l') -> [l; l']) (Utils.concatMap (fun pInfo -> pInfo.transitions) procedureInfos) in
  match Utils.tryFind (fun l -> not(List.exists (fun l' -> l = l') declaredLocations)) usedLocations with
  | Some l ->
      raise (ParseException (sprintf "Location '%s' used in transition, but not declared." l))
  | None ->
      ();

  checkInitInfo initInfo;
  List.iter checkCallInfo callInfos;
  List.iter checkReturnInfo returnInfos;

  Program.create initInfo procedureInfos callInfos returnInfos
            
