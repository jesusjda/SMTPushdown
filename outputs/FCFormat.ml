(*
  Fc output

  @author Jesus Domenech

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

open Program
open Printf
open Term
       
module LocMap = Map.Make(String)
module VarMap = Map.Make(String)
       
exception FcOutputException of string

let var_pp_map = ref VarMap.empty
let t2_evil_re = Str.regexp "[^a-zA-Z0-9_']"
let t2_var_pp v =
  if not(VarMap.mem v !var_pp_map) then
    (
      let rec find_fresh_name v =
        if VarMap.mem v !var_pp_map then
          find_fresh_name (v ^ "'")
        else
          v
      in
      let newVName = find_fresh_name (Str.global_replace t2_evil_re "_" v) in
      var_pp_map := VarMap.add v newVName !var_pp_map
    );
  VarMap.find v !var_pp_map
let rec find e = function
  | [] -> false
  | h::t -> h = e || find e t
let rec unique_append_list l1 l2 =
  match l1 with
  | [] -> l2
  | h::t -> if find h l2 then unique_append_list t l2
            else unique_append_list t (h::l2)
let getExistentialVariables c =
  match c with
  | BoolTerm.Exists (vars, _) -> vars
  | _ -> []

let add_prime lv =
  List.map (fun (v) ->
      t2_var_pp (v ^ "'")) lv
let rec impliesEquality c v1 v2 =
  match c with
  | BoolTerm.Eq eqs ->
    let isVar v t =
      match t with
      | IntTerm.IId i -> i = v
      | _ -> false
    in
    List.exists (isVar v1) eqs && List.exists (isVar v2) eqs
  | BoolTerm.And conjuncts ->
    List.fold_left (fun res t -> res || (impliesEquality t v1 v2)) false conjuncts
  | BoolTerm.Or (disj::disjuncts) ->
    List.fold_left (fun res t -> res && (impliesEquality t v1 v2)) (impliesEquality disj v1 v2) disjuncts
  | BoolTerm.Exists (boundVars, t)
  | BoolTerm.Forall (boundVars, t) ->
    if not(List.exists (fun (i, _) -> v1 = i || v2 = i) boundVars) then
      impliesEquality t v1 v2
    else
      false
  | _ -> false


let rec constraintToFcString c =
  match c with
  | BoolTerm.True -> "    0 <= 0"
  | BoolTerm.False -> "    1 <= 0"
  | BoolTerm.And args ->
     ("    " ^ String.concat ",\n    " (List.map constraintToFcString args) )
  | BoolTerm.Exists (_, body) -> (* Fresh variables are implictly existentially quantified in conditions *)
     constraintToFcString body
  | BoolTerm.Forall _ ->
     raise (FcOutputException "Cannot export universally quantified formula to Fc format.")
  | BoolTerm.Not _ ->
     raise (FcOutputException "Found unexpected negation in normalized constraint")
  | BoolTerm.Or args ->
     raise (FcOutputException "Found unexpected disjunct in normalized constraint")
  | a -> BoolTerm.to_string_infix a

let output p terminationOnly =
  if Program.hasNonIntVars p then
    raise (FcOutputException "Fc format does not support non-Int variables.");
  if terminationOnly && List.length (Program.getAllCalls p) > 0 then
    raise (FcOutputException "Fc format does not support true recursion. A termination-preserving abstraction can be activated with --termination-only.");
  
  let normalizeTrans (l, rel, l') =
    match (BoolTerm.toDNF rel) with
    | BoolTerm.Or args -> List.map (fun c -> (l, c, l')) args
    | relNF -> [(l, relNF, l')]
  in
  let computeUnchangedVars preVars postVars r =
    List.fold_left2
      (fun (resPre, resPost) preV postV ->
        if impliesEquality r preV postV then
          (resPre, resPost)
        else
          (preV::resPre, postV::resPost))
      ([], [])
      preVars
      postVars in

  let printTrans t l l' constr preVars postVars =
    let preVars = List.map fst preVars in
    let postVars = List.map fst postVars in
    let (unchangedPreVars, unchangedPostVars) = computeUnchangedVars preVars postVars constr in
    printf ".trans %s : %s -> %s{\n" t l l';
    List.iter2 (fun preV postV -> printf "    %s = %s,\n" (t2_var_pp preV) (t2_var_pp postV))
      (Utils.removeAll (=) preVars unchangedPreVars)
      (Utils.removeAll (=) postVars unchangedPostVars);
    printf "%s \n}\n"(constraintToFcString constr);
  in

  (*let rec printTransList tag (id : int) (trans: transition list) =
    match trans with
      [] -> ""
    | (l, constr, l')::ll -> (printTrans (sprintf "%s%d" tag id) l l' constr);
                             printTransList tag (id+1) ll
  in*)
  let printProcedure (p : procedureInformation) =
    let preVars = p.preVars in
    let postVars = p.postVars in
    List.iteri (fun i (l, rel, l') -> 
        printTrans (sprintf "t%d" i) l l' rel preVars postVars
      ) (Utils.concatMap normalizeTrans p.transitions);
    
  in
  (*(String.concat ",>>" (List.iter l))*)
  let getVarsProcs listproc preV postV =
    List.fold_left (fun (resPre, resPost) p ->
        let preVars = List.map fst p.preVars in
        let postVars = List.map fst p.postVars in
        let rec computeExVars trans =
          match trans with
          | [] -> []
          | (l,rel,l')::r -> unique_append_list (List.map fst (getExistentialVariables rel)) (computeExVars r)
        in
        let exVars = computeExVars p.transitions in          
        let (resPre,resPost) = (
            unique_append_list resPre (preVars),
            unique_append_list resPost (postVars)
          )
        in
        (
          unique_append_list resPre exVars,
          unique_append_list resPost (add_prime exVars)
        )
      ) (preV, postV) listproc
  in
  (*  let (pre, post) = printVars (Program.getAllProcedures p) (Program.getAllCalls p) (Program.getAllReturns p)  *)
  let (pre, post) = getVarsProcs (Program.getAllProcedures p) [] []
  in
  printf ".vars {\n%s\n}\n" ("  " ^ String.concat ", " pre );
  printf "\n.pvars {\n%s\n}\n"("  " ^ String.concat ", " post );
  printf "\n.initnode: %s\n" ((fun(p : initInfo) -> p.initLoc) (Program.getInitInfo p));
  List.iter printProcedure (Program.getAllProcedures p);
(*  List.iter printCall (Program.getAllCalls p);
  List.iter printReturn (Program.getAllReturns p);*)
