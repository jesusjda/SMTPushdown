(*
  T2 output

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

open Program
open Term
open Printf

module LocMap = Map.Make(String)
module VarMap = Map.Make(String)

exception T2OutputException of string

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

(* Syntactic, weak check if a constaint implies equality v1 = v2 (by searching for a (v1 = v2) *)
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
     

let rec constraintToT2String c =
  match c with
  | BoolTerm.True -> "(0 <= 0)"
  | BoolTerm.False -> "(1 <= 0)"
  | BoolTerm.And args ->
    String.concat " && " (List.map constraintToT2String args)
  | BoolTerm.Or args ->
    "(" ^ (String.concat " || " (List.map constraintToT2String args)) ^ ")"
  | BoolTerm.Not t -> sprintf "!(%s)" (constraintToT2String t)
  | BoolTerm.Exists (_, body) -> 
    (* implicitly existentially quantified *)
    constraintToT2String body
  | BoolTerm.Forall _ ->
    raise (T2OutputException "Cannot export universially quantified formula to T2 format.")
  | a -> BoolTerm.to_string_infix_vpp a t2_var_pp

let output p terminationOnly =
  if Program.hasNonIntVars p then
    raise (T2OutputException "T2 format does not support non-Int variables.");
  if terminationOnly && List.length (Program.getAllCalls p) > 0 then
    raise (T2OutputException "T2 format does not support recursion. A termination-preserving abstraction can be activated with --termination.");

  let locMap = List.fold_left 
    (fun acc (l, id) -> LocMap.add l id acc)
    LocMap.empty
    (Utils.mapi (fun i l -> (l, i)) (Program.getAllLocations p))
  in

  let computeUnchangedVars preVars postVars r =
    List.fold_left2 
      (fun (resPre, resPost) preV postV ->
        if impliesEquality r preV postV then 
          (preV::resPre, postV::resPost)
        else
          (resPre, resPost))
      ([], [])
      preVars
      postVars in

  let printTrans l preVars l' postVars r =
    (* Project out sorts. *)
    let preVars = List.map fst preVars in
    let postVars = List.map fst postVars in
    printf "FROM: %i;\n" (LocMap.find l locMap);
    let (unchangedPreVars, unchangedPostVars) = computeUnchangedVars preVars postVars r in
    List.iter (fun v -> printf " %s := nondet();\n" (t2_var_pp v)) postVars;
    printf " assume(%s);\n" (constraintToT2String r);
    List.iter2 (fun preV postV -> printf " %s := %s;\n" (t2_var_pp preV) (t2_var_pp postV)) 
      (Utils.removeAll (=) preVars unchangedPreVars)
      (Utils.removeAll (=) postVars unchangedPostVars);
    printf "TO: %i;\n\n" (LocMap.find l' locMap);
  in

  let printProcedure p =
    let preVars = p.preVars in
    let postVars = p.postVars in
    List.iter (fun (l, rel, l') -> printTrans l preVars l' postVars rel) p.transitions
  in

  (* A call is represented as a simple transition, we forget about the stack *)
  let printCall c =
    let printCallTrans l preVars l' postVars r calleeProcName =
    (* Project out sorts. *)
      match Utils.tryFind (fun p -> p.name = calleeProcName) (Program.getAllProcedures p) with
      | Some p ->
        let preVars = List.map fst p.preVars in
        let postVars = List.map fst postVars in
	printf "FROM: %i;\n" (LocMap.find l locMap);
        let (unchangedPreVars, unchangedPostVars) = computeUnchangedVars preVars postVars r in
	List.iter (fun v -> printf " %s := nondet();\n" (t2_var_pp v)) postVars;
	printf " assume(%s);\n" (constraintToT2String r);
	List.iter2 (fun preV postV -> printf " %s := %s;\n" (t2_var_pp preV) (t2_var_pp postV))
          (Utils.removeAll (=) preVars unchangedPreVars)
          (Utils.removeAll (=) postVars unchangedPostVars);
	printf "TO: %i;\n\n" (LocMap.find l' locMap);
      | None -> () (* Method has no next, just skip call *)
    in
    let preVars = c.callerVars in
    let postVars = c.calleeVars in
    List.iter (fun (l, rel, l') -> printCallTrans l preVars l' postVars rel c.calleeName) c.callTrans
  in

  (* A return is represented as a simple transition from pre-state to
     post-state. We ignore the new values obtained in r.calleeVars and
     do not bind these variables at all on the lhs -- they are then
     implicitly universally quantified.*)
  let printReturn r =
    let preVars = r.callerPreVars in
    let postVars = r.callerPostVars in
    
    List.iter (fun (_, callLoc, r, returnLoc) -> printTrans callLoc preVars returnLoc postVars r) r.returnTrans
  in

  printf "START: %i;\n\n" (LocMap.find (Program.getInitInfo p).location locMap);
  List.iter printProcedure (Program.getAllProcedures p);
  List.iter printCall (Program.getAllCalls p);
  List.iter printReturn (Program.getAllReturns p);
