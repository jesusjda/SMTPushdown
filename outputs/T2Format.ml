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

exception T2OutputException of string

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
  | a -> BoolTerm.to_string_infix a

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

  let printTrans l preVars l' postVars r =
    printf "FROM: %i;\n" (LocMap.find l locMap);
    List.iter (fun (v, _) -> printf " %s := nondet();\n" v) postVars;
    printf " assume(%s);\n" (constraintToT2String r);
    List.iter2 (fun (preV, _) (postV, _) -> printf " %s := %s;\n" preV postV) preVars postVars;
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
      match Utils.tryFind (fun p -> p.name = calleeProcName) (Program.getAllProcedures p) with
      | Some p ->
	printf "FROM: %i;\n" (LocMap.find l locMap);
	List.iter (fun (v, _) -> printf " %s := nondet();\n" v) postVars;
	printf " assume(%s);\n" (constraintToT2String r);
	List.iter2 (fun (preV, _) (postV, _) -> printf " %s := %s;\n" preV postV) p.preVars postVars;
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