(*
  IntTRS output

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
open Printf
open Term

exception IntTRSOutputException of string

let rec constraintToIntTRSString c =
  match c with
  | BoolTerm.True -> "(0 <= 0)"
  | BoolTerm.False -> "(1 <= 0)"
  | BoolTerm.And args ->
    String.concat " /\\ " (List.map constraintToIntTRSString args) 
  | BoolTerm.Exists (_, body) -> (* Fresh variables are implictly existentially quantified in conditions *)
    constraintToIntTRSString body
  | BoolTerm.Forall _ ->
      raise (IntTRSOutputException "Cannot export universally quantified formula to IntTRS format.")
  | BoolTerm.Not _ ->
      raise (IntTRSOutputException "Found unexpected negation in normalized constraint")
  | BoolTerm.Or args ->
      raise (IntTRSOutputException "Found unexpected disjunct in normalized constraint")
  | a -> BoolTerm.to_string_infix a

let output p terminationOnly =
  if Program.hasNonIntVars p then
    raise (IntTRSOutputException "IntTRS format does not support non-Int variables.");
  if terminationOnly && List.length (Program.getAllCalls p) > 0 then
    raise (IntTRSOutputException "IntTRS format does not support true recursion. A termination-preserving abstraction can be activated with --termination-only.");

  let ppSortedVarList l = String.concat ", " (List.map fst l) in
  let normalizeTrans (l, rel, l') =
    match (BoolTerm.toDNF rel) with
    | BoolTerm.Or args -> List.map (fun c -> (l, c, l')) args
    | relNF -> [(l, relNF, l')]
  in


  let printTrans l preVars l' postVars constr =
    printf "%s(%s) -> %s(%s) [ %s ]\n" 
      l (ppSortedVarList preVars)  
      l' (ppSortedVarList postVars)  
      (constraintToIntTRSString constr);
  in

  let printProcedure p =
    let preVars = p.preVars in
    let postVars = p.postVars in
    List.iter (fun (l, rel, l') -> printTrans l preVars l' postVars rel) (Utils.concatMap normalizeTrans p.transitions)
  in

  (* A call is represented as a simple transition, we forget about the stack *)
  let printCall c =
    let preVars = c.callerVars in
    let postVars = c.calleeVars in
    List.iter (fun (l, rel, l') -> printTrans l preVars l' postVars rel) (Utils.concatMap normalizeTrans c.callTrans)
  in

  (* A return is represented as a simple transition from pre-state to
     post-state. We ignore the new values obtained in r.calleeVars and
     do not bind these variables at all on the lhs -- they are then
     implicitly universally quantified.*)
  let printReturn r =
    let preVars = r.callerPreVars in
    let postVars = r.callerPostVars in
    
    List.iter 
      (fun (_, callLoc, r, returnLoc) -> 
        List.iter (fun (l, rel, l') -> printTrans l preVars l' postVars rel)
        (normalizeTrans (callLoc, r, returnLoc)))
      r.returnTrans
  in

  List.iter printProcedure (Program.getAllProcedures p);
  List.iter printCall (Program.getAllCalls p);
  List.iter printReturn (Program.getAllReturns p);
