(*
  Fc output

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

exception FcOutputException of string

let rec constraintToFcString c =
  match c with
  | BoolTerm.True -> "\t(0 <= 0)"
  | BoolTerm.False -> "\t(1 <= 0)"
  | BoolTerm.And args ->
    ("\t" ^ String.concat ",\n\t" (List.map constraintToFcString args) )
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


  let printTrans t l l' constr =
    printf ".trans %s : %s -> %s{\n%s \n}\n" 
      t l l' (constraintToFcString constr);
  in

  let printProcedure (p : procedureInformation) =
    List.iteri (i (fun (l, rel, l') -> printTrans (sprintf "t%d" i) l  l'  rel) (Utils.concatMap normalizeTrans p.transitions))
  in

  (* A call is represented as a simple transition, we forget about the stack *)
  let printCall (c : callInformation) =
    List.iteri (fun (i, l, rel, l') -> printTrans (sprintf "c%d" i) l  l'  rel) (Utils.concatMap normalizeTrans c.callTrans)
  in

  (* A return is represented as a simple transition from pre-state to
     post-state. We ignore the new values obtained in r.calleeVars and
     do not bind these variables at all on the lhs -- they are then
     implicitly universally quantified.*)
  let printReturn (r : returnInformation) =
      
    List.iteri 
      (fun (i,_, callLoc, r, returnLoc) -> 
        List.iteri (fun (j,l, rel, l') -> printTrans (sprintf "r%dr%d" i j) l  l'  rel)
        (normalizeTrans (callLoc, r, returnLoc)))
      r.returnTrans
  in

  List.iter printProcedure (Program.getAllProcedures p);
  List.iter printCall (Program.getAllCalls p);
  List.iter printReturn (Program.getAllReturns p);
