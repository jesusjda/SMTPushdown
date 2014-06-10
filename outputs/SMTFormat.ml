(*
  SMT output

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
open Big_int
open Sexplib.Sexp

let output p =
  let ppSortedVarList l = String.concat " " (List.map (fun (v, s) -> sprintf "(%s %s)" v (Sort.to_string s)) l) in

  let printInitInfo i =
    let initVarString = ppSortedVarList i.initVars in

    printf "(define-fun init_%s ( (pc Loc) %s ) Bool\n" i.name initVarString;
    printf "  (cfg_init pc %s %s))\n\n" i.location (BoolTerm.to_string_SMTLIB i.constr);
  in

  let printProcedureInfo p =
    let preVarString = ppSortedVarList p.preVars in
    let postVarString = ppSortedVarList p.postVars in

    printf "(define-fun next_%s (\n" p.name;
    printf "                 (pc Loc) %s\n" preVarString;
    printf "                 (pc1 Loc) %s\n" postVarString;
    printf "             ) Bool\n";
    printf "  (or\n";
    List.iter 
      (fun (l, r, l') ->
        printf "    (cfg_trans2 pc %s pc1 %s %s)\n" l l' (BoolTerm.to_string_SMTLIB r))
      p.transitions;
    printf "  )\n)\n";
  in

  let printCallInfo c = 
    let callerVarString = ppSortedVarList c.callerVars in
    let calleeVarString = ppSortedVarList c.calleeVars in

    printf "(define-fun %s_call_%s (\n" c.callerName c.calleeName;
    printf "                 (pc Loc) %s\n" callerVarString;
    printf "                 (pc1 Loc) %s\n" calleeVarString;
    printf "             ) Bool\n";
    printf "  (or\n";
    List.iter 
      (fun (l, r, l') ->
        printf "    (cfg_trans2 pc %s pc1 %s %s)\n" l l' (BoolTerm.to_string_SMTLIB r))
      c.callTrans;
    printf "  )\n)\n";
  in

  let printReturnInfo r = 
    let calleeVarString = ppSortedVarList r.calleeVars in
    let callerPreVarString = ppSortedVarList r.callerPreVars in
    let callerPostVarString = ppSortedVarList r.callerPostVars in

    printf "(define-fun %s_ret_%s (\n" r.callerName r.calleeName;
    printf "                 (pc Loc) %s\n" calleeVarString;
    printf "                 (pc1 Loc) %s\n" callerPreVarString;
    printf "                 (pc2 Loc) %s\n" callerPostVarString;
    printf "             ) Bool\n";
    printf "  (or\n";
    List.iter 
      (fun (exitLoc, callLoc, r, returnLoc) ->
        printf "    (cfg_trans3 pc %s pc1 %s pc2 %s %s)\n" exitLoc callLoc returnLoc (BoolTerm.to_string_SMTLIB r))
      r.returnTrans;
    printf "  )\n)\n";
  in


  let locations = Program.getAllLocations p in

  printf "(declare-sort Loc 0)\n";
  List.iter (printf "(declare-const %s Loc)\n") locations;
  printf "(assert (distinct %s))\n\n" (String.concat " " locations);

  printf "(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool\n";
  printf "  (and (= pc src) rel))\n\n";

  printf "(define-fun cfg_trans2 ( (pc Loc) (src Loc)\n";
  printf "                         (pc1 Loc) (dst Loc)\n";
  printf "                         (rel Bool) ) Bool\n";
  printf "  (and (= pc src) (= pc1 dst) rel))\n\n";

  printf "(define-fun cfg_trans3 ( (pc Loc) (exit Loc)\n";
  printf "                         (pc1 Loc) (call Loc)\n";
  printf "                         (pc2 Loc) (return Loc)\n";
  printf "                         (rel Bool) ) Bool\n";
  printf "  (and (= pc exit) (= pc1 call) (= pc2 return) rel))\n\n";

  printInitInfo (Program.getInitInfo p);
  List.iter printProcedureInfo (Program.getAllProcedures p);
  List.iter printCallInfo (Program.getAllCalls p);
  List.iter printReturnInfo (Program.getAllReturns p);
