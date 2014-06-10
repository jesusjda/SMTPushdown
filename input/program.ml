(*
  Internal program representation

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

open Term

type procedureName = string
type loc = string
type transition = loc * BoolTerm.t * loc
type returnTransition = loc * loc * BoolTerm.t * loc
type initInfo = { name : procedureName ;
                  location : loc ;
                  initVars : sortedVar list ;
                  constr : BoolTerm.t ;
                }
type procedureInformation = { name : procedureName ;
                              preVars : sortedVar list ;
                              postVars : sortedVar list ;
                              transitions : transition list ;
                         }
type callInformation = { callerName : procedureName ;
                         callerVars : sortedVar list ;
                         calleeName : procedureName ;
                         calleeVars : sortedVar list ;
                         callTrans : transition list ;
                       }
type returnInformation = { callerName : procedureName ;
                           callerPreVars : sortedVar list ;
                           callerPostVars : sortedVar list ;
                           calleeName : procedureName ;
                           calleeVars : sortedVar list ;
                           returnTrans : returnTransition list ;
                         }

module Program : sig
  type program = private { init : initInfo ; 
                           procedures : procedureInformation list ;
                           calls : callInformation list ;
                           returns : returnInformation list ;
                         }
  val create : initInfo -> procedureInformation list -> callInformation list -> returnInformation list -> program
  val getInitInfo : program -> initInfo
  val getAllProcedures : program -> procedureInformation list
  val getAllCalls : program -> callInformation list
  val getAllReturns : program -> returnInformation list
  val getAllLocations : program -> loc list
  val hasNonIntVars : program -> bool
end = struct
  type program = { init : initInfo ;
                   procedures : procedureInformation list ;
                   calls : callInformation list ;
                   returns : returnInformation list ;
                 }
  let create i ps cs rs =
    { init = i ; procedures = ps ; calls = cs ; returns = rs ; }
  let getInitInfo p = p.init
  let getAllProcedures p = p.procedures
  let getAllCalls p = p.calls
  let getAllReturns p = p.returns
  let getAllLocations p =
    let procLocs = List.fold_left (fun acc pInfo -> (Utils.concatMap (fun (l, _, l') -> [l; l']) pInfo.transitions) @ acc) [] p.procedures in
    let allLocs = List.fold_left (fun acc rInfo -> (Utils.concatMap (fun (l, l', _, l'') -> [l; l'; l'']) rInfo.returnTrans) @ acc) procLocs p.returns in
    Utils.deldups allLocs
  let hasNonIntVars p =
    let isIntSorted (_, s) = s <> Sort.SInt in
    List.exists (fun pInfo -> (List.exists isIntSorted pInfo.preVars) || (List.exists isIntSorted pInfo.postVars)) p.procedures
end  

