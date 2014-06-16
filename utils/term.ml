(*
  Internal representation of terms

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

open Big_int
open Utils
open Printf

module Sort = struct
  type t =
  | SInt
  | SBool
  | SLoc

  let to_string s =
    match s with
    | SInt -> "Int"
    | SBool -> "Bool"
    | SLoc -> "Loc"
end

type identifier = string
type sortedVar = identifier * Sort.t

module type Term = sig
  type t
  val sort : Sort.t

  val to_string_infix : t -> string
  val to_string_SMTLIB : t -> string
  val normalize : t -> bool -> t
  val getFreeVars : t -> identifier list
end

module IntTerm = struct
  type t =
  | IId of identifier
  | Const of big_int
  | Mul of t * t
  | Add of t * t
  | Sub of t * t
  | Neg of t

  let sort = Sort.SInt

  let to_string_infix e =
    let rec to_string_infix' force e =
      let protect strength force s =
	if strength >= force then s else "(" ^ s ^ ")"
      in
      match e with
      | Const i -> string_of_big_int i
      | IId(v) -> v
      | Neg(e) -> "-" ^ (to_string_infix' 3 e)
      | Add (e1,e2) -> 
	let larg = to_string_infix' 1 e1 in
	let rarg = to_string_infix' 1 e2 in
	if e1 = Const(zero_big_int) then
	  protect 1 force rarg
	else if e2 = Const(zero_big_int) then
	  protect 1 force larg
	else
	  (
	    match e2 with
	    | Mul(Const(c), e22) -> 
	      (
		if c = (minus_big_int unit_big_int) then
		  protect 1 force (to_string_infix' 1 e1 ^ "-" ^ to_string_infix' 2 e22)
		else if lt_big_int c zero_big_int then
		  protect 1 force (to_string_infix' 1 e1 ^ "-" ^ to_string_infix' 2 (Mul(Const(minus_big_int c), e22)))
		else
		  protect 1 force (to_string_infix' 1 e1 ^ "+" ^ to_string_infix' 1 e2)
	      )
	    | _ -> protect 1 force (to_string_infix' 1 e1 ^ "+" ^ to_string_infix' 1 e2)
	  )
      | Sub(e1,e2) -> protect 1 force (to_string_infix' 1 e1 ^ "-" ^ to_string_infix' 2 e2)
      | Mul(e1,e2) -> protect 2 force (to_string_infix' 2 e1 ^ "*" ^ to_string_infix' 2 e2)
    in
    to_string_infix' 0 e

  let rec to_string_SMTLIB t =
    match t with
    | IId v -> v
    | Const c -> string_of_big_int c
    | Mul (a,b) -> sprintf "(* %s %s)" (to_string_SMTLIB a) (to_string_SMTLIB b)
    | Add (a,b) -> sprintf "(+ %s %s)" (to_string_SMTLIB a) (to_string_SMTLIB b)
    | Sub (a,b) -> sprintf "(- %s %s)" (to_string_SMTLIB a) (to_string_SMTLIB b)
    | Neg (a) -> sprintf "(- %s)" (to_string_SMTLIB a)

  let normalize c _ =
    match c with
    | Add(Const c1, Const c2) -> Const (add_big_int c1 c2)
    | Sub(Const c1, Const c2) -> Const (sub_big_int c1 c2)
    | Mul(Const c1, Const c2) -> Const (mult_big_int c1 c2)
    | _ -> c

  let rec getFreeVars t =
    match t with
    | IId v -> VarSet.singleton v
    | Const _ -> VarSet.empty
    | Mul (a,b) | Add (a,b) | Sub (a,b) ->
      VarSet.union (getFreeVars a) (getFreeVars b)
    | Neg (a) ->
      getFreeVars a
end

module BoolTerm = struct
  type t =
  (* Core theory: *)
  | True
  | False
  | BId of identifier
  | Not of t
  | And of t list
  | Or of t list
  | Exists of sortedVar list * t
  | Forall of sortedVar list * t
(* TODO: Maybe support these, too?
  | Xor of term list
  | Impl of term list
*)

  (* Int theory, bool-sorted *)
  | Eq of IntTerm.t list
  | Lt of IntTerm.t * IntTerm.t
  | Le of IntTerm.t * IntTerm.t
  | Gt of IntTerm.t * IntTerm.t
  | Ge of IntTerm.t * IntTerm.t

  let sort = Sort.SBool

  let to_string_infix e =
    let rec to_string_infix' force e =
      let protect strength force s =
	if strength >= force then s else "(" ^ s ^ ")"
      in
      match e with
      | True -> "true"
      | False -> "false"
      | BId(v) -> v
      | Not(e) -> "not(" ^ (to_string_infix' 0 e) ^ ")"
      | Or [] -> "false"
      | Or (a1::[]) -> protect 1 force (to_string_infix' 1 a1)
      | Or (a1::args) -> protect 1 force (to_string_infix' 1 a1 ^ " || " ^ to_string_infix' 1 (Or args))
      | And [] -> "true"
      | And (a1::[]) -> protect 2 force (to_string_infix' 2 a1)
      | And (a1::args) -> protect 2 force (to_string_infix' 2 a1 ^ " && " ^ to_string_infix' 2 (And args))
      | Exists (vars, body) -> protect 0 force (Printf.sprintf "Ex. %s: %s" (String.concat ", " (List.map fst vars)) (to_string_infix' 0 body))
      | Forall (vars, body) -> protect 0 force (Printf.sprintf "For all %s: %s" (String.concat ", " (List.map fst vars)) (to_string_infix' 0 body))
      | Eq args -> String.concat " = " (List.map IntTerm.to_string_infix args)
      | Le (a, b) -> (IntTerm.to_string_infix a) ^ " <= " ^ (IntTerm.to_string_infix b)
      | Ge (a, b) -> (IntTerm.to_string_infix a) ^ " >= " ^ (IntTerm.to_string_infix b)
      | Lt (a, b) -> (IntTerm.to_string_infix a) ^ " < "  ^ (IntTerm.to_string_infix b)
      | Gt (a, b) -> (IntTerm.to_string_infix a) ^ " > "  ^ (IntTerm.to_string_infix b)
    in
    to_string_infix' 0 e

  let rec to_string_SMTLIB t =
    match t with
    | True -> "true"
    | False -> "false"
    | BId v -> v
    | Not arg -> sprintf "(not %s)" (to_string_SMTLIB arg)
    | And args -> sprintf "(and %s)" (String.concat " " (List.map to_string_SMTLIB args))
    | Or args -> sprintf "(or %s)" (String.concat " " (List.map to_string_SMTLIB args))
    | Exists (args, body) -> sprintf "(exists ( %s ) %s)" (String.concat " " (List.map (fun (i, s) -> sprintf "(%s %s)" i (Sort.to_string s)) args)) (to_string_SMTLIB body)
    | Forall (args, body) -> sprintf "(forall ( %s ) %s)" (String.concat " " (List.map (fun (i, s) -> sprintf "(%s %s)" i (Sort.to_string s)) args)) (to_string_SMTLIB body)

    | Eq args -> sprintf "(= %s)" (String.concat " " (List.map IntTerm.to_string_SMTLIB args))
    | Lt (a,b) -> sprintf "(< %s %s)" (IntTerm.to_string_SMTLIB a) (IntTerm.to_string_SMTLIB b)
    | Le (a,b) -> sprintf "(<= %s %s)" (IntTerm.to_string_SMTLIB a) (IntTerm.to_string_SMTLIB b)
    | Gt (a,b) -> sprintf "(> %s %s)" (IntTerm.to_string_SMTLIB a) (IntTerm.to_string_SMTLIB b)
    | Ge (a,b) -> sprintf "(>= %s %s)" (IntTerm.to_string_SMTLIB a) (IntTerm.to_string_SMTLIB b)

  let rec normalize t aggressive =
    match t with
    | Not(And args) -> 
      normalize (Or(List.map (fun t -> (Not t)) args)) aggressive
    | Not(Or args) -> 
      normalize (And(List.map (fun t -> (Not t)) args)) aggressive
    | Not(Forall (vars, body)) ->
      Exists (vars, normalize (Not(body)) aggressive)
    | Not(Exists (vars, body)) ->
      Forall (vars, normalize (Not(body)) aggressive)
    | Not(Le(a,b)) ->
      Le(b, IntTerm.normalize (IntTerm.Sub(a, IntTerm.Const unit_big_int)) aggressive)
    | Not(Not c) -> normalize c aggressive
    | Not(BId _)
    | Not(True)
    | Not(False) -> t
    | Not(a) ->
      normalize (Not (normalize a true)) aggressive (* the inner call turns everything into one of the cases above *)
    | And [a] ->
      normalize a aggressive
    | And args ->
      let flattenedArgs = 
	List.fold_left 
	  (fun acc t ->
	    match t with
	    | And otherargs -> otherargs@acc
	    | _ -> t::acc)
	  []
	  (List.map (fun a -> normalize a aggressive) args)
      in And(flattenedArgs)
    | Or [a] ->
      normalize a aggressive
    | Or args ->
      let flattenedArgs =
	List.fold_left 
	  (fun acc t ->
	    match t with
	    | Or otherargs -> otherargs@acc
	    | _ -> t::acc)
	  []
	  (List.map (fun a -> normalize a aggressive) args)
      in Or(flattenedArgs)
    | Forall (vars, body) ->
      Forall (vars, normalize body aggressive)
    | Exists (vars, body) ->
      Exists (vars, normalize body aggressive)
    | BId _
    | True
    | False ->
      t

    | Eq (a::b::[]) ->
      if aggressive then
	And [Le (IntTerm.normalize a aggressive, IntTerm.normalize b aggressive) 
	    ; Le (IntTerm.normalize b aggressive, IntTerm.normalize a aggressive)]
      else
	Eq [ IntTerm.normalize a aggressive; IntTerm.normalize b aggressive ]
    | Eq (a::b::args) ->
      if aggressive then
	And [Le (IntTerm.normalize a aggressive, IntTerm.normalize b aggressive) ; 
             Le (IntTerm.normalize b aggressive, IntTerm.normalize a aggressive) ;
	     normalize (Eq (b::args)) aggressive ]
      else
        Eq (List.map (fun t -> IntTerm.normalize t aggressive) (a::b::args))
    | Eq a -> raise (Invalid_argument "Unary equality encountered.")
    | Le (a, b)
    | Ge (b, a) ->
      Le (IntTerm.normalize a aggressive, IntTerm.normalize b aggressive)
    | Lt (a, b) 
    | Gt (b, a) ->
      Le (IntTerm.normalize a aggressive, IntTerm.normalize (IntTerm.Sub (b, IntTerm.Const unit_big_int)) aggressive)

  let rec getFreeVars e =
    match e with
    | True
    | False -> 
      VarSet.empty
    | BId v -> 
      VarSet.singleton v
    | Not arg -> 
      getFreeVars arg
    | And args
    | Or args ->
      List.fold_left (fun acc s -> VarSet.union acc s) VarSet.empty (List.map getFreeVars args)
    | Forall (vars, b)
    | Exists (vars, b) ->
      let boundIDs = List.fold_left (fun acc sv -> VarSet.add (fst sv) acc) VarSet.empty vars in
      let bodyFreeVars = getFreeVars b in
      VarSet.fold (fun i acc -> VarSet.remove i acc) boundIDs bodyFreeVars
    | Eq args ->
      List.fold_left (fun acc s -> VarSet.union acc s) VarSet.empty (List.map IntTerm.getFreeVars args)
    | Lt (a,b) | Le (a,b) | Gt (a,b) | Ge (a,b) ->
      VarSet.union (IntTerm.getFreeVars a) (IntTerm.getFreeVars b)

  let toDNF c =
    let rec toDNF' c =
      (* bottom up, so arguments are assumed to be in DNF already *)
      match c with
      | Or args -> Or (List.map toDNF' args)
      | And andArgs -> 
	let dnf = distributeOr (List.map toDNF' andArgs) in
	if List.length dnf = 1 then
	  And (List.hd dnf)
	else
	  Or (List.map (fun d -> And d) dnf)
      | _ -> c
    and distributeOr conjuncts =
      let rec distributeOr' seen todo =
	match todo with
	| (Or orArgs)::rest ->
	  let distributed = List.map (fun oArg -> oArg::seen) orArgs in
          Utils.concatMap (fun seenWithDisjunct -> distributeOr' seenWithDisjunct rest) distributed
	| a::rest -> distributeOr' (a::seen) rest
	| [] -> [seen]
      in distributeOr' [] conjuncts
    in 
    (* normalize, then dnfify, then normalize for Or(Or(...), ...) stuff. *)
    normalize (toDNF' (normalize c false)) false
end


