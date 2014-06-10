(*
  Utility functions.

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

module VarSet = Set.Make(String)

let rec tryFind p l =
  match l with
  | x::xs -> if p x then Some x else tryFind p xs
  | [] -> None

let concatMap f l =
  List.fold_right (fun v acc -> (f v) @ acc) l []

(* Removes the first occurence of an element from a list, using comparison comp *)
let rec remove comp l e =
  match l with
    | x::xs -> if comp x e then
                 xs
               else
                 x::(remove comp xs e)
    | [] -> []

(* Removes the first occurence of each element from a list from another list, using comparison comp *)
let rec removeAll comp l l' =
  match l' with
    | e::rest -> removeAll comp (remove comp l e) rest
    | [] -> l

(* Checks whether e is in l *)
let rec contains comp l e =
  match l with
    | x::xs -> (comp x e) || contains comp xs e
    | [] -> false

let rec take n l =
  if n <= 0 then 
    []
  else
    match l with
      | x::xs -> x::(take (n-1) xs)
      | []    -> raise (Failure (Printf.sprintf "Trying to take %i elements from empty list" n))

let rec drop n l =
  if n <= 0 then 
    l
  else
    match l with
      | x::xs -> drop (n-1) xs
      | []    -> raise (Failure (Printf.sprintf "Trying to drop %i elements from empty list" n))


let rec deldups l =
  match l with
  | [] -> []
  | x::xs -> x::(deldups (List.filter (fun y -> x <> y) xs))


let varListToSet l =
  List.fold_left (fun acc e -> VarSet.add e acc) VarSet.empty l

(* Turns a list [x1; x2; ...; xn] into a list of lists [ [x1; ... ;x_{i_1}-1]; [x_{i_1}; ...; x_{i_2}-1]; ...]
   such that p x_ij holds for all j, and for no other x_j. *)
let splitListBefore p l =
  let rec splitListBefore' p acc l =
    match l with
    | [] -> [acc]
    | x::xs -> 
      if p x then
	acc::(splitListBefore' p [x] xs)
      else 
	splitListBefore' p (acc @ [x]) xs
  in
  let res = splitListBefore' p [] l in
  if List.length res > 0 && List.hd res = [] then
    List.tl res
  else
    res

(* Waiting for OCaml 4... *)

let mapi f l =
  let rec mapi' f i l =
    match l with
    | x::xs -> (f i x)::(mapi' f (i+1) xs)
    | [] -> []
  in mapi' f 0 l

let iteri f l =
  let rec iteri' f i l =
    match l with
    | x::xs -> (f i x) ; (iteri' f (i+1) xs)
    | [] -> ()
  in iteri' f 0 l
    
