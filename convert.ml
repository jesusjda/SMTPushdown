(*
  Parser, validator and translator for SMTLIB-based Pushdown Automata format.

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

type outputFormat =
  | SMTLib
  | IntTRS
  | T2

type runMode = 
  | Validate
  | ConvertTo of outputFormat

let runmode = ref Validate
let filename = ref ""
let enableWarnings = ref false
let warningsAsErrors = ref false
let terminationOnly = ref false

let rec parseFormat s =
  match (String.lowercase s) with
  | "inttrs"
  | "int-trs"
  | "kittel"
  | "koat"    -> IntTRS
  | "t2"      -> T2
  | "smtlib"
  | "smt"     -> SMTLib
  | _         -> print_usage (); exit 1
and speclist =
  [
    ("--validate",    Arg.Unit   (fun () -> runmode := Validate), "");
    ("-validate",     Arg.Unit   (fun () -> runmode := Validate), "   - Validate format of input file");
    ("--convert-to",   Arg.String (fun s -> runmode := ConvertTo (parseFormat s)), "");
    ("-convert-to",   Arg.String (fun s -> runmode := ConvertTo (parseFormat s)), "");
    ("--convertto",   Arg.String (fun s -> runmode := ConvertTo (parseFormat s)), "");
    ("-convertto",    Arg.String (fun s -> runmode := ConvertTo (parseFormat s)), "  - Convert input file to given format (SMTLib/IntTRS/T2)");
    ("--warnings",    Arg.Unit   (fun () -> enableWarnings := true), "");
    ("-warnings",     Arg.Unit   (fun () -> enableWarnings := true), "   - Show warnings.");
    ("--strict",      Arg.Unit   (fun () -> warningsAsErrors := true), "");
    ("-strict",       Arg.Unit   (fun () -> warningsAsErrors := true), "     - Warnings are fatal.");
    ("--termination", Arg.Unit   (fun () -> terminationOnly := true), "");
    ("-termination",  Arg.Unit   (fun () -> terminationOnly := true), "- Allow conversions that are sound for termination, but otherwise unsound.");
    ("--help",        Arg.Unit   (fun () -> print_usage (); exit 1), "");
    ("-help",         Arg.Unit   (fun () -> print_usage (); exit 1), "       - Display this list of options");
  ]
and usage = 
  "usage: " ^ Sys.argv.(0) ^ " [--validate|--convertto <format>] <filename>"
and print_usage () =
  Arg.usage speclist usage

let main () =
  Arg.parse speclist (fun f -> filename := f) usage;
  if !filename = "" then
    (
      Printf.printf "%s\n" (Sys.argv.(0) ^ ": need a filename.");
      print_usage ();
      exit 1
    )
  else
    (
      try
	let p = Parser.parse !filename !enableWarnings !warningsAsErrors in
	match !runmode with
	| Validate ->
	  (* Parser crashes and burns if there's something wrong. *)
          Printf.printf "File %s valid.\n" !filename;
          exit 0;
	| ConvertTo SMTLib ->
          SMTFormat.output p;
          exit 0;
	| ConvertTo IntTRS ->
          IntTRSFormat.output p !terminationOnly;
          exit 0;
	| ConvertTo T2 ->
          T2Format.output p !terminationOnly;
          exit 0;
      with 
      | Parser.ParseException msg -> 
	(
	  Printf.printf "File %s invalid: %s\n" !filename msg;
	  exit 1;
	)
    )
let _ = main ()
