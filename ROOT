chapter AFP

(* Session name, add to AFP group, list base session: *)
session "Example-Submission" (AFP) = HOL +

(* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 600]

(* To suppress document generation of some theories: *)
(*
  theories [document = false]
    This_Theory
    That_Theory
*)

(* The top-level theories of the submission: *)
  theories
    Submission
    
(* Dependencies on non-Isabelle files: *)
  document_files
    "root.bib"
    "root.tex"
