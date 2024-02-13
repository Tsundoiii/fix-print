Require Import String.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Extraction.

Inductive leaf : Type :=
| ENDMARKER : leaf
| NAME : string -> leaf
| NUMBER : leaf
| STRING : string -> leaf
| NEWLINE : leaf
| INDENT : leaf
| DEDENT : leaf
| LPAR : leaf
| RPAR : leaf
| LSQB : leaf
| RSQB : leaf
| COLON : leaf
| COMMA : leaf
| SEMI : leaf
| PLUS : leaf
| MINUS : leaf
| STAR : leaf
| SLASH : leaf
| VBAR : leaf
| AMPER : leaf
| LESS : leaf
| GREATER : leaf
| EQUAL : leaf
| DOT : leaf
| PERCENT : leaf
| BACKQUOTE : leaf
| LBRACE : leaf
| RBRACE : leaf
| EQEUQAL : leaf
| NOTEQUAL : leaf
| LESSEQUAL : leaf
| GREATEREQUAL : leaf
| TILDE : leaf
| CIRCUMFLEX : leaf
| LEFTSHIFT : leaf
| RIGHTSHIFT : leaf
| DOUBLESTAR : leaf
| PLUSEQUAL : leaf
| MINEQUAL : leaf
| STAREQUAL : leaf
| SLASHEQUAL : leaf
| PERCENTEQUAL : leaf
| AMPEREQUAL : leaf
| VBAREQUAL : leaf
| CIRCUMFLEXEQUAL : leaf
| LEFTSHIFTEQUAL : leaf
| RIGHTSHIFTEQUAL : leaf
| DOUBLESTAREQUAL : leaf
| DOUBLESLASH : leaf
| DOUBLESLASHEQUAL : leaf
| AT : leaf
| ATEQUAL : leaf
| OP : leaf
| COMMENT : string -> leaf
| NL : leaf
| RARROW : leaf
| AWAIT : leaf
| ASYNC : leaf
| ERRORTOKEN : leaf
| COLONEQUAL : leaf.

Inductive tree : Type :=
| LEAF : leaf -> tree
| NODE : list tree -> tree.

Definition leaf_to_string (l : leaf) : string :=
match l with
| NAME n => n
| STRING s => s
| LPAR => "("
| RPAR => ")"
| COLON => ":"
| COMMA => ","
| _ => ""
end.

Fixpoint concat_strings (lst : list string) : string :=
  match lst with
  | [] => ""  (* Base case: concatenation of an empty list is an empty string *)
  | x :: xs => x ++ concat_strings xs  (* Recursive case: concatenate the head of the list to the concatenation of the tail *)
  end.

Program Fixpoint list_to_string (l :list leaf) {measure (length l)}: string :=
leaf_to_string (hd (STRING "") l) ++ list_to_string (tl l).
Next Obligation.
Search (_<_) in List.
induction l.
simpl.
inversion.

(**Definition to_string (t : tree) : string :=
match t with
| NODE n => list_to_string (n)
| _ => ""
end.

Definition fix_print (t : tree) :=
match t with
| NODE [LEAF (NAME "print") ; n] => NODE [LEAF (NAME "print") ; LEAF LPAR ; n ; LEAF RPAR]
| NODE [LEAF (NAME "print") ; n; LEAF COMMA] => NODE [LEAF (NAME "print") ; LEAF LPAR ; n ; LEAF COMMA; LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ") ; LEAF RPAR]
| NODE [LEAF (NAME "print") ; LEAF RIGHTSHIFT ; LEAF (NAME f) ; LEAF COMMA ; n] => NODE [LEAF (NAME "print") ; LEAF LPAR ; n ; LEAF COMMA; LEAF (NAME "file") ; LEAF EQUAL ; LEAF (NAME f) ; LEAF RPAR]
| NODE [LEAF (NAME "print") ; LEAF RIGHTSHIFT ; LEAF (NAME f) ; LEAF COMMA ; n; LEAF COMMA] => NODE [LEAF (NAME "print") ; LEAF LPAR ; n ; LEAF COMMA; LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ") ; LEAF COMMA; LEAF (NAME "file") ; LEAF EQUAL ; LEAF (NAME f) ; LEAF RPAR]
| _ => t
end.

Definition node_to_list (n : tree) : list tree :=
match n with
| NODE l => l
| _ => [LEAF COMMA]
end.

Definition test := NODE [LEAF (NAME "print") ; LEAF RIGHTSHIFT ; LEAF (NAME "test") ; LEAF COMMA ; LEAF (STRING "idk") ; LEAF (STRING "i") ; LEAF COMMA].

Eval simpl in node_to_list (test).
Eval simpl in fix_print (test).


Lemma fix_print_end_correctness : forall n , In [LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ")] node_to_list (fix_print (NODE [LEAF (NAME "print") ; n; LEAF COMMA])).
Proof.



Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction tree.**)

