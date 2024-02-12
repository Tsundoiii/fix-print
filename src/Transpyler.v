Require Import String.
Require Import List.
Import ListNotations.
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

Fixpoint to_string (t : tree) : string :=
match t with
| LEAF (NAME n) => n
| LEAF (STRING s) => s
| LEAF LPAR => "("
| LEAF RPAR => ")"
| LEAF COLON => ":"
| LEAF COMMA => ","
(**| NODE n => to_string (hd (LEAF (STRING "")) n) ++ to_string (NODE (tl n))**)
| _ => ""
end.

Eval simpl in to_string (LEAF (NAME "s")).

Definition test := NODE [LEAF (NAME "print") ; LEAF RIGHTSHIFT ; LEAF (NAME "test") ; LEAF COMMA ; LEAF (STRING "idk") ; LEAF (STRING "i") ; LEAF COMMA].
Eval simpl in map to_string (node_to_list test).


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

Eval simpl in node_to_list (test).
Eval simpl in fix_print (test).


Lemma fix_print_end_correctness : forall n , In [LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ")] node_to_list (fix_print (NODE [LEAF (NAME "print") ; n; LEAF COMMA])).
Proof.



(**Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction tree.**)

