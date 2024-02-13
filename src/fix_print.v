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

Fixpoint concat_strings (lst : list string) : string :=
match lst with
| [] => "" 
| x :: xs => x ++ concat_strings xs
end.

Fixpoint to_string (t : tree) : string :=
match t with
| LEAF (NAME n) => n
(**| LEAF NUMBER => leaf**)
| LEAF (STRING s) => "'" ++ s ++ "'"
| LEAF LPAR => "("
| LEAF RPAR => ")"
| LEAF COLON => ":"
| LEAF COMMA => ","
| LEAF SEMI => ";"
| LEAF PLUS => "+"
| LEAF MINUS => "-"
| LEAF STAR => "*"
| LEAF SLASH => "/"
| LEAF AMPER => "&"
| LEAF LESS => "<"
| LEAF GREATER => ">"
| LEAF EQUAL => "="
| LEAF DOT => "."
| LEAF PERCENT => "%"
| LEAF BACKQUOTE => "`"
| LEAF LBRACE => "{"
| LEAF RBRACE => "}"
| LEAF EQEUQAL => "=="
| LEAF NOTEQUAL => "!="
| LEAF LESSEQUAL => "<="
| LEAF GREATEREQUAL => ">="
| LEAF TILDE => "~"
| LEAF CIRCUMFLEX => "^"
| LEAF LEFTSHIFT => "<<"
| LEAF RIGHTSHIFT => ">>"
| LEAF DOUBLESTAR => "**"
| LEAF PLUSEQUAL => "+="
| LEAF MINEQUAL => "-="
| LEAF STAREQUAL => "*="
| LEAF SLASHEQUAL => "/="
| LEAF PERCENTEQUAL => "%="
| LEAF AMPEREQUAL => "&="
| LEAF VBAREQUAL => "|="
| LEAF CIRCUMFLEXEQUAL => "^="
| LEAF LEFTSHIFTEQUAL => "<<="
| LEAF RIGHTSHIFTEQUAL => ">>="
| LEAF DOUBLESTAREQUAL => "**="
| LEAF DOUBLESLASH => "//"
| LEAF DOUBLESLASHEQUAL => "//="
| LEAF AT => "@"
| LEAF ATEQUAL => "@="
| LEAF COLONEQUAL => ":="
(**| NODE [] => ""
| NODE (x :: xs) => to_string (x) ++ to_string (NODE xs)**)
| _ => ""
end.

Definition fix_print (t : tree) : tree :=
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

Definition test := NODE [LEAF (NAME "print") ; LEAF RIGHTSHIFT ; LEAF (NAME "test") ; LEAF COMMA ; LEAF (STRING "idk") ; LEAF COMMA].
Eval simpl in fix_print test.

Eval simpl in concat_strings (map to_string (node_to_list test)).

(**Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Recursive Extraction tree.**)

