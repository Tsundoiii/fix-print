Require Import String.
Require Import List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNativeString.

Inductive leaf : Type :=
| ENDMARKER : leaf
| NAME : string -> leaf
| NUMBER : string -> leaf
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

Fixpoint concat_strings (l : list string) : string :=
match l with
| [] => "" 
| x :: xs => x ++ concat_strings xs
end.

Definition to_string (t : tree) : string :=
  match t with
  | LEAF (NAME n) => n
  | LEAF (NUMBER n) => n
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
  | _ => ""
  end.

Definition fix_print (l : list tree) : list tree :=
  match l with
  | LEAF (NAME "print") :: n => LEAF (NAME "print") :: LEAF LPAR ::
    (match n with
    | LEAF RIGHTSHIFT :: LEAF (NAME f) :: LEAF COMMA :: n' => 
      match rev n' with
      | LEAF COMMA :: n'' => rev n'' ++ [LEAF COMMA ; LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ") ; LEAF COMMA; LEAF (NAME "file") ; LEAF EQUAL ; LEAF (NAME f)]
      | _ => n' ++ [LEAF COMMA; LEAF (NAME "file") ; LEAF EQUAL ; LEAF (NAME f)]
      end
    | _ => match rev n with
      | LEAF COMMA :: n' => rev n' ++ [LEAF COMMA ; LEAF (NAME "end") ; LEAF EQUAL ; LEAF (STRING " ")]
      | _ => n
      end
    end) ++ [LEAF RPAR]
  | _ => l
  end.

Definition node_to_list (n : tree) : list tree :=
match n with
| NODE l => l
| _ => []
end.

Definition transpile (l : list tree) : string := concat_strings (map to_string (fix_print l)).

Definition test_prefix_preservation := transpile [LEAF (NAME "print") ; LEAF (NUMBER "1") ; LEAF COMMA ; LEAF (NUMBER "1") ; LEAF PLUS ; LEAF (NUMBER "1") ; LEAF COMMA ; LEAF (NUMBER "1") ; LEAF PLUS ; LEAF (NUMBER "1") ; LEAF PLUS ; LEAF (NUMBER "1")].

Extraction "test_prefix_preservation.ml" test_prefix_preservation.

