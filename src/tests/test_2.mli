
val app : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type leaf =
| ENDMARKER
| NAME of string
| NUMBER of string
| STRING of string
| NEWLINE
| INDENT
| DEDENT
| LPAR
| RPAR
| LSQB
| RSQB
| COLON
| COMMA
| SEMI
| PLUS
| MINUS
| STAR
| SLASH
| VBAR
| AMPER
| LESS
| GREATER
| EQUAL
| DOT
| PERCENT
| BACKQUOTE
| LBRACE
| RBRACE
| EQEUQAL
| NOTEQUAL
| LESSEQUAL
| GREATEREQUAL
| TILDE
| CIRCUMFLEX
| LEFTSHIFT
| RIGHTSHIFT
| DOUBLESTAR
| PLUSEQUAL
| MINEQUAL
| STAREQUAL
| SLASHEQUAL
| PERCENTEQUAL
| AMPEREQUAL
| VBAREQUAL
| CIRCUMFLEXEQUAL
| LEFTSHIFTEQUAL
| RIGHTSHIFTEQUAL
| DOUBLESTAREQUAL
| DOUBLESLASH
| DOUBLESLASHEQUAL
| AT
| ATEQUAL
| OP
| COMMENT of string
| NL
| RARROW
| AWAIT
| ASYNC
| ERRORTOKEN
| COLONEQUAL

type tree =
| LEAF of leaf
| NODE of tree list

val concat_strings : string list -> string

val to_string : tree -> string

val fix_print : tree list -> tree list

val transpile : tree list -> string

val test : string
