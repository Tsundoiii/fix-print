
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

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

(** val concat_strings : string list -> string **)

let rec concat_strings = function
| [] -> ""
| x :: xs -> (^) x (concat_strings xs)

(** val to_string : tree -> string **)

let to_string = function
| LEAF l ->
  (match l with
   | NAME n -> n
   | NUMBER n -> n
   | STRING s -> (^) "'" ((^) s "'")
   | LPAR -> "("
   | RPAR -> ")"
   | COLON -> ":"
   | COMMA -> ","
   | SEMI -> ";"
   | PLUS -> "+"
   | MINUS -> "-"
   | STAR -> "*"
   | SLASH -> "/"
   | AMPER -> "&"
   | LESS -> "<"
   | GREATER -> ">"
   | EQUAL -> "="
   | DOT -> "."
   | PERCENT -> "%"
   | BACKQUOTE -> "`"
   | LBRACE -> "{"
   | RBRACE -> "}"
   | EQEUQAL -> "=="
   | NOTEQUAL -> "!="
   | LESSEQUAL -> "<="
   | GREATEREQUAL -> ">="
   | TILDE -> "~"
   | CIRCUMFLEX -> "^"
   | LEFTSHIFT -> "<<"
   | RIGHTSHIFT -> ">>"
   | DOUBLESTAR -> "**"
   | PLUSEQUAL -> "+="
   | MINEQUAL -> "-="
   | STAREQUAL -> "*="
   | SLASHEQUAL -> "/="
   | PERCENTEQUAL -> "%="
   | AMPEREQUAL -> "&="
   | VBAREQUAL -> "|="
   | CIRCUMFLEXEQUAL -> "^="
   | LEFTSHIFTEQUAL -> "<<="
   | RIGHTSHIFTEQUAL -> ">>="
   | DOUBLESTAREQUAL -> "**="
   | DOUBLESLASH -> "//"
   | DOUBLESLASHEQUAL -> "//="
   | AT -> "@"
   | ATEQUAL -> "@="
   | COLONEQUAL -> ":="
   | _ -> "")
| NODE _ -> ""

(** val fix_print : tree list -> tree list **)

let fix_print l = match l with
| [] -> l
| t :: n ->
  (match t with
   | LEAF l0 ->
     (match l0 with
      | NAME s ->
        ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

           (fun _ -> l)
           (fun a s0 ->
           (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
             (fun b b0 b1 b2 b3 b4 b5 b6 ->
             if b
             then l
             else if b0
                  then l
                  else if b1
                       then l
                       else if b2
                            then l
                            else if b3
                                 then if b4
                                      then if b5
                                           then if b6
                                                then l
                                                else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                        (fun _ ->
                                                        l)
                                                        (fun a0 s1 ->
                                                        (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                          (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                                                          if b7
                                                          then l
                                                          else if b8
                                                               then if b9
                                                                    then l
                                                                    else 
                                                                    if b10
                                                                    then l
                                                                    else 
                                                                    if b11
                                                                    then 
                                                                    if b12
                                                                    then 
                                                                    if b13
                                                                    then 
                                                                    if b14
                                                                    then l
                                                                    else 
                                                                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    l)
                                                                    (fun a1 s2 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b15 b16 b17 b18 b19 b20 b21 b22 ->
                                                                    if b15
                                                                    then 
                                                                    if b16
                                                                    then l
                                                                    else 
                                                                    if b17
                                                                    then l
                                                                    else 
                                                                    if b18
                                                                    then 
                                                                    if b19
                                                                    then l
                                                                    else 
                                                                    if b20
                                                                    then 
                                                                    if b21
                                                                    then 
                                                                    if b22
                                                                    then l
                                                                    else 
                                                                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    l)
                                                                    (fun a2 s3 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b23 b24 b25 b26 b27 b28 b29 b30 ->
                                                                    if b23
                                                                    then l
                                                                    else 
                                                                    if b24
                                                                    then 
                                                                    if b25
                                                                    then 
                                                                    if b26
                                                                    then 
                                                                    if b27
                                                                    then l
                                                                    else 
                                                                    if b28
                                                                    then 
                                                                    if b29
                                                                    then 
                                                                    if b30
                                                                    then l
                                                                    else 
                                                                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    l)
                                                                    (fun a3 s4 ->
                                                                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                                                                    (fun b31 b32 b33 b34 b35 b36 b37 b38 ->
                                                                    if b31
                                                                    then l
                                                                    else 
                                                                    if b32
                                                                    then l
                                                                    else 
                                                                    if b33
                                                                    then 
                                                                    if b34
                                                                    then l
                                                                    else 
                                                                    if b35
                                                                    then 
                                                                    if b36
                                                                    then 
                                                                    if b37
                                                                    then 
                                                                    if b38
                                                                    then l
                                                                    else 
                                                                    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                                    (fun _ ->
                                                                    (LEAF
                                                                    (NAME
                                                                    "print")) :: ((LEAF
                                                                    LPAR) :: 
                                                                    (app
                                                                    (match n with
                                                                    | [] ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t0 :: n' ->
                                                                    (match t0 with
                                                                    | LEAF l1 ->
                                                                    (match l1 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))
                                                                    | t0 :: l1 ->
                                                                    (match t0 with
                                                                    | LEAF l2 ->
                                                                    (match l2 with
                                                                    | RIGHTSHIFT ->
                                                                    (match l1 with
                                                                    | [] ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t1 :: n' ->
                                                                    (match t1 with
                                                                    | LEAF l3 ->
                                                                    (match l3 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))
                                                                    | t1 :: l3 ->
                                                                    (match t1 with
                                                                    | LEAF l4 ->
                                                                    (match l4 with
                                                                    | NAME f ->
                                                                    (match l3 with
                                                                    | [] ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t2 :: n' ->
                                                                    (match t2 with
                                                                    | LEAF l5 ->
                                                                    (match l5 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))
                                                                    | t2 :: n' ->
                                                                    (match t2 with
                                                                    | LEAF l5 ->
                                                                    (match l5 with
                                                                    | COMMA ->
                                                                    (match 
                                                                    rev n' with
                                                                    | [] ->
                                                                    app n'
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "file")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (NAME
                                                                    f)) :: []))))
                                                                    | t3 :: n'' ->
                                                                    (match t3 with
                                                                    | LEAF l6 ->
                                                                    (match l6 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n'')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "file")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (NAME
                                                                    f)) :: []))))))))
                                                                    | _ ->
                                                                    app n'
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "file")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (NAME
                                                                    f)) :: [])))))
                                                                    | NODE _ ->
                                                                    app n'
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "file")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (NAME
                                                                    f)) :: []))))))
                                                                    | _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t3 :: n'0 ->
                                                                    (match t3 with
                                                                    | LEAF l6 ->
                                                                    (match l6 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n'0)
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n)))
                                                                    | NODE _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t3 :: n'0 ->
                                                                    (match t3 with
                                                                    | LEAF l5 ->
                                                                    (match l5 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n'0)
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))))
                                                                    | _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t2 :: n' ->
                                                                    (match t2 with
                                                                    | LEAF l5 ->
                                                                    (match l5 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n)))
                                                                    | NODE _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t2 :: n' ->
                                                                    (match t2 with
                                                                    | LEAF l4 ->
                                                                    (match l4 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))))
                                                                    | _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t1 :: n' ->
                                                                    (match t1 with
                                                                    | LEAF l3 ->
                                                                    (match l3 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n)))
                                                                    | NODE _ ->
                                                                    (match 
                                                                    rev n with
                                                                    | [] -> n
                                                                    | t1 :: n' ->
                                                                    (match t1 with
                                                                    | LEAF l2 ->
                                                                    (match l2 with
                                                                    | COMMA ->
                                                                    app
                                                                    (rev n')
                                                                    ((LEAF
                                                                    COMMA) :: ((LEAF
                                                                    (NAME
                                                                    "end")) :: ((LEAF
                                                                    EQUAL) :: ((LEAF
                                                                    (STRING
                                                                    " ")) :: []))))
                                                                    | _ -> n)
                                                                    | NODE _ ->
                                                                    n))))
                                                                    ((LEAF
                                                                    RPAR) :: []))))
                                                                    (fun _ _ ->
                                                                    l)
                                                                    s4)
                                                                    else l
                                                                    else l
                                                                    else l
                                                                    else l)
                                                                    a3)
                                                                    s3)
                                                                    else l
                                                                    else l
                                                                    else l
                                                                    else l
                                                                    else l)
                                                                    a2)
                                                                    s2)
                                                                    else l
                                                                    else l
                                                                    else l
                                                                    else l)
                                                                    a1)
                                                                    s1)
                                                                    else l
                                                                    else l
                                                                    else l
                                                               else l)
                                                          a0)
                                                        s0)
                                           else l
                                      else l
                                 else l)
             a)
           s)
      | _ -> l)
   | NODE _ -> l)

(** val transpile : tree list -> string **)

let transpile l =
  concat_strings (map to_string (fix_print l))

(** val test : string **)

let test =
  transpile ((LEAF (NAME "print")) :: ((LEAF (NUMBER "1")) :: ((LEAF
    COMMA) :: ((LEAF (NUMBER "1")) :: ((LEAF PLUS) :: ((LEAF (NUMBER
    "1")) :: ((LEAF COMMA) :: ((LEAF (NUMBER "1")) :: ((LEAF PLUS) :: ((LEAF
    (NUMBER "1")) :: ((LEAF PLUS) :: ((LEAF (NUMBER "1")) :: []))))))))))))

let () = print_string test