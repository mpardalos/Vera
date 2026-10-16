open Format
module Zarith_Z = Z
open Vera
open Concrete

let nid = Zarith_Z.pp_print
let sid = Zarith_Z.pp_print

let sort fmt (s : Coq_Sort.t) =
  fprintf fmt "bitvec %a" Zarith_Z.pp_print s

let operation s fmt (op : operation) =
  let unary name e = fprintf fmt "%s %a %a" name sid s nid e in
  let binary name l r = fprintf fmt "%s %a %a %a" name sid s nid l nid r in
  match op with
  | UnsignedExtend (w, e) -> fprintf fmt "uext %a %a %a" sid s nid e Zarith_Z.pp_print w
  | SignedExtend (w, e) -> fprintf fmt "sext %a %a %a" sid s nid e Zarith_Z.pp_print w
  | Slice (hi, lo, e) ->
      fprintf fmt "slice %a %a %a %a" sid s nid e Zarith_Z.pp_print hi Zarith_Z.pp_print lo
  | Not e -> unary "not" e
  | Inc e -> unary "inc" e
  | Dec e -> unary "dec" e
  | RedAnd e -> unary "redand" e
  | RedOr e -> unary "redor" e
  | RedXor e -> unary "redxor" e
  | Iff (l, r) -> binary "iff" l r
  | Implies (l, r) -> binary "implies" l r
  | Eq (l, r) -> binary "eq" l r
  | NEq (l, r) -> binary "neq" l r
  | SignedGt (l, r) -> binary "sgt" l r
  | UnsignedGt (l, r) -> binary "ugt" l r
  | SignedGtE (l, r) -> binary "sgte" l r
  | UnsignedGtE (l, r) -> binary "ugte" l r
  | SignedLt (l, r) -> binary "slt" l r
  | UnsignedLt (l, r) -> binary "ult" l r
  | SignedLtE (l, r) -> binary "slte" l r
  | UnsignedLtE (l, r) -> binary "ulte" l r
  | And (l, r) -> binary "and" l r
  | NAnd (l, r) -> binary "nand" l r
  | Or (l, r) -> binary "or" l r
  | NOr (l, r) -> binary "nor" l r
  | XOr (l, r) -> binary "xor" l r
  | XNor (l, r) -> binary "xnor" l r
  | Rol (l, r) -> binary "rol" l r
  | Sll (l, r) -> binary "sll" l r
  | Sra (l, r) -> binary "sra" l r
  | Srl (l, r) -> binary "srl" l r
  | Add (l, r) -> binary "add" l r
  | Mul (l, r) -> binary "mul" l r
  | SignedDiv (l, r) -> binary "sdiv" l r
  | UnsignedDiv (l, r) -> binary "udiv" l r
  | SignedMod (l, r) -> binary "smod" l r
  | SignedRem (l, r) -> binary "srem" l r
  | UnsignedRem (l, r) -> binary "urem" l r
  | Sub (l, r) -> binary "sub" l r
  | SignedAddOverflow (l, r) -> binary "saddo" l r
  | UnsignedAddOverflow (l, r) -> binary "uaddo" l r
  | SignedDivOverflow (l, r) -> binary "sdivo" l r
  | SignedMulOverflow (l, r) -> binary "smulo" l r
  | UnsignedMulOverflow (l, r) -> binary "umulo" l r
  | SignedSubOverflow (l, r) -> binary "ssubo" l r
  | UnsignedSubOverflow (l, r) -> binary "usubo" l r
  | Concat (l, r) -> binary "concat" l r
  | ITE (cond, ifT, ifF) -> fprintf fmt "ite %a %a %a %a" sid s nid cond nid ifT nid ifF

let node fmt (n : node) =
  match n with
  | SortDecl (s, t) -> fprintf fmt "%a sort %a" sid s sort t
  | Operation (i, s, op) -> fprintf fmt "%a %a" nid i (operation s) op
  | StateInit (i, s, state, init) ->
      fprintf fmt "%a init %a %a %a" nid i sid s nid state nid init
  | StateNext (i, s, state, next) ->
      fprintf fmt "%a next %a %a %a" nid i sid s nid state nid next
  | Bad (i, p) -> fprintf fmt "%a bad %a" nid i nid p
  | Constraint (i, p) -> fprintf fmt "%a constraint %a" nid i nid p
  | Fair (i, p) -> fprintf fmt "%a fair %a" nid i nid p
  | Output (i, p) -> fprintf fmt "%a output %a" nid i nid p
  | Justice (i, n) -> fprintf fmt "%a justice %a" nid i Zarith_Z.pp_print n

let btor fmt nodes =
  List.iter (fun n -> fprintf fmt "%a\n" node n) nodes
