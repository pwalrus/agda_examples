

module d7.gates where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (_++_; toList; fromList; padLeft ; unlines)
open import Data.String.Properties using (_==_)
open import util.list_stuff using (words ; lines ; parse_nat)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.List.Base using (map)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat ; _+_ ; _-_ ; _*_ ; mod-helper ; div-helper ; suc)
open import Data.Nat.Show using (show ; showInBase ; readMaybe)
open import Data.Nat.Base using (_^_)
open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe.Base as Maybe using (Maybe ; nothing ; just)
open import Agda.Builtin.Equality using (refl ; _≡_)

data TermUnion : Set where
  litu : Nat -> TermUnion
  wireu : String -> TermUnion

data GateType : Set where
  AND : GateType
  OR : GateType
  LSHIFT : GateType
  RSHIFT : GateType

data Inst : Set where
  assignop : TermUnion → String → Inst
  binop : TermUnion → GateType → TermUnion → String → Inst
  notop : TermUnion → String → Inst
  nope : Inst

data Assignment : Set where
  assm : String → Nat → Assignment

mod_sixteen : Nat → Nat
mod_sixteen x = mod-helper 0 65535 x 65535

parse_bin : Nat → List Char → Maybe Nat
parse_bin start ('0' ∷ []) = just (2 * start)
parse_bin start ('1' ∷ []) = just (2 * start + 1)
parse_bin start ('0' ∷ xs) = (parse_bin (2 * start) xs)
parse_bin start ('1' ∷ xs) = (parse_bin (2 * start + 1) xs)
parse_bin _ _ = nothing

bit_lshift : Maybe Nat → Maybe Nat → Maybe Nat
bit_lshift (just val) (just d) = just (mod_sixteen (val * (2 ^ d)))
bit_lshift _ _ = nothing

bit_rshift : Maybe Nat → Maybe Nat → Maybe Nat
bit_rshift (just val) (just d) = just (div-helper 0 (2 ^ d - 1) val (2 ^ d - 1))
bit_rshift _ _ = nothing

bit_and : Maybe Nat → Maybe Nat → Maybe Nat
bit_and (just l) (just r) = (parse_bin 0 (comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
  where
    comb : List Char → List Char → List Char
    comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (comb ls rs)
    comb ('0' ∷ ls) ('1' ∷ rs) = '0' ∷ (comb ls rs)
    comb ('1' ∷ ls) ('0' ∷ rs) = '0' ∷ (comb ls rs)
    comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (comb ls rs)
    comb _ _ = []
bit_and _ _ = nothing

bit_or : Maybe Nat → Maybe Nat →  Maybe Nat
bit_or (just l) (just r) = (parse_bin 0 (comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
  where
    comb : List Char → List Char → List Char
    comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (comb ls rs)
    comb ('0' ∷ ls) ('1' ∷ rs) = '1' ∷ (comb ls rs)
    comb ('1' ∷ ls) ('0' ∷ rs) = '1' ∷ (comb ls rs)
    comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (comb ls rs)
    comb _ _ = []
bit_or _ _ = nothing

bit_not : Maybe Nat → Maybe Nat
bit_not nothing = nothing
bit_not (just l) = (parse_bin 0 (comb
  (toList (padLeft '0' 16 (showInBase 2 l)))))
  where
    comb : List Char → List Char
    comb ('0' ∷ ls) = '1' ∷ (comb ls)
    comb ('1' ∷ ls) = '0' ∷ (comb ls)
    comb _ = []

out_wire : Inst → String
out_wire (assignop _ w)  = w
out_wire (binop _ _ _ w) = w
out_wire (notop _ w) = w
out_wire _ = "none"

show_assm : Assignment → String
show_assm (assm wire val) = wire ++ ": " ++ (show val)

read_val : TermUnion → List Assignment → Maybe Nat
read_val (litu lit) _ = just lit
read_val wire [] = nothing
read_val (wireu wire) ((assm x val) ∷ xs) = if wire == x then (just val) else read_val (wireu wire) xs

first_match : String -> List Inst -> Maybe Inst
first_match wire [] = nothing
first_match wire (x ∷ xs) = if wire == (out_wire x)
  then just x
  else first_match wire xs

data RecResult : Set where
  ok : Nat → RecResult
  missing : String → RecResult
  failed : RecResult
  hit_limit : RecResult

from_maybe : Maybe Nat → RecResult
from_maybe (just p) = ok p
from_maybe _ = failed

func_from_op : GateType → (Maybe Nat → Maybe Nat → Maybe Nat)
func_from_op AND = bit_and
func_from_op OR = bit_or
func_from_op LSHIFT = bit_lshift
func_from_op RSHIFT = bit_rshift

read_val_rec : Nat → TermUnion → List Inst → RecResult
read_val_rec 0 _ _ = hit_limit
read_val_rec _ (litu lit) _ = ok lit
read_val_rec (suc l) (wireu wire) insts with (first_match wire insts)
read_val_rec (suc l) (wireu wire) insts | nothing = missing wire
read_val_rec (suc l) (wireu wire) insts | just (assignop val _) = (read_val_rec l val insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) with (read_val_rec l wa insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) with (read_val_rec l wb insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | (ok q) = from_maybe ((func_from_op op) (just p) (just q))
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | k = k
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | k = k

read_val_rec (suc l) (wireu wire) insts | just (notop wa _) with (read_val_rec l wa insts)
read_val_rec (suc l) (wireu wire) insts | just (notop wa _) | (ok r) = from_maybe (bit_not (just r))
read_val_rec (suc l) (wireu wire) insts | just (notop wa _) | k = k
read_val_rec (suc l) (wireu wire) insts | just _ = failed

write_val : String → Nat → List Assignment → List Assignment
write_val wire val [] = (assm wire val) ∷ []
write_val wire val ((assm w old) ∷ xs) = if wire == w
  then (assm wire val) ∷ xs
  else (assm w old) ∷ (write_val wire val xs)

calc_inst : Inst → List Assignment → Maybe Nat
calc_inst (assignop val _) db = read_val val db
calc_inst (binop wa AND wb _) db = bit_and (read_val wa db) (read_val wb db)
calc_inst (binop wa OR wb _) db = bit_or (read_val wa db) (read_val wb db)
calc_inst (binop wa LSHIFT wb _) db = bit_lshift (read_val wa db) (read_val wb db)
calc_inst (binop wa RSHIFT wb _) db = bit_rshift (read_val wa db) (read_val wb db)
calc_inst (notop wa _) db = bit_not (read_val wa db)
calc_inst _ _ = nothing

apply_inst : Inst → List Assignment → List Assignment
apply_inst inst db with (calc_inst inst db)
...                   | just x = write_val (out_wire inst) x db
...                   | nothing = db

apply_all_inst : List Inst → List Assignment → List Assignment
apply_all_inst [] db = db
apply_all_inst (x ∷ xs) db = apply_all_inst xs (apply_inst x db)

parse_term : String → TermUnion
parse_term x with (readMaybe 10 x)
...             | just y = (litu y)
...             | nothing = (wireu x)

parse_line_parts : List String → Inst
parse_line_parts (lit ∷ "->" ∷ wire ∷ _) = assignop (parse_term lit) wire
parse_line_parts (wa ∷ "AND" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse_term wa) AND (parse_term wb) wire
parse_line_parts (wa ∷ "OR" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse_term wa) OR (parse_term wb) wire
parse_line_parts (wa ∷ "LSHIFT" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse_term wa) LSHIFT (parse_term wb) wire
parse_line_parts (wa ∷ "RSHIFT" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse_term wa) RSHIFT (parse_term wb) wire
parse_line_parts ("NOT" ∷ w ∷ "->" ∷ wire ∷ _) = notop (parse_term w) wire
parse_line_parts _ = nope

parse_line : String → Inst
parse_line x = parse_line_parts (words x)

test_parse_lshift : parse_line "w LSHIFT 3 -> f " ≡ binop (wireu "w") LSHIFT (litu 3) "f"
test_parse_lshift = refl

test_lshift : bit_lshift (just 2) (just 1) ≡ just 4
test_lshift = refl

test_bitor : bit_or (just 2) (just 1) ≡ just 3
test_bitor = refl

test_apply_inst : apply_inst (assignop (litu 123) "a") ((assm "b" 23) ∷ (assm "a" 45) ∷ (assm "q" 3) ∷ []) ≡ ((assm "b" 23) ∷ (assm "a" 123) ∷ (assm "q" 3) ∷ [])
test_apply_inst = refl

test_read_val_rec : read_val_rec 100 (wireu "a") ((binop (wireu "b") OR (wireu "b") "a") ∷ (assignop (litu 123) "b") ∷ []) ≡ ok 123
test_read_val_rec = refl

test_one_and : apply_inst (parse_line "1 AND 1 -> a") [] ≡ ((assm "a" 1) ∷ [])
test_one_and = refl

run_sim : String → String
run_sim x with read_val_rec 1000 (wireu "a") (map parse_line (lines x))
... | (missing wire) = "wire was missing: " ++ wire ++ "\n"
... | ok p = "a: " ++ (show p) ++ "\n"
... | hit_limit = "hit limit"
... | _ = "failed"
