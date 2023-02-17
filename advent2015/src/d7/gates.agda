

module d7.gates where

open import Agda.Builtin.String using (String)
open import Data.String.Base using (_++_; toList; fromList; padLeft ; unlines)
open import Data.String.Properties using (_==_ ; _<?_)
open import util.list_stuff using (words ; lines ; parse_nat)
open import util.lookup using (LookupTree ; build_tree ; has_val ; set_val ; all_values) renaming (read_val to read_tree)
open import Agda.Builtin.List using (List ; _∷_ ; [])
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (map ; length)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat ; _+_ ; _-_ ; _*_  ; _<_ ; mod-helper ; div-helper ; suc)
open import Data.Nat.Show using (show ; showInBase ; readMaybe)
open import Data.Nat.Base using (_^_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (_∧_)
open import Data.Bool.Base using (if_then_else_)
open import Data.Maybe.Base as Maybe using (Maybe ; nothing ; just)
open import Relation.Nullary.Decidable using (isYes)
open import Agda.Builtin.Equality using (refl ; _≡_)

data TermUnion : Set where
  litu : Nat → TermUnion
  wireu : String → TermUnion

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

show_assm : Assignment → String
show_assm (assm wire val) = wire ++ ": " ++ (show val)

mod_sixteen : Nat → Nat
mod_sixteen x = mod-helper 0 65535 x 65535

parse_bin : Nat → List Char → Maybe Nat
parse_bin start ('0' ∷ []) = just (2 * start)
parse_bin start ('1' ∷ []) = just (2 * start + 1)
parse_bin start ('0' ∷ xs) = (parse_bin (2 * start) xs)
parse_bin start ('1' ∷ xs) = (parse_bin (2 * start + 1) xs)
parse_bin _ _ = nothing

bit_lshift : Nat → Nat → Nat
bit_lshift val d = mod_sixteen (val * (2 ^ d))

bit_rshift : Nat → Nat → Nat
bit_rshift val d = div-helper 0 (2 ^ d - 1) val (2 ^ d - 1)

and_comb : List Char → List Char → List Char
and_comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (and_comb ls rs)
and_comb ('0' ∷ ls) ('1' ∷ rs) = '0' ∷ (and_comb ls rs)
and_comb ('1' ∷ ls) ('0' ∷ rs) = '0' ∷ (and_comb ls rs)
and_comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (and_comb ls rs)
and_comb _ _ = []

bit_and : Nat → Nat → Nat
bit_and l r with (parse_bin 0 (and_comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
... | just x = x
... | nothing = 0


or_comb : List Char → List Char → List Char
or_comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (or_comb ls rs)
or_comb ('0' ∷ ls) ('1' ∷ rs) = '1' ∷ (or_comb ls rs)
or_comb ('1' ∷ ls) ('0' ∷ rs) = '1' ∷ (or_comb ls rs)
or_comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (or_comb ls rs)
or_comb _ _ = []

bit_or : Nat → Nat →  Nat
bit_or l r with (parse_bin 0 (or_comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
... | just x = x
... | nothing = 0

not_comb : List Char → List Char
not_comb ('0' ∷ ls) = '1' ∷ (not_comb ls)
not_comb ('1' ∷ ls) = '0' ∷ (not_comb ls)
not_comb _ = []
    
bit_not : Nat → Nat
bit_not l with (parse_bin 0 (not_comb
  (toList (padLeft '0' 16 (showInBase 2 l)))))
... | just x = x
... | nothing = 0

out_wire : Inst → String
out_wire (assignop _ w)  = w
out_wire (binop _ _ _ w) = w
out_wire (notop _ w) = w
out_wire _ = "none"

read_val : TermUnion → List Assignment → Maybe Nat
read_val (litu lit) _ = just lit
read_val wire [] = nothing
read_val (wireu wire) ((assm x val) ∷ xs) = if wire == x then (just val) else read_val (wireu wire) xs

first_match : String → List Inst → Maybe Inst
first_match wire [] = nothing
first_match wire (x ∷ xs) = if wire == (out_wire x)
  then just x
  else first_match wire xs

data RecResult : Set where
  ok : Nat → RecResult
  missing : String → RecResult
  failed : RecResult
  hit_limit : RecResult

--from_maybe : Maybe Nat → RecResult
--from_maybe (just p) = ok p
--from_maybe _ = failed

func_from_op : GateType → (Nat → Nat → Nat)
func_from_op AND = bit_and
func_from_op OR = bit_or
func_from_op LSHIFT = bit_lshift
func_from_op RSHIFT = bit_rshift

str_lt : String → String → Bool
str_lt a b = isYes (a <? b)

mk_tree : List Inst → LookupTree String Inst
mk_tree [] = build_tree _==_ str_lt []
mk_tree x = build_tree _==_ str_lt (map (λ {i → (out_wire i , i) }) x)

-- works on smaller examples but needs too much memory for the full puzzle
read_val_rec : Nat → TermUnion → LookupTree String Inst → RecResult
read_val_rec 0 _ _ = hit_limit
read_val_rec _ (litu lit) _ = ok lit
read_val_rec (suc l) (wireu wire) insts with (read_tree wire insts)
read_val_rec (suc l) (wireu wire) insts | nothing = missing wire
read_val_rec (suc l) (wireu wire) insts | just (assignop val _) = (read_val_rec l val insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) with (read_val_rec l wa insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) with (read_val_rec l wb insts)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | (ok q) =  ok ((func_from_op op) p q)
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | k = k
read_val_rec (suc l) (wireu wire) insts | just (binop wa op wb _) | k = k

read_val_rec (suc l) (wireu wire) insts | just (notop wa _) with (read_val_rec l wa insts)
read_val_rec (suc l) (wireu wire) insts | just (notop wa _) | (ok r) = ok (bit_not r)
read_val_rec (suc l) (wireu wire) insts | just (notop wa _) | k = k
read_val_rec (suc l) (wireu wire) insts | just _ = failed

write_val : String → Nat → List Assignment → List Assignment
write_val wire val [] = (assm wire val) ∷ []
write_val wire val ((assm w old) ∷ xs) = if wire == w
  then (assm wire val) ∷ xs
  else (assm w old) ∷ (write_val wire val xs)

calc_inst : Inst → List Assignment → Maybe Nat
calc_inst (assignop val _) db = read_val val db
calc_inst (binop wa op wb _) db with (read_val wa db)
calc_inst (binop wa op wb _) db | (just p) with (read_val wb db)
calc_inst (binop wa op wb _) db | (just p) | (just q) = just ((func_from_op op) p q)
calc_inst (binop wa op wb _) db | (just p) | nothing = nothing
calc_inst (binop wa op wb _) db | nothing = nothing
calc_inst (notop wa _) db with (read_val wa db)
calc_inst (notop wa _) db | (just p) = just (bit_not p)
calc_inst (notop wa _) db | nothing = nothing
calc_inst _ _ = nothing

find_init_know : List Inst → List Assignment
find_init_know [] = []
find_init_know ((assignop (litu l) wire) ∷ xs) = (assm wire l) ∷ (find_init_know xs)
find_init_know (_ ∷ xs) = (find_init_know xs)

mk_assm_tree : List Inst → LookupTree String Assignment
mk_assm_tree inp = build_tree _==_ str_lt (map (λ {(assm wire l) → (wire , (assm wire l)) }) (find_init_know inp))

needed_inputs : Inst → List TermUnion
needed_inputs (assignop wa _) = wa ∷ []
needed_inputs (binop wa op wb _) = wa ∷ wb ∷ []
needed_inputs (notop wa _) = wa ∷ []
needed_inputs _ = []

all_known : List TermUnion → LookupTree String Assignment → Bool
all_known [] _ = true
all_known ((litu l) ∷ xs) known = (all_known xs known)
all_known ((wireu w) ∷ xs) known = (has_val w known) ∧ (all_known xs known)

replace_known : TermUnion → LookupTree String Assignment → TermUnion
replace_known (litu l) db = litu l
replace_known (wireu w) db with (read_tree w db)
replace_known (wireu w) db | nothing = wireu w
replace_known (wireu w) db | just (assm _ v) = litu v

replace_known_inst : Inst → LookupTree String Assignment → Inst
replace_known_inst (assignop val o) db = assignop (replace_known val db) o
replace_known_inst (binop wa op wb o) db = (binop (replace_known wa db) op (replace_known wb db) o)
replace_known_inst (notop wa o) db = notop (replace_known wa db) o
replace_known_inst x db = x

find_next_known : List String → LookupTree String Inst → LookupTree String Assignment → (List String × LookupTree String Assignment)
find_next_known [] db known = ([] , known)
find_next_known (x ∷ xs) db known with (read_tree x db)
find_next_known (x ∷ xs) db known | nothing = find_next_known xs db known
find_next_known (x ∷ xs) db known | (just inst) with (needed_inputs inst)
find_next_known (x ∷ xs) db known | (just inst) | [] = find_next_known xs db known
find_next_known (x ∷ xs) db known | (just inst) | terms with (all_known terms known)
find_next_known (x ∷ xs) db known | (just inst) | terms | false with (find_next_known xs db known)
find_next_known (x ∷ xs) db known | (just inst) | terms | false | (needed , nassm) = ((x ∷ needed) , nassm)
find_next_known (x ∷ xs) db known | (just inst) | terms | true with (calc_inst (replace_known_inst inst known) [] )
find_next_known (x ∷ xs) db known | (just inst) | terms | true | nothing = (find_next_known xs db (set_val x (assm x 1000000) known))
find_next_known (x ∷ xs) db known | (just inst) | terms | true | (just v) = (find_next_known xs db (set_val x (assm x v) known))

find_next_iter : Nat → List String → LookupTree String Inst → LookupTree String Assignment → LookupTree String Assignment
find_next_iter 0 _ _ known = known
find_next_iter _ [] _ known = known
find_next_iter (suc l) inp db known with (find_next_known inp db known)
find_next_iter (suc l) inp db known | ([] , nknown) = nknown
find_next_iter (suc l) inp db known | (needed , nknown) = find_next_iter l needed db nknown

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

test_lshift : bit_lshift 2  1 ≡ 4
test_lshift = refl

test_bitor : bit_or  2 1 ≡ 3
test_bitor = refl

test_apply_inst : apply_inst (assignop (litu 123) "a") ((assm "b" 23) ∷ (assm "a" 45) ∷ (assm "q" 3) ∷ []) ≡ ((assm "b" 23) ∷ (assm "a" 123) ∷ (assm "q" 3) ∷ [])
test_apply_inst = refl

test_read_val_rec : read_val_rec 100 (wireu "a") (mk_tree ((binop (wireu "b") OR (wireu "b") "a") ∷ (assignop (litu 123) "b") ∷ [])) ≡ ok 123
test_read_val_rec = refl

test_one_and : apply_inst (parse_line "1 AND 1 -> a") [] ≡ ((assm "a" 1) ∷ [])
test_one_and = refl

run_sim : String → String
run_sim x =
  unlines (map show_assm (all_values atree)) ++ "\n"
  where
    atree = (find_next_iter (suc(length (lines x)))
      (map out_wire db)
      (mk_tree db)
      (mk_assm_tree db))
      where
        db : List Inst
        db = (assignop (litu 956) "b") ∷ (map parse_line (lines x))

--run_sim x with read_val_rec (suc(length (lines x))) (wireu "a") (mk_tree (map parse_line (lines x)))
--... | (missing wire) = "wire was missing: " ++ wire ++ "\n"
--... | ok p = "a: " ++ (show p) ++ "\n"
--... | hit_limit = "hit limit"
--... | _ = "failed"
