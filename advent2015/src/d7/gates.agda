

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

show-assm : Assignment → String
show-assm (assm wire val) = wire ++ ": " ++ (show val)

mod-sixteen : Nat → Nat
mod-sixteen x = mod-helper 0 65535 x 65535

parse-bin : Nat → List Char → Maybe Nat
parse-bin start ('0' ∷ []) = just (2 * start)
parse-bin start ('1' ∷ []) = just (2 * start + 1)
parse-bin start ('0' ∷ xs) = (parse-bin (2 * start) xs)
parse-bin start ('1' ∷ xs) = (parse-bin (2 * start + 1) xs)
parse-bin _ _ = nothing

bit-lshift : Nat → Nat → Nat
bit-lshift val d = mod-sixteen (val * (2 ^ d))

bit-rshift : Nat → Nat → Nat
bit-rshift val d = div-helper 0 (2 ^ d - 1) val (2 ^ d - 1)

and-comb : List Char → List Char → List Char
and-comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (and-comb ls rs)
and-comb ('0' ∷ ls) ('1' ∷ rs) = '0' ∷ (and-comb ls rs)
and-comb ('1' ∷ ls) ('0' ∷ rs) = '0' ∷ (and-comb ls rs)
and-comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (and-comb ls rs)
and-comb _ _ = []

bit-and : Nat → Nat → Nat
bit-and l r with (parse-bin 0 (and-comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
... | just x = x
... | nothing = 0


or-comb : List Char → List Char → List Char
or-comb ('0' ∷ ls) ('0' ∷ rs) = '0' ∷ (or-comb ls rs)
or-comb ('0' ∷ ls) ('1' ∷ rs) = '1' ∷ (or-comb ls rs)
or-comb ('1' ∷ ls) ('0' ∷ rs) = '1' ∷ (or-comb ls rs)
or-comb ('1' ∷ ls) ('1' ∷ rs) = '1' ∷ (or-comb ls rs)
or-comb _ _ = []

bit-or : Nat → Nat →  Nat
bit-or l r with (parse-bin 0 (or-comb
  (toList (padLeft '0' 16 (showInBase 2 l)))
  (toList (padLeft '0' 16 (showInBase 2 r))) ))
... | just x = x
... | nothing = 0

not-comb : List Char → List Char
not-comb ('0' ∷ ls) = '1' ∷ (not-comb ls)
not-comb ('1' ∷ ls) = '0' ∷ (not-comb ls)
not-comb _ = []
    
bit-not : Nat → Nat
bit-not l with (parse-bin 0 (not-comb
  (toList (padLeft '0' 16 (showInBase 2 l)))))
... | just x = x
... | nothing = 0

out_wire : Inst → String
out_wire (assignop _ w)  = w
out_wire (binop _ _ _ w) = w
out_wire (notop _ w) = w
out_wire _ = "none"

read-val : TermUnion → List Assignment → Maybe Nat
read-val (litu lit) _ = just lit
read-val wire [] = nothing
read-val (wireu wire) ((assm x val) ∷ xs) = if wire == x then (just val) else read-val (wireu wire) xs

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
func_from_op AND = bit-and
func_from_op OR = bit-or
func_from_op LSHIFT = bit-lshift
func_from_op RSHIFT = bit-rshift

str_lt : String → String → Bool
str_lt a b = isYes (a <? b)

mk_tree : List Inst → LookupTree String Inst
mk_tree [] = build_tree _==_ str_lt []
mk_tree x = build_tree _==_ str_lt (map (λ {i → (out_wire i , i) }) x)

-- works on smaller examples but needs too much memory for the full puzzle
read-val-rec : Nat → TermUnion → LookupTree String Inst → RecResult
read-val-rec 0 _ _ = hit_limit
read-val-rec _ (litu lit) _ = ok lit
read-val-rec (suc l) (wireu wire) insts with (read_tree wire insts)
read-val-rec (suc l) (wireu wire) insts | nothing = missing wire
read-val-rec (suc l) (wireu wire) insts | just (assignop val _) = (read-val-rec l val insts)
read-val-rec (suc l) (wireu wire) insts | just (binop wa op wb _) with (read-val-rec l wa insts)
read-val-rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) with (read-val-rec l wb insts)
read-val-rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | (ok q) =  ok ((func_from_op op) p q)
read-val-rec (suc l) (wireu wire) insts | just (binop wa op wb _) | (ok p) | k = k
read-val-rec (suc l) (wireu wire) insts | just (binop wa op wb _) | k = k

read-val-rec (suc l) (wireu wire) insts | just (notop wa _) with (read-val-rec l wa insts)
read-val-rec (suc l) (wireu wire) insts | just (notop wa _) | (ok r) = ok (bit-not r)
read-val-rec (suc l) (wireu wire) insts | just (notop wa _) | k = k
read-val-rec (suc l) (wireu wire) insts | just _ = failed

write-val : String → Nat → List Assignment → List Assignment
write-val wire val [] = (assm wire val) ∷ []
write-val wire val ((assm w old) ∷ xs) = if wire == w
  then (assm wire val) ∷ xs
  else (assm w old) ∷ (write-val wire val xs)

calc-inst : Inst → List Assignment → Maybe Nat
calc-inst (assignop val _) db = read-val val db
calc-inst (binop wa op wb _) db with (read-val wa db)
calc-inst (binop wa op wb _) db | (just p) with (read-val wb db)
calc-inst (binop wa op wb _) db | (just p) | (just q) = just ((func_from_op op) p q)
calc-inst (binop wa op wb _) db | (just p) | nothing = nothing
calc-inst (binop wa op wb _) db | nothing = nothing
calc-inst (notop wa _) db with (read-val wa db)
calc-inst (notop wa _) db | (just p) = just (bit-not p)
calc-inst (notop wa _) db | nothing = nothing
calc-inst _ _ = nothing

find-init-know : List Inst → List Assignment
find-init-know [] = []
find-init-know ((assignop (litu l) wire) ∷ xs) = (assm wire l) ∷ (find-init-know xs)
find-init-know (_ ∷ xs) = (find-init-know xs)

mk-assm-tree : List Inst → LookupTree String Assignment
mk-assm-tree inp = build_tree _==_ str_lt (map (λ {(assm wire l) → (wire , (assm wire l)) }) (find-init-know inp))

needed-inputs : Inst → List TermUnion
needed-inputs (assignop wa _) = wa ∷ []
needed-inputs (binop wa op wb _) = wa ∷ wb ∷ []
needed-inputs (notop wa _) = wa ∷ []
needed-inputs _ = []

all-known : List TermUnion → LookupTree String Assignment → Bool
all-known [] _ = true
all-known ((litu l) ∷ xs) known = (all-known xs known)
all-known ((wireu w) ∷ xs) known = (has_val w known) ∧ (all-known xs known)

replace-known : TermUnion → LookupTree String Assignment → TermUnion
replace-known (litu l) db = litu l
replace-known (wireu w) db with (read_tree w db)
replace-known (wireu w) db | nothing = wireu w
replace-known (wireu w) db | just (assm _ v) = litu v

replace-known_inst : Inst → LookupTree String Assignment → Inst
replace-known_inst (assignop val o) db = assignop (replace-known val db) o
replace-known_inst (binop wa op wb o) db = (binop (replace-known wa db) op (replace-known wb db) o)
replace-known_inst (notop wa o) db = notop (replace-known wa db) o
replace-known_inst x db = x

find-next-known : List String → LookupTree String Inst → LookupTree String Assignment → (List String × LookupTree String Assignment)
find-next-known [] db known = ([] , known)
find-next-known (x ∷ xs) db known with (read_tree x db)
find-next-known (x ∷ xs) db known | nothing = find-next-known xs db known
find-next-known (x ∷ xs) db known | (just inst) with (needed-inputs inst)
find-next-known (x ∷ xs) db known | (just inst) | [] = find-next-known xs db known
find-next-known (x ∷ xs) db known | (just inst) | terms with (all-known terms known)
find-next-known (x ∷ xs) db known | (just inst) | terms | false with (find-next-known xs db known)
find-next-known (x ∷ xs) db known | (just inst) | terms | false | (needed , nassm) = ((x ∷ needed) , nassm)
find-next-known (x ∷ xs) db known | (just inst) | terms | true with (calc-inst (replace-known_inst inst known) [] )
find-next-known (x ∷ xs) db known | (just inst) | terms | true | nothing = (find-next-known xs db (set_val x (assm x 1000000) known))
find-next-known (x ∷ xs) db known | (just inst) | terms | true | (just v) = (find-next-known xs db (set_val x (assm x v) known))

find-next-iter : Nat → List String → LookupTree String Inst → LookupTree String Assignment → LookupTree String Assignment
find-next-iter 0 _ _ known = known
find-next-iter _ [] _ known = known
find-next-iter (suc l) inp db known with (find-next-known inp db known)
find-next-iter (suc l) inp db known | ([] , nknown) = nknown
find-next-iter (suc l) inp db known | (needed , nknown) = find-next-iter l needed db nknown

apply-inst : Inst → List Assignment → List Assignment
apply-inst inst db with (calc-inst inst db)
...                   | just x = write-val (out_wire inst) x db
...                   | nothing = db

apply-all-inst : List Inst → List Assignment → List Assignment
apply-all-inst [] db = db
apply-all-inst (x ∷ xs) db = apply-all-inst xs (apply-inst x db)

parse-term : String → TermUnion
parse-term x with (readMaybe 10 x)
...             | just y = (litu y)
...             | nothing = (wireu x)

parse-line-parts : List String → Inst
parse-line-parts (lit ∷ "->" ∷ wire ∷ _) = assignop (parse-term lit) wire
parse-line-parts (wa ∷ "AND" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse-term wa) AND (parse-term wb) wire
parse-line-parts (wa ∷ "OR" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse-term wa) OR (parse-term wb) wire
parse-line-parts (wa ∷ "LSHIFT" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse-term wa) LSHIFT (parse-term wb) wire
parse-line-parts (wa ∷ "RSHIFT" ∷ wb ∷ "->" ∷ wire ∷ _) = binop (parse-term wa) RSHIFT (parse-term wb) wire
parse-line-parts ("NOT" ∷ w ∷ "->" ∷ wire ∷ _) = notop (parse-term w) wire
parse-line-parts _ = nope

parse-line : String → Inst
parse-line x = parse-line-parts (words x)

test-parse-lshift : parse-line "w LSHIFT 3 -> f " ≡ binop (wireu "w") LSHIFT (litu 3) "f"
test-parse-lshift = refl

test-lshift : bit-lshift 2  1 ≡ 4
test-lshift = refl

test-bitor : bit-or  2 1 ≡ 3
test-bitor = refl

test-apply-inst : apply-inst (assignop (litu 123) "a") ((assm "b" 23) ∷ (assm "a" 45) ∷ (assm "q" 3) ∷ []) ≡ ((assm "b" 23) ∷ (assm "a" 123) ∷ (assm "q" 3) ∷ [])
test-apply-inst = refl

test-read-val-rec : read-val-rec 100 (wireu "a") (mk_tree ((binop (wireu "b") OR (wireu "b") "a") ∷ (assignop (litu 123) "b") ∷ [])) ≡ ok 123
test-read-val-rec = refl

test-one-and : apply-inst (parse-line "1 AND 1 -> a") [] ≡ ((assm "a" 1) ∷ [])
test-one-and = refl

run-sim : String → String
run-sim x =
  unlines (map show-assm (all_values atree)) ++ "\n"
  where
    atree = (find-next-iter (suc(length (lines x)))
      (map out_wire db)
      (mk_tree db)
      (mk-assm-tree db))
      where
        db : List Inst
        db = (assignop (litu 956) "b") ∷ (map parse-line (lines x))

--run-sim x with read-val-rec (suc(length (lines x))) (wireu "a") (mk_tree (map parse_line (lines x)))
--... | (missing wire) = "wire was missing: " ++ wire ++ "\n"
--... | ok p = "a: " ++ (show p) ++ "\n"
--... | hit_limit = "hit limit"
--... | _ = "failed"
