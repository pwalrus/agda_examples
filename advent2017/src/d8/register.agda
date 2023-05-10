module d8.register where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; list-minus ; conseq ; index-of ; set-at) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; build-str-tree ; LTPair ; counter ; quick-sort ; str-lt ; all-values ; all-keys ; all-kv ; has-val) renaming (set-val to set-tree ; read-val to read-tree)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree)
open import util.json using (readIntMaybe)
open import util.search using (search-rec-breadth-dedup ; branch-bound)
open import util.nat_stuff using (div-nat ; mod-nat)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse ; fromChar)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred ; _⊔_)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer using (∣_∣) renaming (_<?_ to _<?z_ ; _+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse ; head ; cartesianProductWith ; applyUpTo ; take ; drop ; any ; all)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_ ; _<?_ to _<c?_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function using (_∘_ ; id ; flip)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; map₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


data RegVal : Set where
  reg : String → RegVal
  val : Int → RegVal

parse-reg-val : String → RegVal
parse-reg-val x with (readIntMaybe (toList x))
parse-reg-val x | (just n) = val n
parse-reg-val x | _ = reg x

show-reg-val : RegVal → String
show-reg-val (reg n) = n
show-reg-val (val x) = show-z x

record Inst : Set where
  constructor inst
  field
    r1 : RegVal
    op : String
    r2 : RegVal

parse-inst-w : List String → Maybe Inst
parse-inst-w (a ∷ "inc" ∷ b ∷ []) = just (inst (parse-reg-val a) "inc" (parse-reg-val b))
parse-inst-w (a ∷ "dec" ∷ b ∷ []) = just (inst (parse-reg-val a) "dec" (parse-reg-val b))
parse-inst-w _ = nothing

show-inst : Inst → String
show-inst (inst a op b) = show-reg-val a ++ " " ++ op ++ " " ++ show-reg-val b

record Cond : Set where
  constructor cond
  field
    r1 : RegVal
    op : String
    r2 : RegVal

parse-cond-w : List String → Maybe Cond
parse-cond-w (a ∷ "<" ∷ b ∷ []) = just (cond (parse-reg-val a) "<" (parse-reg-val b))
parse-cond-w (a ∷ ">" ∷ b ∷ []) = just (cond (parse-reg-val a) ">" (parse-reg-val b))
parse-cond-w (a ∷ "<=" ∷ b ∷ []) = just (cond (parse-reg-val a) "<=" (parse-reg-val b))
parse-cond-w (a ∷ ">=" ∷ b ∷ []) = just (cond (parse-reg-val a) ">=" (parse-reg-val b))
parse-cond-w (a ∷ "==" ∷ b ∷ []) = just (cond (parse-reg-val a) "==" (parse-reg-val b))
parse-cond-w (a ∷ "!=" ∷ b ∷ []) = just (cond (parse-reg-val a) "!=" (parse-reg-val b))
parse-cond-w _ = nothing

show-cond : Cond → String
show-cond (cond a op b) = show-reg-val a ++ " " ++ op ++ " " ++ show-reg-val b

record Stmt : Set where
  constructor stmt
  field
    i1 : Inst
    c1 : Cond

parse-row-w : List String → Maybe Stmt
parse-row-w (a1 ∷ o1 ∷ b1 ∷ "if" ∷ a2 ∷ o2 ∷ b2 ∷ []) with (parse-inst-w (a1 ∷ o1 ∷ b1 ∷ []))
parse-row-w (a1 ∷ o1 ∷ b1 ∷ "if" ∷ a2 ∷ o2 ∷ b2 ∷ []) | (just i) with (parse-cond-w (a2 ∷ o2 ∷ b2 ∷ []))
parse-row-w (a1 ∷ o1 ∷ b1 ∷ "if" ∷ a2 ∷ o2 ∷ b2 ∷ []) | (just i) | (just c) = just (stmt i c)
parse-row-w (a1 ∷ o1 ∷ b1 ∷ "if" ∷ a2 ∷ o2 ∷ b2 ∷ []) | (just i) | _ = nothing
parse-row-w (a1 ∷ o1 ∷ b1 ∷ "if" ∷ a2 ∷ o2 ∷ b2 ∷ []) | _ = nothing
parse-row-w  _ = nothing

parse-row : String → Maybe Stmt
parse-row = parse-row-w ∘ words

show-stmt : Stmt → String
show-stmt (stmt i c) = show-inst i ++ " if " ++ show-cond c

State : Set
State = LookupStrTree Int

show-state : State → String
show-state = unlines ∘ map (λ {(a , b) → a ++ ": " ++ show-z b}) ∘ all-kv

read-state : State → RegVal → Int
read-state db (reg n) with (read-tree n db)
read-state db (reg n) | (just x) = x
read-state db (reg n) | _ = pos 0
read-state db (val x) = x

_==z_ : Int → Int → Bool
_==z_ a b = isYes (a ≟ b)

_<z_ : Int → Int → Bool
_<z_ a b = isYes (a <?z b)

check-cond : State → Cond → Bool
check-cond db (cond a op b) with (read-state db a , read-state db b)
check-cond db (cond a op b) | (v1 , v2) with (op)
check-cond db (cond a op b) | (v1 , v2) | "==" = v1 ==z v2
check-cond db (cond a op b) | (v1 , v2) | "<" = v1 <z v2
check-cond db (cond a op b) | (v1 , v2) | ">" = v2 <z v1
check-cond db (cond a op b) | (v1 , v2) | "!=" = not (v1 ==z v2)
check-cond db (cond a op b) | (v1 , v2) | ">=" = not (v1 <z v2)
check-cond db (cond a op b) | (v1 , v2) | "<=" = not (v2 <z v1)
check-cond db (cond a op b) | (v1 , v2) | _ = false

reset-highest : State → Int → State
reset-highest db x with (read-state db (reg "highest"))
reset-highest db x | (q) with (q <z x)
reset-highest db x | (q) | true = set-tree "highest" x db
reset-highest db x | (q) | false = db

apply-inst : Inst → State → State
apply-inst (inst (reg a) op b) db with (read-state db (reg a) , read-state db b)
apply-inst (inst (reg a) op b) db | (v1 , v2) with (op)
apply-inst (inst (reg a) op b) db | (v1 , v2) | "inc" = set-tree a (v1 +z v2) (reset-highest db (v1 +z v2))
apply-inst (inst (reg a) op b) db | (v1 , v2) | "dec" = set-tree a (v1 -z v2) (reset-highest db (v1 -z v2))
apply-inst (inst (reg a) op b) db | (v1 , v2) | _ = db
apply-inst _ db = db

apply-program : List Stmt → State → State
apply-program [] db = db
apply-program (x ∷ xs) db with (check-cond db (Stmt.c1 x))
apply-program (x ∷ xs) db | true = apply-program xs (apply-inst (Stmt.i1 x) db)
apply-program (x ∷ xs) db | false = apply-program xs db

run-cond-program : String → String
run-cond-program x = (show-state ∘ flip apply-program (build-str-tree (("" , pos 0) ∷ [])) ∘ unmaybe ∘ map parse-row ∘ lines) x ++ "\n"

test-parse-row-a : (show-stmt ∘ fromMaybe (stmt (inst (reg "") "op" (reg "")) (cond (reg "") "op" (reg ""))) ∘ parse-row) "b inc 5 if a > 1" ≡ "b inc 5 if a > 1"
test-parse-row-a = refl

test-parse-row-b : (show-stmt ∘ fromMaybe (stmt (inst (reg "") "op" (reg "")) (cond (reg "") "op" (reg ""))) ∘ parse-row) "c dec -10 if a >= 1" ≡ "c dec -10 if a >= 1"
test-parse-row-b = refl

test-fixture : String
test-fixture =
  "b inc 5 if a > 1\n" ++
  "a inc 1 if b < 5\n" ++
  "c dec -10 if a >= 1\n" ++
  "c inc -20 if c == 10"

test-apply-program : run-cond-program test-fixture ≡ "highest: 10\nc: -10\na: 1\n: 0\n"
test-apply-program = refl
