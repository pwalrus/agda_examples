module d23.asm where

open import util.list_stuff using (words ; lines ; unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has_val ; all_values ; all-keys ; all-kv ; LTPair) renaming (set_val to set-tree ; read_val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

data Inst : Set where
  hlf : String → Inst
  tpl : String → Inst
  inc : String → Inst
  jmp : Int → Inst
  jie : String → Int → Inst 
  jio : String → Int → Inst
  nop : Inst

State : Set
State = LookupStrTree Nat

Program : Set
Program = LookupNatTree Inst

show-state : State → String
show-state tree = intersperse ", " (map (λ {(k , v) → k ++ ": " ++ show v}) (all-kv tree))

show-state-m : Maybe State → String
show-state-m (just tree) = show-state tree
show-state-m nothing = "no state"

rem-plus : String → String
rem-plus x = fromList output
  where
    x-ch : List Char
    x-ch = toList x
    output : List Char
    output with x-ch
    output | ('+' ∷ xs) = xs
    output | xs = xs

rem-comma : String → String
rem-comma = fromList ∘ (rem-dot ',') ∘ toList

div-nat : Nat → Nat → Nat
div-nat x y = div-helper 0 (pred y) x (pred y)

mod-nat : Nat → Nat → Nat
mod-nat x y = mod-helper 0 (pred y) x (pred y)

parse-line-w : List String → Maybe Inst
parse-line-w ("nop" ∷ _) = just (nop)
parse-line-w ("hlf" ∷ reg ∷ _) = just (hlf reg)
parse-line-w ("tpl" ∷ reg ∷ _) = just (tpl reg)
parse-line-w ("inc" ∷ reg ∷ _) = just (inc reg)
parse-line-w ("jmp" ∷ offm ∷ _) with ((readIntMaybe ∘ toList ∘ rem-plus) offm)
parse-line-w ("jmp" ∷ offm ∷ _) | nothing = nothing
parse-line-w ("jmp" ∷ offm ∷ _) | (just offset) = just (jmp offset)
parse-line-w ("jie" ∷ reg ∷ offm ∷ _) with ((readIntMaybe ∘ toList ∘ rem-plus) offm)
parse-line-w ("jie" ∷ reg ∷ offm ∷ _) | nothing = nothing
parse-line-w ("jie" ∷ reg ∷ offm ∷ _) | (just offset) = just (jie (rem-comma reg) offset)
parse-line-w ("jio" ∷ reg ∷ offm ∷ _) with ((readIntMaybe ∘ toList ∘ rem-plus) offm)
parse-line-w ("jio" ∷ reg ∷ offm ∷ _) | nothing = nothing
parse-line-w ("jio" ∷ reg ∷ offm ∷ _) | (just offset) = just (jio (rem-comma reg) offset)
parse-line-w _ = nothing

parse-line : String → Maybe Inst
parse-line = parse-line-w ∘ words

adjust-val : String → (Nat → Nat) → State → State
adjust-val reg op st with (read-tree reg st)
adjust-val reg op st | nothing = set-tree reg (op 0) st
adjust-val reg op st | (just x) = set-tree reg (op x) st

inc-line : State → State
inc-line = adjust-val "current" (λ {q → q + 1})

non-negify : Int → Nat
non-negify (pos x) = x
non-negify _ = 0

is-even : String → State → Bool
is-even reg st with (read-tree reg st)
is-even reg st | nothing = true
is-even reg st | (just x) = (mod-nat x 2) ==n 0

is-one : String → State → Bool
is-one reg st with (read-tree reg st)
is-one reg st | nothing = false
is-one reg st | (just x) = x ==n 1

apply-state : Inst → State → State
apply-state nop st = inc-line st
apply-state (hlf reg) st = inc-line (adjust-val reg (λ {q → div-nat q 2}) st)
apply-state (tpl reg) st = inc-line (adjust-val reg (λ {q → 3 * q}) st)
apply-state (inc reg) st = inc-line (adjust-val reg (λ {q → suc q}) st)
apply-state (jmp offs) st = adjust-val "current" (λ {q → non-negify ((pos q) +z offs)}) st
apply-state (jie reg offs) st with (is-even reg st)
apply-state (jie reg offs) st | true = adjust-val "current" (λ {q → non-negify ((pos q) +z offs)}) st
apply-state (jie reg offs) st | false = inc-line st

apply-state (jio reg offs) st with (is-one reg st)
apply-state (jio reg offs) st | true = adjust-val "current" (λ {q → non-negify ((pos q) +z offs)}) st
apply-state (jio reg offs) st | false = inc-line st


next-state : Program → State → Maybe State
next-state prog st = new-state
  where
    linenum : Nat
    linenum with (read-tree "current" st)
    linenum | nothing = 0
    linenum | (just x) = x
    new-state : Maybe State
    new-state with (read-tree linenum prog)
    new-state | nothing = nothing
    new-state | (just inst) = just (apply-state inst st)

init-state : State
init-state = build-str-tree (("current" , 0) ∷ [])

p2-state : State
p2-state = build-str-tree (("current" , 0) ∷ ("a" , 1) ∷ [])

parse-prog : String → Program
parse-prog x = build-nat-tree (enumerate insts)
  where
    insts : List Inst
    insts = (unmaybe ∘ (map parse-line) ∘ lines) x

run-program : Nat → Program → State → State
run-program 0 _ st = st
run-program (suc l) prog st = next
  where
    next : State
    next with (next-state prog st)
    next | nothing = st
    next | (just new-st) = run-program l prog new-st

show-final-state : String → String
show-final-state x = show-state (run-program 10000 prog init-state) ++ "\n"
  where
  prog : Program
  prog = parse-prog x

show-final-state-p2 : String → String
show-final-state-p2 x = show-state (run-program 10000 prog p2-state) ++ "\n"
  where
  prog : Program
  prog = parse-prog x


test-parse-line-nop : parse-line "nop" ≡ just nop
test-parse-line-nop = refl

test-parse-line-hlf : parse-line "hlf a" ≡ just (hlf "a")
test-parse-line-hlf = refl

test-parse-line-jio : parse-line "jio a, +2" ≡ just (jio "a" (pos 2))
test-parse-line-jio = refl

test-next-state : show-state-m (next-state (parse-prog "inc a\njio a, +2\ntpl a\ninc a") init-state) ≡ "current: 1, a: 1"
test-next-state = refl

test-run-program : show-state (run-program 1000 (parse-prog "inc a\njio a, +2\ntpl a\ninc a") init-state) ≡ "current: 4, a: 2"
test-run-program = refl



