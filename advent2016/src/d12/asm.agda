module d12.asm where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate) renaming (trim to trim-ch)
open import util.lookup using (LookupStrTree ; LookupNatTree ; build-str-tree ; build-nat-tree ; has-val ; all-values ; all-keys ; all-kv ; LTPair) renaming (set-val to set-tree ; read-val to read-tree)
open import util.json using (readIntMaybe)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; intersperse)
open import Data.String.Properties using (_==_ ; _<?_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_ ; div-helper ; mod-helper) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using () renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Show using () renaming (show to show-z)
open import Data.Integer.Properties using (_≟_)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip)
open import Agda.Builtin.Char using (Char)
open import Data.Char.Properties using () renaming (_==_ to _==c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)

data ValReg : Set where
  val : Int → ValReg
  reg : String → ValReg

data Inst : Set where
  nop : Inst
  cpy : ValReg → ValReg → Inst
  inc : ValReg → Inst
  dec : ValReg → Inst
  jnz : ValReg → ValReg → Inst
  

State : Set
State = LookupStrTree Int

Program : Set
Program = LookupNatTree Inst

show-state : State → String
show-state tree = intersperse ", " (map (λ {(k , v) → k ++ ": " ++ show-z v}) (all-kv tree))

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

parse-valreg : String → ValReg
parse-valreg x with (readIntMaybe ∘ toList ∘ rem-plus) x
parse-valreg x | (just y) = val y
parse-valreg x | nothing = reg x

parse-line-w : List String → Maybe Inst
parse-line-w ("nop" ∷ _) = just (nop)
parse-line-w ("cpy" ∷ x ∷ y ∷ _) = just (cpy (parse-valreg x) (parse-valreg y))
parse-line-w ("inc" ∷ x ∷ _) = just (inc (parse-valreg x))
parse-line-w ("dec" ∷ x ∷ _) = just (dec (parse-valreg x))
parse-line-w ("jnz" ∷ x ∷ y ∷ _) = just (jnz (parse-valreg x) (parse-valreg y))
parse-line-w _ = nothing

parse-line : String → Maybe Inst
parse-line = parse-line-w ∘ words

adjust-val : String → (Int → Int) → State → State
adjust-val rn op st with (read-tree rn st)
adjust-val rn op st | nothing = set-tree rn (op (pos 0)) st
adjust-val rn op st | (just x) = set-tree rn (op x) st

inc-line : State → State
inc-line = adjust-val "current" (λ {q → q +z (pos 1)})

is-zero : String → State → Bool
is-zero rn st with (read-tree rn st)
is-zero rn st | nothing = true
is-zero rn st | (just x) = isYes (x ≟ (pos 0))

apply-state : Inst → State → State
apply-state nop st = inc-line st
apply-state (inc (reg rn)) st = inc-line (adjust-val rn (λ {q → q +z (pos 1)}) st)
apply-state (inc _) st = inc-line st
apply-state (dec (reg rn)) st = inc-line (adjust-val rn (λ {q → q -z (pos 1)}) st)
apply-state (dec _) st = inc-line st
apply-state (jnz (reg rn) (val offs)) st with (is-zero rn st)
apply-state (jnz (reg rn) (val offs)) st | false = adjust-val "current" (λ {q → q +z offs}) st
apply-state (jnz (reg rn) (val offs)) st | true = inc-line st
apply-state (jnz (val v1) (val offs)) st with (isYes (v1 ≟ (pos 0)))
apply-state (jnz (val v1) (val offs)) st | false = adjust-val "current" (λ {q → q +z offs}) st
apply-state (jnz (val v1) (val offs)) st | true = inc-line st
apply-state (jnz _ _) st = inc-line st
apply-state (cpy (reg rni) (reg rno)) st with (read-tree rni st)
apply-state (cpy (reg rni) (reg rno)) st | nothing = inc-line (adjust-val rno (λ {_ → (pos 0)}) st)
apply-state (cpy (reg rni) (reg rno)) st | (just v) = inc-line (adjust-val rno (λ {_ → v}) st)
apply-state (cpy (val v) (reg rno)) st = inc-line (adjust-val rno (λ {_ → v}) st)
apply-state (cpy _ (val _)) st = inc-line st


next-state : Program → State → Maybe State
next-state prog st = new-state
  where
    linenum : Nat
    linenum with (read-tree "current" st)
    linenum | (just (pos x)) = x
    linenum | _ = 1000000
    new-state : Maybe State
    new-state with (read-tree linenum prog)
    new-state | nothing = nothing
    new-state | (just inst) = just (apply-state inst st)

init-state : State
init-state = build-str-tree (("current" , (pos 0)) ∷ [])

parse-prog : String → Program
parse-prog x = build-nat-tree (enumerate insts)
  where
    insts : List Inst
    insts = (fromMaybe [] ∘ hard-unmaybe ∘ (map parse-line) ∘ lines) x

run-program : Nat → Program → State → State
run-program 0 _ st = st --set-tree "current" (negsuc 0) st
run-program (suc l) prog st = next
  where
    next : State
    next with (next-state prog st)
    next | nothing = st
    next | (just new-st) = run-program l prog new-st

show-final-state : String → String
show-final-state x = show-state (run-program 100000000 prog init-state) ++ "\n"
  where
  prog : Program
  prog = parse-prog x

test-parse-line-nop : parse-line "nop" ≡ just nop
test-parse-line-nop = refl

test-parse-line-inc : parse-line "inc a" ≡ just (inc (reg "a"))
test-parse-line-inc = refl

test-parse-line-dec : parse-line "dec a" ≡ just (dec (reg "a"))
test-parse-line-dec = refl

test-parse-line-cpy : parse-line "cpy a b" ≡ just (cpy (reg "a") (reg "b"))
test-parse-line-cpy = refl

test-parse-line-jnz : parse-line "jnz a -3" ≡ just (jnz (reg "a") (val (negsuc 2)))
test-parse-line-jnz = refl

test-next-state : show-state-m (next-state (parse-prog ("cpy 41 a\n" ++
  "inc a\n" ++
  "inc a\n" ++
  "dec a\n" ++
  "jnz a 2\n" ++
  "dec a")) init-state) ≡ "current: 1, a: 41"
test-next-state = refl

test-run-program : show-state (run-program 1000 (parse-prog ("cpy 41 a\n" ++
  "inc a\n" ++
  "inc a\n" ++
  "dec a\n" ++
  "jnz a 2\n" ++
  "dec a")) init-state) ≡ "current: 6, a: 42"
test-run-program = refl



