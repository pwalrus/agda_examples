module d23.asm where

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
open import Data.List using (map ; foldr ; concat ; length ; zip ; reverse)
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
  tgl : ValReg → Inst

show-val-reg : ValReg → String
show-val-reg (val v) = show-z v
show-val-reg (reg rn) = rn

show-inst : Inst → String
show-inst nop = "nop"
show-inst (cpy x y) = "cpy " ++ show-val-reg x ++ " " ++ show-val-reg y
show-inst (inc x) = "inc " ++ show-val-reg x
show-inst (dec x) = "dec " ++ show-val-reg x
show-inst (jnz x y ) = "jnz " ++ show-val-reg x ++ " " ++ show-val-reg y
show-inst (tgl x) = "tgl " ++ show-val-reg x



State : Set
State = LookupStrTree Int

Program : Set
Program = LookupNatTree (Bool × Inst)

show-program : Program → String
show-program = unlines ∘ map show-inst ∘ reverse ∘ map proj₂ ∘ map proj₂ ∘ all-kv

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
parse-line-w ("tgl" ∷ x ∷ _) = just (tgl (parse-valreg x))
parse-line-w _ = nothing

parse-line : String → Maybe Inst
parse-line = parse-line-w ∘ words

adjust-val : String → (Int → Int) → State → State
adjust-val rn op st with (read-tree rn st)
adjust-val rn op st | nothing = set-tree rn (op (pos 0)) st
adjust-val rn op st | (just x) = set-tree rn (op x) st

toggle-inst : Inst → Inst
toggle-inst nop = nop
toggle-inst (cpy x y) = jnz x y
toggle-inst (inc x) = dec x
toggle-inst (dec x) = inc x
toggle-inst (jnz x y) = cpy x y
toggle-inst (tgl x) = inc x

toggle-prog : Int → Int → Program → Program
toggle-prog current offs prog with (current +z offs)
toggle-prog current offs prog | (pos idx) with (read-tree idx prog)
toggle-prog current offs prog | (pos idx) | just (t , inst) = set-tree idx (not t , toggle-inst inst) prog
toggle-prog current offs prog | (pos idx) | _ = prog
toggle-prog current offs prog | _ = prog

inc-line : State → State
inc-line = adjust-val "current" (λ {q → q +z (pos 1)})

read-vr : ValReg → State → Int
read-vr (val v) _ = v
read-vr (reg rn) st with (read-tree rn st)
read-vr (reg rn) st | nothing = pos 0
read-vr (reg rn) st | (just x) = x

is-zero : ValReg → State → Bool
is-zero vr st with (read-vr vr st)
is-zero vr st | x = isYes (x ≟ (pos 0))

apply-state : Inst → (Program × State) → (Program × State)
apply-state nop (prg , st) = prg , inc-line st
apply-state (inc (reg rn)) (prg , st) = prg , inc-line (adjust-val rn (λ {q → q +z (pos 1)}) st)
apply-state (inc _) (prg , st) = prg , inc-line st
apply-state (dec (reg rn)) (prg , st) = prg , inc-line (adjust-val rn (λ {q → q -z (pos 1)}) st)
apply-state (dec _) (prg , st) = prg , inc-line st
apply-state (jnz vr1 vr2) (prg , st) with (is-zero vr1 st)
apply-state (jnz vr1 vr2) (prg , st) | false with (read-vr vr2 st)
apply-state (jnz vr1 vr2) (prg , st) | false | offs = prg , adjust-val "current" (λ {q → q +z offs}) st
apply-state (jnz vr1 vr2) (prg , st) | true = prg , inc-line st
apply-state (cpy vr1 (reg rno)) (prg , st) with (read-vr vr1 st)
apply-state (cpy vr1 (reg rno)) (prg , st) | v = prg , inc-line (adjust-val rno (λ {_ → v}) st)
apply-state (cpy _ (val _)) (prg , st) = prg , inc-line st
apply-state (tgl vr) (prg , st) with (read-vr vr st)
apply-state (tgl vr) (prg , st) | v with (read-tree "current" st)
apply-state (tgl vr) (prg , st) | v | (just curr) = toggle-prog curr v prg , inc-line st
apply-state (tgl vr) (prg , st) | v | _ = prg , inc-line st


next-state : Program → State → Maybe (Program × State)
next-state prog st = new-state
  where
    linenum : Nat
    linenum with (read-tree "current" st)
    linenum | (just (pos x)) = x
    linenum | _ = 1000000
    new-state : Maybe (Program × State)
    new-state with (read-tree linenum prog)
    new-state | nothing = nothing
    new-state | (just (t , inst)) = just (apply-state inst (prog , st))

init-state : State
init-state = build-str-tree (("current" , (pos 0)) ∷ [])

init-state-7 : State
init-state-7 = build-str-tree (("current" , (pos 0)) ∷ ("a" , (pos 7)) ∷ [])

parse-prog : String → Program
parse-prog x = build-nat-tree (enumerate insts)
  where
    insts : List (Bool × Inst)
    insts = (map (λ {q → false , q}) ∘ fromMaybe [] ∘ hard-unmaybe ∘ (map parse-line) ∘ lines) x

run-program : Nat → Program → State → (Program × State)
run-program 0 prog st = prog , st
run-program (suc l) prog st = next
  where
    next : Program × State
    next with (next-state prog st)
    next | nothing = prog , st
    next | (just (new-prog , new-st)) = run-program l new-prog new-st

show-prog-state : (Program × State) → String
show-prog-state (p , st) = show-program p ++ "\n\n" ++ show-state st 

show-tgl-state : String → String
show-tgl-state x = show-prog-state (run-program 100000000 prog init-state-7) ++ "\n"
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

test-parse-line-tgl : parse-line "tgl a" ≡ just (tgl (reg "a"))
test-parse-line-tgl = refl

test-fixture-prog : Program
test-fixture-prog = parse-prog (
  "cpy 41 a\n" ++
  "inc a\n" ++
  "inc a\n" ++
  "dec a\n" ++
  "jnz a 2\n" ++
  "dec a")

test-next-state : (show-state ∘ proj₂ ∘ fromMaybe (test-fixture-prog , init-state) ∘ next-state test-fixture-prog) init-state ≡ "current: 1, a: 41"
test-next-state = refl

test-run-program : show-state (proj₂(run-program 1000 (parse-prog ("cpy 41 a\n" ++
  "inc a\n" ++
  "inc a\n" ++
  "dec a\n" ++
  "jnz a 2\n" ++
  "dec a")) init-state)) ≡ "current: 6, a: 42"
test-run-program = refl

test-is-zero : is-zero (val (pos 1)) init-state ≡ false
test-is-zero = refl

test-run-program-tgl-a : show-prog-state ((run-program 1000 (parse-prog (
  "cpy 2 a\n" ++
  "tgl a\n" ++
  "tgl a\n" ++
  "tgl a\n" ++
  "cpy 1 a\n" ++
  "dec a\n" ++
  "dec a"
  )) init-state)) ≡
  "cpy 2 a\n" ++
  "tgl a\n" ++
  "tgl a\n" ++
  "inc a\n" ++
  "jnz 1 a\n" ++
  "dec a\n" ++
  "dec a\n"++
  "\ncurrent: 7, a: 3"
test-run-program-tgl-a = refl



