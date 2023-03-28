
module d19.elephant where

open import util.list_stuff using (words ; lines ; unmaybe ; hard-unmaybe ; filterᵇ ; each-one ; make-perms ; rem-dot ; append-front-all ; all-replacements ; cartproduct ; min-by-f ; enumerate ; split ; empty-table ; show-table ; transpose ; eq-classes ; rem-match ; partitionᵇ ; deduplicateᵇ ; index-of) renaming (trim to trim-ch)
open import util.lookup using (str-lt ; quick-sort ; LookupStrTree) renaming (all-kv to all-str-kv)
open import util.lookup_nat using (LookupNatTree ; build-nat-tree ; has-val ; all-kv) renaming (set-val to set-tree ; read-val to read-tree ; rem-val to rem-tree)
open import util.json using (readIntMaybe ; rem-lst-c)
open import util.search using (search-rec-breadth ; search-rec-all)
open import util.hash using (hash-md5)
open import util.nat_stuff using (mod-nat ; div-nat ; lin-mod-system)
open import Data.Tree.Binary using (leaf ; node)
open import Agda.Builtin.String using (String)
open import Data.String.Base using (toList ; fromList ; _++_ ; unlines ; unwords ; intersperse ; fromChar ; padRight)
open import Data.String.Properties using (_==_)
open import Agda.Builtin.Nat using (Nat ; suc ; _<_ ; _+_ ; _-_ ; _*_) renaming (_==_ to _==n_)
open import Data.Nat.Base using (pred)
open import Data.Nat.Show using (show ; readMaybe ; showInBase)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer.Base using (_≤ᵇ_) renaming (_+_ to _+z_ ; _-_ to _-z_)
open import Data.Integer.Properties using (_≟_)
open import Data.Integer.Show using () renaming (show to showz)
open import Agda.Builtin.List using (List ; [] ; _∷_)
open import Data.List using (map ; foldr ; concat ; length ; zip ; take ; drop ; head ; last; tail ; any ; all ; cartesianProductWith ; applyUpTo ; scanr ; reverse)
open import Agda.Builtin.Char using (Char ; primCharToNat ; primNatToChar)
open import Data.Char.Properties renaming (_==_ to _==c_ ; _<?_ to _<c_)
open import Agda.Builtin.Bool using (Bool ; true ; false)
open import Data.Bool.Base using (if_then_else_ ; _∧_ ; _∨_ ; not)
open import Agda.Builtin.Maybe using (Maybe ; nothing ; just)
open import Data.Maybe using (fromMaybe)
open import Function.Base using (_∘_ ; id ; const)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Agda.Builtin.Equality using (refl ; _≡_)
open import Relation.Nullary.Decidable using (isYes)


record Elf : Set where
  constructor elf
  field
    eid : Nat
    inv : Nat

show-elf : Elf → String
show-elf (elf x y) = "elf#" ++ show x ++ " has " ++ show y

init-list : Nat → List Elf
init-list = applyUpTo (λ {q → elf (suc q) 1})

one-step : Nat → List Elf × List Elf → List Elf × List Elf
one-step 0 p = p
one-step _ ([] , []) = ([] , [])
one-step (suc lm) ([] , xs) = one-step lm (reverse xs , [])
one-step _ (x ∷ [] , []) = (x ∷ [] , [])
one-step (suc lm) (x ∷ [] , xs) = one-step lm (x ∷ (reverse xs) , [])
one-step _ ((elf i v1) ∷ (elf _ v2) ∷ xs , ys) = (xs , (elf i (v1 + v2)) ∷ ys)


apply-all-steps-h : Nat → List Elf × List Elf → List Elf × List Elf
apply-all-steps-h 0 p = p
apply-all-steps-h _ (x ∷ [] , []) = (x ∷ [] , [])
apply-all-steps-h (suc lm) (xs , ys) = apply-all-steps-h lm (one-step 2 (xs , ys))

-- takes too much memory to complete for large input
apply-all-steps : List Elf → List Elf
apply-all-steps xs = proj₁ (apply-all-steps-h (suc(length xs)) (xs , []))


record EleSit : Set where
  constructor elesit
  field
    population : Nat
    starting : Nat
    skip : Nat

one-sit-step : EleSit → EleSit
one-sit-step (elesit 0 st sk) = (elesit 0 st sk)
one-sit-step (elesit 1 st sk) = (elesit 1 st sk)
one-sit-step (elesit pop st sk) = elesit (div-nat pop 2) (if (mod-nat pop 2 ==n 0) then st else (st + (2 * sk))) (2 * sk)

apply-all-sit-steps-h : Nat → EleSit → EleSit
apply-all-sit-steps-h 0 p = p
apply-all-sit-steps-h _ (elesit 1 st sk) = elesit 1 st sk
apply-all-sit-steps-h (suc lm) sit = apply-all-sit-steps-h lm (one-sit-step sit)

-- far faster and more mem efficient
apply-all-sit-steps : EleSit → Elf
apply-all-sit-steps sit = elf (EleSit.starting final) (EleSit.population sit)
  where
    final : EleSit
    final = apply-all-sit-steps-h (suc(EleSit.population sit)) sit

trim : String → String
trim = fromList ∘ trim-ch ∘ toList

find-final-elf : String → String
find-final-elf x = (show-elf ∘ apply-all-sit-steps) (elesit num 1 1) ++ "\n"
  where
    num : Nat
    num = (fromMaybe 1 ∘ readMaybe 10 ∘ trim) x

record RotSit : Set where
  constructor rotsit
  field
    remaining : List Nat

next-rotset : RotSit → RotSit
next-rotset (rotsit []) = rotsit []
next-rotset (rotsit (x ∷ [])) = rotsit (x ∷ [])
next-rotset (rotsit (x ∷ xs)) = rotsit (concat (lhs ∷ rhs ∷ (x ∷ []) ∷ []))
  where
    cutpoint : Nat
    cutpoint = if (mod-nat (length xs) 2 ==n 0)
      then pred (div-nat (length xs) 2)
      else (div-nat (length xs) 2)
    lhs : List Nat
    lhs = take cutpoint xs
    rhs : List Nat
    rhs = drop (suc cutpoint) xs

show-rotsit : RotSit → String
show-rotsit (rotsit xs) = (intersperse " " ∘ map show)  xs

apply-n : {A : Set} → Nat → (A → A) → (A → A)
apply-n 0 _ = id
apply-n 1 f = f
apply-n (suc n) f = f ∘ (apply-n n f)

rot-sit-all-h : Nat → RotSit → RotSit
rot-sit-all-h 0 x = x
rot-sit-all-h _ (rotsit (x ∷ [])) = rotsit (x ∷ [])
rot-sit-all-h (suc lm) rs = rot-sit-all-h lm next
  where
    next : RotSit
    next = next-rotset rs

greatest-pow-under-n-h : Nat → Nat → Nat → Nat → Nat
greatest-pow-under-n-h 0 target p temp = temp
greatest-pow-under-n-h (suc lm) target p temp with (p * temp < target)
greatest-pow-under-n-h (suc lm) target p temp | false = temp
greatest-pow-under-n-h (suc lm) target p temp | true = greatest-pow-under-n-h lm target p (p * temp)

greatest-pow-under-n : Nat → Nat → Nat
greatest-pow-under-n target p = greatest-pow-under-n-h target target p 1

quick-rot-sol : Nat → Nat
quick-rot-sol n = sol
  where
    gp3 : Nat
    gp3 = greatest-pow-under-n n 3
    sol : Nat
    sol with ((2 * gp3) < suc n)
    sol | false = n - gp3
    sol | true = gp3 + 2 * (n - (2 * gp3))

find-rot-sit-all : String → String
find-rot-sit-all x = "\n" ++ (unlines ∘ map (λ {(idx , sol) → padRight ' ' 5  (show idx) ++ padRight ' ' 5 (show-rotsit sol) ++ (padRight ' ' 5 ∘ show) (greatest-pow-under-n idx 3) ++ (padRight ' ' 5 ∘ show) (quick-rot-sol idx) })) pairs ++ "\n"
  where
    num : Nat
    num = (fromMaybe 1 ∘ readMaybe 10 ∘ trim) x
    pairs : List (Nat × RotSit)
    pairs = applyUpTo (λ {q → q , (rot-sit-all-h (suc q) ∘ rotsit ∘ applyUpTo suc) q}) num

test-apply-all-steps : (unlines ∘ map show-elf ∘ apply-all-steps ∘ init-list) 5 ≡ "elf#3 has 5"
test-apply-all-steps = refl

test-one-sit-step-a : one-sit-step (elesit 5 1 1) ≡ (elesit 2 3 2)
test-one-sit-step-a = refl

test-one-sit-step-b : one-sit-step (elesit 3 3 2) ≡ (elesit 1 7 4)
test-one-sit-step-b = refl

test-apply-all-sit-steps : (show-elf ∘ apply-all-sit-steps) (elesit 5 1 1) ≡ "elf#3 has 5"
test-apply-all-sit-steps = refl

test-apply-all-sit-steps-a : (unlines ∘ map show-elf ∘ apply-all-steps ∘ init-list) 4 ≡ (show-elf ∘ apply-all-sit-steps) (elesit 4 1 1)
test-apply-all-sit-steps-a = refl

test-apply-all-sit-steps-b : (unlines ∘ map show-elf ∘ apply-all-steps ∘ init-list) 7 ≡ (show-elf ∘ apply-all-sit-steps) (elesit 7 1 1)
test-apply-all-sit-steps-b = refl

test-apply-all-sit-steps-c : (unlines ∘ map show-elf ∘ apply-all-steps ∘ init-list) 19 ≡ (show-elf ∘ apply-all-sit-steps) (elesit 19 1 1)
test-apply-all-sit-steps-c = refl

test-find-final-elf : find-final-elf "5\n" ≡ "elf#3 has 5\n"
test-find-final-elf = refl

test-quick-rot-sol : quick-rot-sol 3001330 ≡ 1407007
test-quick-rot-sol = refl
