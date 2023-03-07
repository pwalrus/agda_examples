module adv2015 where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

open import d1.floors using (count-moves)
open import d1.enter using (count-enters)
open import d2.boxes using (calc-size-box)
open import d2.ribbon using (calc-ribbon)
open import d3.moves using (calc-unique-loc)
open import d3.robo_moves using (calc-unique-loc-b)
open import d5.nice_word using (judge-words)
open import d5.more_word using (judge-words-b)
open import d6.lights using (lights-on)
open import d6.brights using (brights-on)
open import d7.gates using (run-sim)
open import d8.escape using (rel-size)
open import d9.tsm using (shortest)
open import d10.look using (look-and-see-len)
open import d11.password using (next-pass)
open import d12.json using (sum-all-json)
open import d13.table using (total-hap)
open import d14.deer using (fastest-each-sec)
open import d15.cookie using (best-cookie)
open import d16.mfcsam using (find-sue)
open import d17.nog using (divide-nog)
open import d18.autom using (step-through ; step-through-b)
open import d19.chem using (count-replace ; steps-to-e-from-last)
open import d20.primes using (search-min-house)
open import d21.rpg using (cheapest-winner)
open import d22.magic using (cheapest-real-spells)
open import d23.asm using (show-final-state ; show-final-state-p2)
open import d24.balance using (min-quantum)
open import d25.diag using (find-big-code)

postulate interact : (String → String) → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC interact = \ f -> interact ( T.unpack . f . T.pack ) #-}

main : IO ⊤
main = interact find-big-code

