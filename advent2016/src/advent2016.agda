module advent2016 where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String

open import d1.taxi using (calc-taxi-dist ; calc-taxi-twice)
open import d2.keypad using (find-sequence2)
open import d3.triangle using (check-all-triangles)
open import d4.obscure using (sum-valid-sectors ; decrypt-names)
open import d6.common using (decode-by-freq2)
open import d7.ipv7 using (count-ssl-addr)
open import d8.rect using (count-lights-on)
open import d9.compress using (find-f-decom-size)
open import d10.bots using (calc-one-step)
open import d11.rtg using (show-minimal-moves)
open import d12.asm using (show-final-state)
open import d13.maze using (find-shortest-maze)
open import d14.otpad using (find-otp-index)
open import d15.discs using (perfect-align)
open import d16.dragon using (correct-checksum)
open import d17.maze using (iter-over-maze-longest)
open import d18.rogue using (show-safe-tile-count)
open import d19.elephant using (find-final-elf)

postulate interact : (String → String) → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC interact = \ f -> interact ( T.unpack . f . T.pack ) #-}

main : IO ⊤
main = interact find-rot-sit-all

