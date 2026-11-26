module

public import Research.PvsNP.Tau.ModularRootBound

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Machine-Verified Wave A Record Witnesses for the Shub–Smale $\tau$-Conjecture

This module machine-verifies the Wave A record constant-free straight-line program (`SLP`)
lower-bound witnesses for `zMaxGe`:

1. **Symmetric Midpoint Difference Family (`tau_record_11_eight_sym : zMaxGe 11 8`):**
   `2(X^2 - 1)(X^2 - 4)(X^2 - 9)(X^2 - 16)` in `11` gates with `8` distinct integer roots
   `{-4, -3, -2, -1, 1, 2, 3, 4}`, leaving `X = 0` free.
2. **Midpoint Difference Trick (`tau_record_12_nine : zMaxGe 12 9`):**
   Multiplying the symmetric `11`-gate witness by `X` yields `9` distinct integer roots
   `{-4, -3, -2, -1, 0, 1, 2, 3, 4}` in `12` gates.
3. **Shifted Pronic-Square with Gate Reuse (`tau_record_13_ten : zMaxGe 13 10`):**
   For `q = X(1 + X)`, `q * ((q - 16)^2 - 14^2) * ((q - 16)^2 - 16)` yields `10` distinct
   integer roots `{-6, -5, -4, -2, -1, 0, 1, 3, 4, 5}` in `13` gates.
4. **Bonus `15`-Gate Extension (`tau_record_15_eleven : zMaxGe 15 11`):**
   Extending the `13`-gate witness by `(X - 2)` yields `11` distinct integer roots
   `{-6, -5, -4, -2, -1, 0, 1, 2, 3, 4, 5}` in `15` gates.
-/

/-! ## 1. Concrete Wave A Record Witness SLPs (`τ = 11, 12, 13, 15`) -/

/-- Length-11 symmetric midpoint witness:
`(X^2 - (2 - X^2)^2) * (X^2 - 16) * ((2 - X^2) - (X^2 - 16))`,
with `8` distinct integer roots `{-4, -3, -2, -1, 1, 2, 3, 4}`. -/
def slpRecord11Sym : SLP 11 :=
  let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 1 + 1 = 2
  let p2 : SLP 2 := .snoc p1 .mul ⟨1, by omega⟩ ⟨1, by omega⟩     -- w3 = X^2
  let p3 : SLP 3 := .snoc p2 .sub ⟨2, by omega⟩ ⟨3, by omega⟩     -- w4 = 2 - X^2
  let p4 : SLP 4 := .snoc p3 .mul ⟨4, by omega⟩ ⟨4, by omega⟩     -- w5 = (2 - X^2)^2
  let p5 : SLP 5 := .snoc p4 .sub ⟨3, by omega⟩ ⟨5, by omega⟩     -- w6 = X^2 - (2 - X^2)^2
  let p6 : SLP 6 := .snoc p5 .mul ⟨2, by omega⟩ ⟨2, by omega⟩     -- w7 = 4
  let p7 : SLP 7 := .snoc p6 .mul ⟨7, by omega⟩ ⟨7, by omega⟩     -- w8 = 16
  let p8 : SLP 8 := .snoc p7 .sub ⟨3, by omega⟩ ⟨8, by omega⟩     -- w9 = X^2 - 16
  let p9 : SLP 9 := .snoc p8 .mul ⟨6, by omega⟩ ⟨9, by omega⟩     -- w10 = w6 * w9
  let p10 : SLP 10 := .snoc p9 .sub ⟨4, by omega⟩ ⟨9, by omega⟩   -- w11 = (2 - X^2) - (X^2 - 16)
  .snoc p10 .mul ⟨10, by omega⟩ ⟨11, by omega⟩                    -- w12 = w10 * w11

/-- Length-12 midpoint difference record witness:
`X * slpRecord11Sym`, with `9` distinct integer roots `{-4, -3, -2, -1, 0, 1, 2, 3, 4}`. -/
def slpRecord12 : SLP 12 :=
  .snoc slpRecord11Sym .mul ⟨1, by omega⟩ ⟨12, by omega⟩          -- w13 = X * w12

/-- Length-13 shifted pronic-square record witness:
`q * ((q - 16)^2 - 14^2) * ((q - 16)^2 - 16)` where `q = X * (1 + X)`,
with `10` distinct integer roots `{-6, -5, -4, -2, -1, 0, 1, 3, 4, 5}`. -/
def slpRecord13 : SLP 13 :=
  let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨1, by omega⟩    -- w2 = 1 + X
  let p2 : SLP 2 := .snoc p1 .mul ⟨1, by omega⟩ ⟨2, by omega⟩      -- w3 = q = X * (1 + X)
  let p3 : SLP 3 := .snoc p2 .add ⟨0, by omega⟩ ⟨0, by omega⟩      -- w4 = 2
  let p4 : SLP 4 := .snoc p3 .add ⟨4, by omega⟩ ⟨4, by omega⟩      -- w5 = 4
  let p5 : SLP 5 := .snoc p4 .mul ⟨5, by omega⟩ ⟨5, by omega⟩      -- w6 = 16
  let p6 : SLP 6 := .snoc p5 .sub ⟨3, by omega⟩ ⟨6, by omega⟩      -- w7 = q - 16
  let p7 : SLP 7 := .snoc p6 .mul ⟨7, by omega⟩ ⟨7, by omega⟩      -- w8 = (q - 16)^2
  let p8 : SLP 8 := .snoc p7 .sub ⟨6, by omega⟩ ⟨4, by omega⟩      -- w9 = 16 - 2 = 14
  let p9 : SLP 9 := .snoc p8 .mul ⟨9, by omega⟩ ⟨9, by omega⟩      -- w10 = 14^2 = 196
  let p10 : SLP 10 := .snoc p9 .sub ⟨8, by omega⟩ ⟨10, by omega⟩   -- w11 = (q - 16)^2 - 14^2
  let p11 : SLP 11 := .snoc p10 .sub ⟨8, by omega⟩ ⟨6, by omega⟩   -- w12 = (q - 16)^2 - 16
  let p12 : SLP 12 := .snoc p11 .mul ⟨11, by omega⟩ ⟨12, by omega⟩ -- w13 = w11 * w12
  .snoc p12 .mul ⟨13, by omega⟩ ⟨3, by omega⟩                      -- w14 = w13 * q

/-- Length-15 bonus record witness:
`slpRecord13 * (X - 2)`, with `11` distinct integer roots
`{-6, -5, -4, -2, -1, 0, 1, 2, 3, 4, 5}`. -/
def slpRecord15 : SLP 15 :=
  let p14 : SLP 14 := .snoc slpRecord13 .sub ⟨1, by omega⟩ ⟨4, by omega⟩ -- w15 = X - 2
  .snoc p14 .mul ⟨14, by omega⟩ ⟨15, by omega⟩                           -- w16 = w14 * (X - 2)

/-! ## 2. Machine-Verified Record Lower Bounds (`zMaxGe`) -/

theorem tau_record_11_eight_sym : zMaxGe 11 8 :=
  zMaxGe_of_evalInt slpRecord11Sym {-4, -3, -2, -1, 1, 2, 3, 4} 0
    (by decide) (by decide) (by decide)

theorem tau_record_12_nine : zMaxGe 12 9 :=
  zMaxGe_of_evalInt slpRecord12 {-4, -3, -2, -1, 0, 1, 2, 3, 4} 5
    (by decide) (by decide) (by decide)

theorem tau_record_13_ten : zMaxGe 13 10 :=
  zMaxGe_of_evalInt slpRecord13 {-6, -5, -4, -2, -1, 0, 1, 3, 4, 5} 2
    (by decide) (by decide) (by decide)

theorem tau_record_15_eleven : zMaxGe 15 11 :=
  zMaxGe_of_evalInt slpRecord15 {-6, -5, -4, -2, -1, 0, 1, 2, 3, 4, 5} (-3)
    (by decide) (by decide) (by decide)

end Research.PvsNP.Tau

end
