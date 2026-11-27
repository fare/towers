-- Unfinished category laws. See the unit-law obstruction in composition.md.
module Towers.WildCatDraft where

open import Cubical.Categories.Category
open import Cubical.WildCat.Base using (WildCat)
open import Cubical.Foundations.Prelude
open import Towers.Implementation

module _ {ℓ} where
 open Impl {ℓ} {ℓ} {ℓ} {ℓ} {ℓ} {ℓ} {ℓ} {ℓ}
 module WildCatOfImplementations where

 WildCatOfImplementations : WildCat (ℓ-suc ℓ) (ℓ-suc ℓ)
 WildCatOfImplementations .WildCat.ob = Category ℓ ℓ
 WildCatOfImplementations .WildCat.Hom[_,_] = Implementation
 WildCatOfImplementations .WildCat.id = IdImpl _
 WildCatOfImplementations .WildCat._⋆_ = _I∘_
 WildCatOfImplementations .WildCat.⋆IdL = {!!}
 WildCatOfImplementations .WildCat.⋆IdR = {!!}
 WildCatOfImplementations .WildCat.⋆Assoc = {!!}
