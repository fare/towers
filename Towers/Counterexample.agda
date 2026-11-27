module Towers.Counterexample where

open import Cubical.Foundations.Prelude hiding (lower)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Sigma
open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.FullSubcategory using (FullInclusion)
open import Towers.Implementation

-- The preorder on two objects induced by implication between their labels.
preorder : (P : Bool → Type₀) → ((b : Bool) → isProp (P b)) → Category ℓ-zero ℓ-zero
preorder P prop .Category.ob = Bool
preorder P prop .Category.Hom[_,_] x y = P x → P y
preorder P prop .Category.id x = x
preorder P prop .Category._⋆_ f g x = g (f x)
preorder P prop .Category.⋆IdL _ = refl
preorder P prop .Category.⋆IdR _ = refl
preorder P prop .Category.⋆Assoc _ _ _ = refl
preorder P prop .Category.isSetHom {y = y} = isProp→isSet (isPropΠ λ _ → prop y)

Label : Bool → Type₀
Label false = ⊥
Label true = Unit

label-prop : (b : Bool) → isProp (Label b)
label-prop false = isProp⊥
label-prop true = isPropUnit

-- Bottom permits false → true. Middle also permits the return to false.
Bottom = preorder Label label-prop
Middle = preorder (λ _ → Unit) (λ _ → isPropUnit)

Visible : Bool → Type₀
Visible false = Unit
Visible true = ⊥

open Impl {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero} {ℓ-zero}
lower : Implementation Middle Bottom
lower .Impl.Implementation.isObservable _ = Unit
lower .Impl.Implementation.isSimpleA-hom _ = Unit
lower .Impl.Implementation.isSimpleC-hom _ = Unit
lower .Impl.Implementation.Φ .Functor.F-ob = fst
lower .Impl.Implementation.Φ .Functor.F-hom _ _ = tt
lower .Impl.Implementation.Φ .Functor.F-id = refl
lower .Impl.Implementation.Φ .Functor.F-seq _ _ = refl

upper : Implementation Middle Middle
upper .Impl.Implementation.isObservable = Visible
upper .Impl.Implementation.isSimpleA-hom _ = Unit
upper .Impl.Implementation.isSimpleC-hom _ = Unit
upper .Impl.Implementation.Φ = FullInclusion _ _

module L = Implementation _ _ lower
module U = Implementation _ _ upper
module T = Implementation _ _ (upper I∘ lower)

lower-observable : L.IsObservable
L.IsObservable.proof lower-observable {c' = y} _ _ = y , (λ x → x) , tt , tt

upper-observable : U.IsObservable
U.IsObservable.proof upper-observable _ _ = false , (λ _ → tt) , tt , tt

composite-fails : T.IsObservable → ⊥
composite-fails obs
  with T.IsObservable.proof obs {c = false} {c' = true} (λ _ → tt) (tt , tt)
... | false , finish , _ = finish tt
... | true , _ , (_ , visible) , _ = visible
