module Towers.Implementation where

open import Cubical.Foundations.Prelude
--import Cubical.Foundations.Isomorphism as Iso
import Cubical.Categories.Bifunctor as Bifunctor

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation as Prop
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Nat using (_+_)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Instances.FullSubcategory

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
--     B C D E : Category ℓ ℓ'



record Advancement (A : Category ℓ ℓ') ℓa : Type (ℓ-max (ℓ-suc ℓa) (ℓ-max ℓ ℓ')) where
 field
  isAdvancing : ∀ {a a'} → A [ a , a' ] → Type ℓa
  idIsNotAdvancing : ∀ {a} → isAdvancing (Category.id A {a}) → ⊥
  transˡ : ∀ {a a' a''} → (f : A [ a , a' ]) (g : A [ a' , a'' ])
             → isAdvancing g → isAdvancing (f ⋆⟨ A ⟩ g)
  transʳ : ∀ {a a' a''} → (f : A [ a , a' ]) (g : A [ a' , a'' ])
             → isAdvancing f → isAdvancing (f ⋆⟨ A ⟩ g)




module _ {ℓP ℓP' ℓP'' ℓa} (A : Category ℓ ℓ') (C : Category ℓ'' ℓ''') where

 module A = Category A
 module C = Category C


 private
   variable
     a a' a'' : A.ob
     c c' c'' : C.ob

 record Implementation : Type (ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓP''))) ) ) where

  field
   isObservable : Category.ob C → Type ℓP
   isSimpleA-hom : A.Hom[ a , a' ] → Type ℓP'
   isSimpleC-hom : C.Hom[ c , c' ] → Type ℓP''



  O : Category (ℓ-max ℓ'' ℓP) ℓ'''
  O = FullSubcategory C isObservable

  module O = Category O

  field
   Φ : Functor O A


  private
    variable
      o o' o'' : O.ob



  record IsCompleteImpl : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓP''))) ) ))  where
   field
    isCompleteImpl :
     (h : A.Hom[ Φ ⟅ o ⟆  , a' ]) → isSimpleA-hom h →
        Σ[ o' ∈ O.ob  ]
        Σ[ g ∈ O.Hom[ o , o' ] ] (isSimpleC-hom g ×
       (Σ[ p ∈ Φ ⟅ o' ⟆ ≡ a' ] PathP (λ i → A.Hom[ Φ ⟅ o ⟆ , p i ]) (Φ ⟪ g ⟫)  h ))


  record IsObservableImpl : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓP''))) ) )) where
   field
    isObservableImpl : (f : C.Hom[ c , c' ]) →
     isObservable c →
      Σ[ c'' ∈ C.ob ]
      Σ[ g   ∈ C.Hom[ c' , c'' ]
        ] isObservable c'' × isSimpleC-hom g



  record IsLivenessImpl : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓa))) ) )) where
    field
     advancementA : Advancement A ℓa
     advancementC : Advancement C ℓa

    module advA = Advancement advancementA
    module advC = Advancement advancementC

    field
     isLivenessImpl :
       ∀ (f : C.Hom[ c , c' ]) →
       advC.isAdvancing f →
       (isObs-c : isObservable c) →
       Σ[ c'' ∈ C.ob ]
       Σ[ isObs-c'' ∈ isObservable c'' ]
       Σ[ f' ∈ C.Hom[ c , c'' ] ]
       Σ[ g ∈ C.Hom[ c'' , c' ] ]
       advA.isAdvancing (Functor.F-hom Φ {_ , isObs-c} {_ , isObs-c''}  f')
