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
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (_+_)
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Morphism
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Instances.EssentialImage
open import Cubical.Categories.Instances.FullSubcategory

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


record Advancement (A : Category ℓ ℓ') ℓa : Type (ℓ-max (ℓ-suc ℓa) (ℓ-max ℓ ℓ')) where
 field
  isAdvancing : ∀ {a a'} → A [ a , a' ] → Type ℓa
  idIsNotAdvancing : ∀ {a} → isAdvancing (Category.id A {a}) → ⊥
  transˡ : ∀ {a a' a''} → (f : A [ a , a' ]) (g : A [ a' , a'' ])
             → isAdvancing g → isAdvancing (f ⋆⟨ A ⟩ g)
  transʳ : ∀ {a a' a''} → (f : A [ a , a' ]) (g : A [ a' , a'' ])
             → isAdvancing f → isAdvancing (f ⋆⟨ A ⟩ g)


-- private
--   variable
--     ℓa ℓP ℓP' ℓP'' : Level

module Impl {ℓa ℓP ℓP' ℓP''} (A : Category ℓ ℓ') (C : Category ℓ'' ℓ''') where

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


  record IsComplete : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓP'')))))) where
   field
    proof :
     (h : A.Hom[ Φ ⟅ o ⟆  , a' ]) → isSimpleA-hom h →
        Σ[ o' ∈ O.ob ]
        Σ[ g ∈ O.Hom[ o , o' ] ] (isSimpleC-hom g ×
       (Σ[ p ∈ Φ ⟅ o' ⟆ ≡ a' ] PathP (λ i → A.Hom[ Φ ⟅ o ⟆ , p i ]) (Φ ⟪ g ⟫) h))


  record IsObservable : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓP'')))))) where
   field
    proof : (f : C.Hom[ c , c' ]) →
     isObservable c →
      Σ[ c'' ∈ C.ob ]
      Σ[ g   ∈ C.Hom[ c' , c'' ]
        ] isObservable c'' × isSimpleC-hom g


  record IsLive : Type ((ℓ-max (ℓ-max ℓ ℓ')
            (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-suc (ℓ-max ℓP (ℓ-max ℓP' ℓa)))))) where
    field
     advancementA : Advancement A ℓa
     advancementC : Advancement C ℓa

    module advA = Advancement advancementA
    module advC = Advancement advancementC

    field
     proof :
       ∀ (f : C.Hom[ c , c' ]) →
       advC.isAdvancing f →
       (isObs-c : isObservable c) →
       Σ[ c'' ∈ C.ob ]
       Σ[ isObs-c'' ∈ isObservable c'' ]
       Σ[ f' ∈ C.Hom[ c , c'' ] ]
       Σ[ g ∈ C.Hom[ c'' , c' ] ]
       advA.isAdvancing (Functor.F-hom Φ {_ , isObs-c} {_ , isObs-c''}  f')


 open Implementation using (IsComplete)

 CompleteImplementation : Type _
 CompleteImplementation = Σ _ IsComplete

private
 variable
  A A' A'' : Category ℓ ℓ


module _ {ℓ} where
 open Impl {ℓ} {ℓ} {ℓ} {ℓ} {ℓ}  {ℓ} {ℓ} {ℓ}
 module _ where
  open Category

  IdImpl : ∀ A → Implementation A A
  IdImpl A .Impl.Implementation.isObservable _ = Unit*
  IdImpl A .Impl.Implementation.isSimpleA-hom _ = Unit*
  IdImpl A .Impl.Implementation.isSimpleC-hom _ = Unit*
  IdImpl A .Impl.Implementation.Φ = FullInclusion _ _

  _I∘_ : Implementation A A' → Implementation A' A'' → Implementation A A''
  _I∘_ {A} {A'} {A''} I₀  I₁ = I₀∘I₁
   where
   module I₀ = Implementation _ _ I₀
   module I₁ = Implementation _ _ I₁


   I₀∘I₁ : Implementation _ _
   I₀∘I₁ .Impl.Implementation.isObservable o = Σ[ o∈ ∈ I₁.isObservable o ] I₀.isObservable (I₁.Φ ⟅ o , o∈ ⟆)
   I₀∘I₁ .Impl.Implementation.isSimpleA-hom = I₀.isSimpleA-hom
   I₀∘I₁ .Impl.Implementation.isSimpleC-hom = I₁.isSimpleC-hom
   I₀∘I₁ .Impl.Implementation.Φ .Functor.F-ob z = I₀.Φ .Functor.F-ob
                                                   (Functor.F-ob I₁.Φ (z .fst , z .snd .fst) , z .snd .snd)
   I₀∘I₁ .Impl.Implementation.Φ .Functor.F-hom x = I₀.Φ .Functor.F-hom (I₁.Φ .Functor.F-hom x)
   I₀∘I₁ .Impl.Implementation.Φ .Functor.F-id = cong (I₀.Φ .Functor.F-hom) (I₁.Φ .Functor.F-id)
     ∙ I₀.Φ .Functor.F-id
   I₀∘I₁ .Impl.Implementation.Φ .Functor.F-seq f g =
     cong (I₀.Φ .Functor.F-hom) (I₁.Φ .Functor.F-seq _ _) ∙ I₀.Φ .Functor.F-seq _ _


 module Composition {A A' A'' : Category ℓ ℓ} (I₀ : Implementation A A') (I₁ : Implementation A' A'') where
  module U = Implementation _ _ I₀
  module L = Implementation _ _ I₁
  module T = Implementation _ _ (I₀ I∘ I₁)

  MiddleCompatible = ∀ {x y} (u : A' [ x , y ]) →
    U.isSimpleC-hom u → L.isSimpleA-hom u

  BottomClosed = ∀ {x y z} (s : A'' [ x , y ]) (t : A'' [ y , z ]) →
    L.isSimpleC-hom s → L.isSimpleC-hom t → L.isSimpleC-hom (s ⋆⟨ A'' ⟩ t)

  observable-compose : MiddleCompatible → BottomClosed →
    U.IsObservable → L.IsObservable → L.IsComplete → T.IsObservable
  T.IsObservable.proof (observable-compose compatible closed upper lower lower-complete) f (lo , up)
    with L.IsObservable.proof lower f lo
  ... | y , s , ly , simple-s
    with U.IsObservable.proof upper
           (Functor.F-hom L.Φ {_ , lo} {y , ly} (f ⋆⟨ A'' ⟩ s)) up
  ... | z , u , uz , simple-u
    with L.IsComplete.proof lower-complete {o = y , ly} u (compatible u simple-u)
  ... | (w , lw) , k , simple-k , p , _ =
    w , (s ⋆⟨ A'' ⟩ k) , (lw , subst U.isObservable (sym p) uz) , closed s k simple-s simple-k

  complete-compose : MiddleCompatible → U.IsComplete → L.IsComplete → T.IsComplete
  T.IsComplete.proof (complete-compose compatible upper lower) {o = x , lx , ux} {a' = a} h sh
    with U.IsComplete.proof upper {o = _ , ux} h sh
  ... | (z , uz) , u , su , p , pu
    with L.IsComplete.proof lower {o = x , lx} u (compatible u su)
  ... | (y , ly) , k , sk , q , qu =
    (y , ly , uy) , k , sk , eq
    where
    -- Transport the upper witness along the equality of endpoint/arrow pairs.
    Witness : (Σ[ b ∈ Category.ob A' ] A' [ L.Φ ⟅ x , lx ⟆ , b ]) → Type _
    Witness (b , v) = Σ[ ub ∈ U.isObservable b ]
      Σ[ r ∈ U.Φ ⟅ b , ub ⟆ ≡ a ]
        PathP (λ i → A [ U.Φ ⟅ _ , ux ⟆ , r i ])
              (Functor.F-hom U.Φ {_ , ux} {b , ub} v) h
    recovered = subst Witness (λ i → q (~ i) , qu (~ i)) (uz , p , pu)
    uy = recovered .fst
    eq = recovered .snd
