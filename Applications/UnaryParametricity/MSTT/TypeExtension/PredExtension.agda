--------------------------------------------------
-- The FromPred type constructor will allow to
-- interpret a number of tuples, consisting of an
-- Agda type and a relation, as MSTT types at mode ¶.
-- To retain decidable equivalence checking, such tuples
-- are encoded by a universe defined in this file.
--------------------------------------------------
module Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension where

open import Data.String hiding (Left)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Unary hiding (_⇒_; _⟨→⟩_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import MSTT.TCMonad

record PredType : Set₁ where
  field
    Left : Set
    Relation : Pred Left 0ℓ

open PredType public

record PredExt : Set₁ where
  field
    PredCode : Set
    show-code : PredCode → String
    _≟code_ : (c d : PredCode) → TCM (c ≡ d)
    interpret-code : PredCode → PredType

  CodeLeft : PredCode → Set
  CodeLeft = Left ∘ interpret-code

  CodeRelation : (c : PredCode) → Pred (CodeLeft c) 0ℓ
  CodeRelation = Relation ∘ interpret-code
