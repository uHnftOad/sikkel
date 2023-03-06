--------------------------------------------------
-- Reexporting the syntax for types in parametric type theory
--   + definition of some synonyms.
--------------------------------------------------

open import Applications.UnaryParametricity.MSTT.TypeExtension.PredExtension

module Applications.UnaryParametricity.MSTT.Syntax.Type (pred-ext : PredExt) where

open import Data.Product
open import Data.Unit

open import Applications.UnaryParametricity.MSTT.ModeTheory
open import Applications.UnaryParametricity.MSTT.TypeExtension pred-ext


import MSTT.Syntax.Type unary-par-mode-theory par-ty-ext as GRType
open GRType using (Ext)
open GRType public hiding (Ext)

pattern FromPred c = Ext (FromPred-code c) tt
    -- Ext (FromPred-code c) tt : TyExpre ¶.
