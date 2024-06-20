---
title:        Sublocale given by a nucleus
author:       ["Ian Ray", "Ayberk Tosun"]
date-started: 2024-06-20
---

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.FunExt
open import UF.Logic
open import MLTT.Spartan hiding (𝟚)
open import UF.PropTrunc
open import UF.Subsingletons

module Locales.Sublocale.SublocaleGivenByNucleus
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext) where

open import Locales.Frame pt fe hiding (𝟚)
open import Locales.Nucleus pt fe
open import Slice.Family

open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

open Locale

\end{code}

\section{Preliminaries}

Given a locale `X` and endofunction `j : 𝒪X → 𝒪X`, we say that an open
`U : 𝒪 X` is `j`-stable if it is a fixed point of `j`.

\begin{code}

module Fixsets (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 is-[_]-stable : (j : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → ⟨ 𝒪 X ⟩ → 𝓤 ⁺  ̇
 is-[ j ]-stable U = j U ＝ U

\end{code}

The type of `j`-stable opens of `X` is denoted `Fixset`.

\begin{code}

 Fixset : (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩) → 𝓤 ⁺  ̇
 Fixset j = Σ U ꞉ ⟨ 𝒪 X ⟩ , is-[ j ]-stable U

\end{code}

We work in a module parameterized by a locale `X` and nucleus `j` on it.

\begin{code}

module Construction-Of-Sublocale (X : Locale (𝓤 ⁺) 𝓤 𝓤) (𝒿 : Nucleus (𝒪 X)) where

 private
  j = pr₁ 𝒿

 open Fixsets X

\end{code}

The ordering on `j`-stable opens is the one in `𝒪 X`.

\begin{code}

 _≼_ : Fixset j → Fixset j → Ω 𝓤
 (U , _) ≼ (V , _) = U ≤[ poset-of (𝒪 X) ] V

\end{code}

\begin{code}

\end{code}

\begin{code}

 fixset-frame-structure : frame-structure 𝓤 𝓤 (Fixset j)
 fixset-frame-structure = (_≼_ , {!!} , {!!}) , {!!}

 sublocale : Locale (𝓤 ⁺) 𝓤 𝓤
 sublocale =
  record { ⟨_⟩ₗ = Fixset j ; frame-str-of = fixset-frame-structure }

\end{code}
