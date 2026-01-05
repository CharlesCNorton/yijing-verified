(******************************************************************************)
(*                                                                            *)
(*                    Yijing: Hexagram Transformation Calculus                *)
(*                                                                            *)
(*     Formalizes the 64 hexagrams of the I Ching, the line transformation    *)
(*     rules (old yin to young yang, old yang to young yin), and the          *)
(*     binary structure Leibniz identified in his 1703 correspondence         *)
(*     with Joachim Bouvet. Proves properties of the King Wen sequence        *)
(*     and derives the bagua trigram symmetries.                              *)
(*                                                                            *)
(*     "The I Ching is the most ancient of classics, and contains the         *)
(*     origin of the binary arithmetic which I have discovered."              *)
(*     -- Gottfried Wilhelm Leibniz, letter to Duke Rudolph August, 1697      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

