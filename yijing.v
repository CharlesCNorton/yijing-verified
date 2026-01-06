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
(*     [The I Ching is the most ancient of classics, and contains the         *)
(*     origin of the binary arithmetic which I have discovered.]              *)
(*     -- Gottfried Wilhelm Leibniz, letter to Duke Rudolph August, 1697      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** * TODO

    1.  Transformation graph: formalize the 64 hexagrams as a graph where edges
        are single-line changes. Prove connectivity, diameter, path properties.

    2.  Complete moving line enumeration: enumerate all 4^6 = 4,096 moving
        hexagram configurations. Prove properties about the full transformation
        space.

    3.  King Wen sequence analysis: prove the pairing structure (inversions and
        complements) for all 32 pairs, not just the three examples.

    4.  Trigram algebra: formalize the 8 trigrams as a group under XOR/complement.
        Prove isomorphism to Z_2^3.

    5.  Nuclear hexagram chain: characterize fixed points and eventual cycles
        of the nuclear hexagram function on all 64 hexagrams.

    6.  Shao Yong circular arrangement: formalize the Fu Xi sequence geometric
        interpretation (hexagrams in a circle, binary complements opposite).

    7.  Line position semantics: define odd positions as yang places, even as
        yin places. Formalize "proper position" (yang line in yang place).

    8.  Constituting rulers: formalize the "ruling line" of each hexagram
        determined by structural properties.

    9.  Correspondence/resonance: define the corresponding pairs (1-4, 2-5, 3-6)
        and their properties.

    10. Time/season mapping: formalize the hexagram-to-month and seasonal cycle
        correspondences.

    11. Textual layer: represent the judgments (guaci) and line statements
        (yaoci) as structured data.

    12. Probability model depth: derive distribution over full readings, expected
        number of changing lines, variance calculations.

    13. Mutual hexagram relation: define and compute the "mutual" hexagram for
        each hexagram.

    14. King Wen sequence uniqueness: prove NoDup (all 64 hexagrams appear
        exactly once).

    15. Fu Xi sequence bijection: complete the bijection theorem (both
        directions, not just fuxi_is_binary_order).

    16. Document bit significance convention: explicitly state that vector
        position 0 (Fin.F1) = least significant bit (bottom line) and
        position 5 = most significant bit (top line).

    17. Remove unused definitions: Line_dec and UIP_nat appear to be
        scaffolding artifacts not used in subsequent proofs.
*)

(** * Citations and Primary Sources

    ** Classical Sources

    Zhouyi (Zhou Dynasty, c. 1000-750 BCE)
    - The original text of judgments and line statements

    Yijing / I Ching (Han Dynasty compilation, c. 136 BCE)
    - Includes Ten Wings commentaries

    ** Historical Sequences

    Fu Xi Sequence (Xiantian / Earlier Heaven)
    - Binary ordering: 0-63 in binary representation
    - Attributed to legendary Fu Xi, formalized by Shao Yong (1011-1077)

    King Wen Sequence (Houtian / Later Heaven)
    - Traditional ordering of 64 hexagrams
    - Attributed to King Wen of Zhou (c. 1100 BCE)

    ** Leibniz Sources

    Explication de l Arithmetique Binaire (1703)
    Correspondence with Joachim Bouvet, S.J. (1701-1703)
    Letter to Duke Rudolph August of Brunswick-Wolfenbuttel (1697)

    ** Modern Scholarship

    Wilhelm, Richard. I Ching (1923, German; 1950, English)
    Shaughnessy, Edward. I Ching: The Classic of Changes (1996)
    Rutt, Richard. The Book of Changes (Zhouyi) (1996)
*)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.BinNat.
Require Import Coq.Vectors.Vector.
Require Import Coq.QArith.QArith.
Require Import Lia.
Import ListNotations.
Import VectorNotations.
Open Scope nat_scope.

(** * Fundamental Types *)

Inductive Line : Type :=
  | Yang : Line      (* solid line, male, light, active *)
  | Yin : Line.      (* broken line, female, dark, receptive *)

Definition Line_dec : forall l1 l2 : Line, {l1 = l2} + {l1 <> l2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Inductive MovingLine : Type :=
  | OldYin : MovingLine     (* 6: changing yin, becomes yang *)
  | YoungYang : MovingLine  (* 7: stable yang *)
  | YoungYin : MovingLine   (* 8: stable yin *)
  | OldYang : MovingLine.   (* 9: changing yang, becomes yin *)

Definition line_of_moving (m : MovingLine) : Line :=
  match m with
  | OldYin => Yin
  | YoungYang => Yang
  | YoungYin => Yin
  | OldYang => Yang
  end.

Definition is_changing (m : MovingLine) : bool :=
  match m with
  | OldYin => true
  | OldYang => true
  | _ => false
  end.

Definition transform_line (m : MovingLine) : Line :=
  match m with
  | OldYin => Yang
  | OldYang => Yin
  | YoungYang => Yang
  | YoungYin => Yin
  end.

(** * Binary Encoding *)

Definition line_to_bit (l : Line) : bool :=
  match l with
  | Yang => true
  | Yin => false
  end.

Definition bit_to_line (b : bool) : Line :=
  if b then Yang else Yin.

Lemma line_bit_roundtrip : forall l, bit_to_line (line_to_bit l) = l.
Proof.
  intros []; reflexivity.
Qed.

Lemma bit_line_roundtrip : forall b, line_to_bit (bit_to_line b) = b.
Proof.
  intros []; reflexivity.
Qed.

(** * Trigrams (Bagua) *)

Definition Trigram := Vector.t Line 3.

Definition trigram_to_nat (t : Trigram) : nat :=
  let b0 := line_to_bit (Vector.nth t Fin.F1) in
  let b1 := line_to_bit (Vector.nth t (Fin.FS Fin.F1)) in
  let b2 := line_to_bit (Vector.nth t (Fin.FS (Fin.FS Fin.F1))) in
  (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition Qian : Trigram := [Yang; Yang; Yang].   (* Heaven, 7 *)
Definition Dui : Trigram := [Yin; Yang; Yang].     (* Lake, 6 *)
Definition Li : Trigram := [Yang; Yin; Yang].      (* Fire, 5 *)
Definition Zhen : Trigram := [Yin; Yin; Yang].     (* Thunder, 4 *)
Definition Xun : Trigram := [Yang; Yang; Yin].     (* Wind, 3 *)
Definition Kan : Trigram := [Yin; Yang; Yin].      (* Water, 2 *)
Definition Gen : Trigram := [Yang; Yin; Yin].      (* Mountain, 1 *)
Definition Kun : Trigram := [Yin; Yin; Yin].       (* Earth, 0 *)

Definition all_trigrams : list Trigram :=
  [Kun; Gen; Kan; Xun; Zhen; Li; Dui; Qian].

Theorem trigram_count : length all_trigrams = 8.
Proof. reflexivity. Qed.

Definition trigram_complement (t : Trigram) : Trigram :=
  Vector.map (fun l => match l with Yang => Yin | Yin => Yang end) t.

Theorem qian_kun_complement : trigram_complement Qian = Kun.
Proof. reflexivity. Qed.

Theorem kun_qian_complement : trigram_complement Kun = Qian.
Proof. reflexivity. Qed.

Lemma line_complement_involution : forall l,
  match match l with Yang => Yin | Yin => Yang end with Yang => Yin | Yin => Yang end = l.
Proof. intros []; reflexivity. Qed.

Theorem trigram_complement_involution : forall t, trigram_complement (trigram_complement t) = t.
Proof.
  intros t.
  unfold Trigram in t.
  apply (Vector.caseS' t). intros l0 t0.
  apply (Vector.caseS' t0). intros l1 t1.
  apply (Vector.caseS' t1). intros l2 t2.
  pattern t2. apply Vector.case0. simpl.
  destruct l0, l1, l2; reflexivity.
Qed.

(** * Hexagrams *)

Definition Hexagram := Vector.t Line 6.

Definition hexagram_to_nat (h : Hexagram) : nat :=
  let b0 := line_to_bit (Vector.nth h Fin.F1) in
  let b1 := line_to_bit (Vector.nth h (Fin.FS Fin.F1)) in
  let b2 := line_to_bit (Vector.nth h (Fin.FS (Fin.FS Fin.F1))) in
  let b3 := line_to_bit (Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) in
  let b4 := line_to_bit (Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) in
  let b5 := line_to_bit (Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) in
  (if b5 then 32 else 0) + (if b4 then 16 else 0) + (if b3 then 8 else 0) +
  (if b2 then 4 else 0) + (if b1 then 2 else 0) + (if b0 then 1 else 0).

Definition nat_to_hexagram (n : nat) : Hexagram :=
  let b0 := bit_to_line (Nat.testbit n 0) in
  let b1 := bit_to_line (Nat.testbit n 1) in
  let b2 := bit_to_line (Nat.testbit n 2) in
  let b3 := bit_to_line (Nat.testbit n 3) in
  let b4 := bit_to_line (Nat.testbit n 4) in
  let b5 := bit_to_line (Nat.testbit n 5) in
  [b0; b1; b2; b3; b4; b5].

Theorem hexagram_nat_roundtrip : forall n, n < 64 -> hexagram_to_nat (nat_to_hexagram n) = n.
Proof.
  intros n Hn.
  do 64 (destruct n as [|n]; [reflexivity|]); lia.
Qed.

Theorem nat_hexagram_roundtrip : forall h, nat_to_hexagram (hexagram_to_nat h) = h.
Proof.
  intros h.
  unfold Hexagram in h.
  apply (Vector.caseS' h). intros l0 h0.
  apply (Vector.caseS' h0). intros l1 h1.
  apply (Vector.caseS' h1). intros l2 h2.
  apply (Vector.caseS' h2). intros l3 h3.
  apply (Vector.caseS' h3). intros l4 h4.
  apply (Vector.caseS' h4). intros l5 h5.
  pattern h5. apply Vector.case0.
  destruct l0, l1, l2, l3, l4, l5; reflexivity.
Qed.

Definition lower_trigram (h : Hexagram) : Trigram :=
  [Vector.nth h Fin.F1;
   Vector.nth h (Fin.FS Fin.F1);
   Vector.nth h (Fin.FS (Fin.FS Fin.F1))].

Definition upper_trigram (h : Hexagram) : Trigram :=
  [Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))].

Definition hexagram_of_trigrams (lower upper : Trigram) : Hexagram :=
  Vector.append lower upper.

Theorem trigram_decomposition : forall h,
  hexagram_of_trigrams (lower_trigram h) (upper_trigram h) = h.
Proof.
  intros h.
  unfold Hexagram in h.
  apply (Vector.caseS' h). intros l0 h0.
  apply (Vector.caseS' h0). intros l1 h1.
  apply (Vector.caseS' h1). intros l2 h2.
  apply (Vector.caseS' h2). intros l3 h3.
  apply (Vector.caseS' h3). intros l4 h4.
  apply (Vector.caseS' h4). intros l5 h5.
  pattern h5. apply Vector.case0.
  reflexivity.
Qed.

(** * The 64 Hexagrams with King Wen Numbers *)

Module KingWen.

  Definition hex1_Qian : Hexagram := [Yang; Yang; Yang; Yang; Yang; Yang].
  Definition hex2_Kun : Hexagram := [Yin; Yin; Yin; Yin; Yin; Yin].
  Definition hex3_Zhun : Hexagram := [Yang; Yin; Yin; Yin; Yang; Yin].
  Definition hex4_Meng : Hexagram := [Yin; Yang; Yin; Yang; Yin; Yin].
  Definition hex5_Xu : Hexagram := [Yang; Yang; Yang; Yin; Yang; Yin].
  Definition hex6_Song : Hexagram := [Yin; Yang; Yin; Yang; Yang; Yang].
  Definition hex7_Shi : Hexagram := [Yin; Yang; Yin; Yin; Yin; Yin].
  Definition hex8_Bi : Hexagram := [Yin; Yin; Yin; Yin; Yang; Yin].
  Definition hex9_XiaoChu : Hexagram := [Yang; Yang; Yang; Yang; Yang; Yin].
  Definition hex10_Lu : Hexagram := [Yin; Yang; Yang; Yang; Yang; Yang].
  Definition hex11_Tai : Hexagram := [Yang; Yang; Yang; Yin; Yin; Yin].
  Definition hex12_Pi : Hexagram := [Yin; Yin; Yin; Yang; Yang; Yang].
  Definition hex13_TongRen : Hexagram := [Yang; Yang; Yang; Yang; Yin; Yang].
  Definition hex14_DaYou : Hexagram := [Yang; Yin; Yang; Yang; Yang; Yang].
  Definition hex15_Qian2 : Hexagram := [Yin; Yin; Yin; Yang; Yin; Yin].
  Definition hex16_Yu : Hexagram := [Yin; Yin; Yang; Yin; Yin; Yin].
  Definition hex17_Sui : Hexagram := [Yin; Yang; Yang; Yin; Yin; Yang].
  Definition hex18_Gu : Hexagram := [Yang; Yin; Yin; Yang; Yang; Yin].
  Definition hex19_Lin : Hexagram := [Yang; Yang; Yin; Yin; Yin; Yin].
  Definition hex20_Guan : Hexagram := [Yin; Yin; Yin; Yin; Yang; Yang].
  Definition hex21_ShiHe : Hexagram := [Yang; Yin; Yang; Yang; Yin; Yin].
  Definition hex22_Bi2 : Hexagram := [Yin; Yin; Yang; Yang; Yin; Yang].
  Definition hex23_Bo : Hexagram := [Yin; Yin; Yin; Yin; Yin; Yang].
  Definition hex24_Fu : Hexagram := [Yang; Yin; Yin; Yin; Yin; Yin].
  Definition hex25_WuWang : Hexagram := [Yang; Yang; Yang; Yang; Yin; Yin].
  Definition hex26_DaChu : Hexagram := [Yang; Yin; Yin; Yang; Yang; Yang].
  Definition hex27_Yi : Hexagram := [Yang; Yin; Yin; Yin; Yin; Yang].
  Definition hex28_DaGuo : Hexagram := [Yin; Yang; Yang; Yang; Yang; Yin].
  Definition hex29_Kan : Hexagram := [Yin; Yang; Yin; Yin; Yang; Yin].
  Definition hex30_Li : Hexagram := [Yang; Yin; Yang; Yang; Yin; Yang].
  Definition hex31_Xian : Hexagram := [Yin; Yang; Yang; Yang; Yin; Yin].
  Definition hex32_Heng : Hexagram := [Yin; Yin; Yang; Yang; Yang; Yin].
  Definition hex33_Dun : Hexagram := [Yang; Yang; Yang; Yang; Yin; Yin].
  Definition hex34_DaZhuang : Hexagram := [Yin; Yin; Yang; Yang; Yang; Yang].
  Definition hex35_Jin : Hexagram := [Yin; Yin; Yin; Yang; Yin; Yang].
  Definition hex36_MingYi : Hexagram := [Yang; Yin; Yang; Yin; Yin; Yin].
  Definition hex37_JiaRen : Hexagram := [Yang; Yang; Yin; Yang; Yin; Yang].
  Definition hex38_Kui : Hexagram := [Yang; Yin; Yang; Yin; Yang; Yang].
  Definition hex39_Jian : Hexagram := [Yin; Yang; Yin; Yang; Yin; Yin].
  Definition hex40_Xie : Hexagram := [Yin; Yin; Yang; Yin; Yang; Yin].
  Definition hex41_Sun : Hexagram := [Yang; Yin; Yin; Yin; Yang; Yang].
  Definition hex42_Yi2 : Hexagram := [Yang; Yang; Yin; Yin; Yin; Yang].
  Definition hex43_Guai : Hexagram := [Yin; Yang; Yang; Yang; Yang; Yang].
  Definition hex44_Gou : Hexagram := [Yang; Yang; Yang; Yang; Yang; Yin].
  Definition hex45_Cui : Hexagram := [Yin; Yin; Yin; Yin; Yang; Yang].
  Definition hex46_Sheng : Hexagram := [Yin; Yang; Yin; Yin; Yin; Yin].
  Definition hex47_Kun2 : Hexagram := [Yin; Yang; Yin; Yin; Yang; Yang].
  Definition hex48_Jing : Hexagram := [Yin; Yang; Yin; Yang; Yang; Yin].
  Definition hex49_Ge : Hexagram := [Yang; Yin; Yang; Yin; Yang; Yang].
  Definition hex50_Ding : Hexagram := [Yang; Yang; Yin; Yang; Yin; Yang].
  Definition hex51_Zhen : Hexagram := [Yin; Yin; Yang; Yin; Yin; Yang].
  Definition hex52_Gen : Hexagram := [Yang; Yin; Yin; Yang; Yin; Yin].
  Definition hex53_Jian2 : Hexagram := [Yang; Yang; Yin; Yang; Yin; Yin].
  Definition hex54_GuiMei : Hexagram := [Yin; Yin; Yang; Yin; Yang; Yang].
  Definition hex55_Feng : Hexagram := [Yin; Yin; Yang; Yang; Yin; Yang].
  Definition hex56_Lu2 : Hexagram := [Yang; Yin; Yang; Yang; Yin; Yin].
  Definition hex57_Xun : Hexagram := [Yang; Yang; Yin; Yang; Yang; Yin].
  Definition hex58_Dui : Hexagram := [Yin; Yang; Yang; Yin; Yang; Yang].
  Definition hex59_Huan : Hexagram := [Yin; Yang; Yin; Yang; Yang; Yin].
  Definition hex60_Jie : Hexagram := [Yin; Yang; Yin; Yin; Yang; Yang].
  Definition hex61_ZhongFu : Hexagram := [Yang; Yang; Yin; Yin; Yang; Yang].
  Definition hex62_XiaoGuo : Hexagram := [Yin; Yin; Yang; Yang; Yin; Yin].
  Definition hex63_Jiji : Hexagram := [Yang; Yin; Yang; Yin; Yang; Yin].
  Definition hex64_Weiji : Hexagram := [Yin; Yang; Yin; Yang; Yin; Yang].

  Definition king_wen_sequence : list Hexagram :=
    [hex1_Qian; hex2_Kun; hex3_Zhun; hex4_Meng; hex5_Xu; hex6_Song; hex7_Shi; hex8_Bi;
     hex9_XiaoChu; hex10_Lu; hex11_Tai; hex12_Pi; hex13_TongRen; hex14_DaYou; hex15_Qian2; hex16_Yu;
     hex17_Sui; hex18_Gu; hex19_Lin; hex20_Guan; hex21_ShiHe; hex22_Bi2; hex23_Bo; hex24_Fu;
     hex25_WuWang; hex26_DaChu; hex27_Yi; hex28_DaGuo; hex29_Kan; hex30_Li; hex31_Xian; hex32_Heng;
     hex33_Dun; hex34_DaZhuang; hex35_Jin; hex36_MingYi; hex37_JiaRen; hex38_Kui; hex39_Jian; hex40_Xie;
     hex41_Sun; hex42_Yi2; hex43_Guai; hex44_Gou; hex45_Cui; hex46_Sheng; hex47_Kun2; hex48_Jing;
     hex49_Ge; hex50_Ding; hex51_Zhen; hex52_Gen; hex53_Jian2; hex54_GuiMei; hex55_Feng; hex56_Lu2;
     hex57_Xun; hex58_Dui; hex59_Huan; hex60_Jie; hex61_ZhongFu; hex62_XiaoGuo; hex63_Jiji; hex64_Weiji].

  Theorem king_wen_length : length king_wen_sequence = 64.
  Proof. reflexivity. Qed.

End KingWen.

(** * Fu Xi Sequence (Binary Order) *)

Module FuXi.

  Definition fuxi_sequence : list Hexagram :=
    List.map nat_to_hexagram (seq 0 64).

  Theorem fuxi_is_binary_order : forall n, n < 64 ->
    hexagram_to_nat (List.nth n fuxi_sequence KingWen.hex1_Qian) = n.
  Proof.
    intros n Hn.
    unfold fuxi_sequence.
    rewrite List.nth_indep with (d' := nat_to_hexagram 0).
    - rewrite map_nth. rewrite seq_nth; [|lia]. simpl.
      apply hexagram_nat_roundtrip. lia.
    - rewrite map_length, seq_length. lia.
  Qed.

  Theorem fuxi_length : length fuxi_sequence = 64.
  Proof.
    unfold fuxi_sequence.
    rewrite map_length.
    rewrite seq_length.
    reflexivity.
  Qed.

End FuXi.

(** * Hexagram Symmetries *)

Definition hexagram_complement (h : Hexagram) : Hexagram :=
  Vector.map (fun l => match l with Yang => Yin | Yin => Yang end) h.

Definition hexagram_invert (h : Hexagram) : Hexagram :=
  [Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS Fin.F1);
   Vector.nth h Fin.F1].

Definition hexagram_nuclear (h : Hexagram) : Hexagram :=
  [Vector.nth h (Fin.FS Fin.F1);
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))].

Theorem hexagram_complement_involution : forall h,
  hexagram_complement (hexagram_complement h) = h.
Proof.
  intros h.
  unfold Hexagram in h.
  apply (Vector.caseS' h). intros l0 h0.
  apply (Vector.caseS' h0). intros l1 h1.
  apply (Vector.caseS' h1). intros l2 h2.
  apply (Vector.caseS' h2). intros l3 h3.
  apply (Vector.caseS' h3). intros l4 h4.
  apply (Vector.caseS' h4). intros l5 h5.
  pattern h5. apply Vector.case0.
  destruct l0, l1, l2, l3, l4, l5; reflexivity.
Qed.

Theorem invert_involution : forall h,
  hexagram_invert (hexagram_invert h) = h.
Proof.
  intros h.
  unfold Hexagram in h.
  apply (Vector.caseS' h). intros l0 h0.
  apply (Vector.caseS' h0). intros l1 h1.
  apply (Vector.caseS' h1). intros l2 h2.
  apply (Vector.caseS' h2). intros l3 h3.
  apply (Vector.caseS' h3). intros l4 h4.
  apply (Vector.caseS' h4). intros l5 h5.
  pattern h5. apply Vector.case0.
  reflexivity.
Qed.

Theorem qian_kun_are_complements :
  hexagram_complement KingWen.hex1_Qian = KingWen.hex2_Kun.
Proof.
  reflexivity.
Qed.

Require Import Eqdep_dec.

Lemma UIP_nat : forall (n : nat) (p q : n = n), p = q.
Proof. intros. apply UIP_dec. decide equality. Qed.

(** * Yarrow Stalk Oracle *)

Module YarrowStalk.

  (** The yarrow stalk method produces values 6, 7, 8, or 9.
      These map to MovingLine values with specific probabilities:
      - 6 (Old Yin):    1/16  -> OldYin
      - 7 (Young Yang): 5/16  -> YoungYang
      - 8 (Young Yin):  7/16  -> YoungYin
      - 9 (Old Yang):   3/16  -> OldYang
  *)

  Definition yarrow_value_to_moving (v : nat) : option MovingLine :=
    match v with
    | 6 => Some OldYin
    | 7 => Some YoungYang
    | 8 => Some YoungYin
    | 9 => Some OldYang
    | _ => None
    end.

  Definition yarrow_value_valid (v : nat) : bool :=
    match v with
    | 6 | 7 | 8 | 9 => true
    | _ => false
    end.

  Lemma yarrow_valid_iff : forall v,
    yarrow_value_valid v = true <-> (v = 6 \/ v = 7 \/ v = 8 \/ v = 9).
  Proof.
    intros v. split.
    - destruct v as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; simpl; try discriminate; auto.
    - intros [H|[H|[H|H]]]; subst; reflexivity.
  Qed.

  Lemma yarrow_valid_gives_some : forall v,
    yarrow_value_valid v = true -> exists m, yarrow_value_to_moving v = Some m.
  Proof.
    intros v H.
    destruct v as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; simpl in *; try discriminate; eauto.
  Qed.

  (** Probabilities as rationals (numerator out of 16) *)
  Definition prob_old_yin : Q := 1 # 16.
  Definition prob_young_yang : Q := 5 # 16.
  Definition prob_young_yin : Q := 7 # 16.
  Definition prob_old_yang : Q := 3 # 16.

  Theorem yarrow_probs_sum_to_one :
    (prob_old_yin + prob_young_yang + prob_young_yin + prob_old_yang == 1)%Q.
  Proof.
    unfold prob_old_yin, prob_young_yang, prob_young_yin, prob_old_yang.
    reflexivity.
  Qed.

  (** Probability of getting a changing line *)
  Definition prob_changing : Q := (prob_old_yin + prob_old_yang)%Q.

  Theorem prob_changing_is_quarter :
    (prob_changing == 1 # 4)%Q.
  Proof.
    unfold prob_changing, prob_old_yin, prob_old_yang.
    reflexivity.
  Qed.

  (** Probability of getting a yang line (stable or changing) *)
  Definition prob_yang : Q := (prob_young_yang + prob_old_yang)%Q.

  Theorem prob_yang_is_half :
    (prob_yang == 1 # 2)%Q.
  Proof.
    unfold prob_yang, prob_young_yang, prob_old_yang.
    reflexivity.
  Qed.

  (** Probability of getting a yin line (stable or changing) *)
  Definition prob_yin : Q := (prob_young_yin + prob_old_yin)%Q.

  Theorem prob_yin_is_half :
    (prob_yin == 1 # 2)%Q.
  Proof.
    unfold prob_yin, prob_young_yin, prob_old_yin.
    reflexivity.
  Qed.

End YarrowStalk.

(** * Coin Oracle *)

Module CoinOracle.

  (** The three-coin method: heads=3, tails=2. Sum gives 6-9.
      - 6 (2+2+2): Old Yin,    prob 1/8
      - 7 (2+2+3): Young Yang, prob 3/8
      - 8 (2+3+3): Young Yin,  prob 3/8
      - 9 (3+3+3): Old Yang,   prob 1/8
  *)

  Definition coin_prob_old_yin : Q := 1 # 8.
  Definition coin_prob_young_yang : Q := 3 # 8.
  Definition coin_prob_young_yin : Q := 3 # 8.
  Definition coin_prob_old_yang : Q := 1 # 8.

  Theorem coin_probs_sum_to_one :
    (coin_prob_old_yin + coin_prob_young_yang + coin_prob_young_yin + coin_prob_old_yang == 1)%Q.
  Proof.
    unfold coin_prob_old_yin, coin_prob_young_yang, coin_prob_young_yin, coin_prob_old_yang.
    reflexivity.
  Qed.

  Definition coin_prob_changing : Q := (coin_prob_old_yin + coin_prob_old_yang)%Q.

  Theorem coin_prob_changing_is_quarter :
    (coin_prob_changing == 1 # 4)%Q.
  Proof.
    unfold coin_prob_changing, coin_prob_old_yin, coin_prob_old_yang.
    reflexivity.
  Qed.

  (** Key difference from yarrow: coin method is symmetric *)
  Theorem coin_yin_yang_symmetric :
    (coin_prob_old_yin == coin_prob_old_yang)%Q /\
    (coin_prob_young_yin == coin_prob_young_yang)%Q.
  Proof.
    split; reflexivity.
  Qed.

  (** Yarrow is asymmetric - more likely to get yin *)
  Theorem yarrow_favors_yin :
    (YarrowStalk.prob_young_yin > YarrowStalk.prob_young_yang)%Q.
  Proof.
    unfold YarrowStalk.prob_young_yin, YarrowStalk.prob_young_yang.
    reflexivity.
  Qed.

End CoinOracle.

(** * Changing Line Transformations *)

Definition MovingHexagram := Vector.t MovingLine 6.

Definition primary_hexagram (m : MovingHexagram) : Hexagram :=
  Vector.map line_of_moving m.

Definition relating_hexagram (m : MovingHexagram) : Hexagram :=
  Vector.map transform_line m.

Definition has_changing_lines (m : MovingHexagram) : bool :=
  Vector.fold_left orb false (Vector.map is_changing m).

Lemma stable_line_same : forall m,
  is_changing m = false -> line_of_moving m = transform_line m.
Proof.
  intros [] H; simpl in *; try reflexivity; discriminate.
Qed.

Theorem no_changes_same_hexagram : forall l0 l1 l2 l3 l4 l5,
  has_changing_lines [l0; l1; l2; l3; l4; l5] = false ->
  primary_hexagram [l0; l1; l2; l3; l4; l5] = relating_hexagram [l0; l1; l2; l3; l4; l5].
Proof.
  intros l0 l1 l2 l3 l4 l5 H.
  unfold has_changing_lines, primary_hexagram, relating_hexagram in *. simpl in *.
  destruct l0, l1, l2, l3, l4, l5; simpl in H |- *;
    try discriminate H; reflexivity.
Qed.

(** * King Wen Sequence Structural Properties *)

(** In King Wen sequence, hexagrams come in pairs (1-2, 3-4, etc.).
    Each pair is related by either inversion or complementation. *)

Definition line_eqb (l1 l2 : Line) : bool :=
  match l1, l2 with
  | Yang, Yang => true
  | Yin, Yin => true
  | _, _ => false
  end.

Definition hexagram_eqb (h1 h2 : Hexagram) : bool :=
  line_eqb (Vector.nth h1 (Fin.F1)) (Vector.nth h2 (Fin.F1)) &&
  line_eqb (Vector.nth h1 (Fin.FS Fin.F1)) (Vector.nth h2 (Fin.FS Fin.F1)) &&
  line_eqb (Vector.nth h1 (Fin.FS (Fin.FS Fin.F1))) (Vector.nth h2 (Fin.FS (Fin.FS Fin.F1))) &&
  line_eqb (Vector.nth h1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) (Vector.nth h2 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) &&
  line_eqb (Vector.nth h1 (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (Vector.nth h2 (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) &&
  line_eqb (Vector.nth h1 (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) (Vector.nth h2 (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))).

Definition is_self_inverse (h : Hexagram) : bool :=
  hexagram_eqb h (hexagram_invert h).

Theorem qian_self_inverse : is_self_inverse KingWen.hex1_Qian = true.
Proof. native_compute. reflexivity. Qed.

Theorem kun_self_inverse : is_self_inverse KingWen.hex2_Kun = true.
Proof. native_compute. reflexivity. Qed.

(** Pair 1-2: Qian and Kun are complements (both self-inverse) *)
Theorem pair_1_2_complements :
  hexagram_complement KingWen.hex1_Qian = KingWen.hex2_Kun.
Proof. reflexivity. Qed.

(** Pair 11-12: Tai and Pi are complements *)
Theorem pair_11_12_complements :
  hexagram_complement KingWen.hex11_Tai = KingWen.hex12_Pi.
Proof. reflexivity. Qed.

(** Pair 63-64: Jiji and Weiji are complements *)
Theorem pair_63_64_complements :
  hexagram_complement KingWen.hex63_Jiji = KingWen.hex64_Weiji.
Proof. reflexivity. Qed.

(** * Nuclear Hexagram Properties *)

(** The nuclear hexagram is formed from the inner lines 2-5.
    Lower nuclear: lines 2-3-4
    Upper nuclear: lines 3-4-5 *)

Definition lower_nuclear (h : Hexagram) : Trigram :=
  [Vector.nth h (Fin.FS Fin.F1);
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)))].

Definition upper_nuclear (h : Hexagram) : Trigram :=
  [Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))].

(** Nuclear trigrams share the middle two lines *)
Theorem nuclear_trigrams_overlap : forall h,
  Vector.nth (lower_nuclear h) (Fin.FS Fin.F1) = Vector.nth (upper_nuclear h) Fin.F1 /\
  Vector.nth (lower_nuclear h) (Fin.FS (Fin.FS Fin.F1)) = Vector.nth (upper_nuclear h) (Fin.FS Fin.F1).
Proof.
  intros h. split; reflexivity.
Qed.

(** Qian's nuclear hexagram is Qian *)
Theorem qian_nuclear_is_qian :
  hexagram_nuclear KingWen.hex1_Qian = KingWen.hex1_Qian.
Proof. reflexivity. Qed.

(** Kun's nuclear hexagram is Kun *)
Theorem kun_nuclear_is_kun :
  hexagram_nuclear KingWen.hex2_Kun = KingWen.hex2_Kun.
Proof. reflexivity. Qed.

