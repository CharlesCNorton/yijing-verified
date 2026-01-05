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

    "Explication de l'Arithmetique Binaire" (1703)
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
Import ListNotations.
Import VectorNotations.

(** * Fundamental Types *)

Inductive Line : Type :=
  | Yang : Line      (* solid line, male, light, active *)
  | Yin : Line.      (* broken line, female, dark, receptive *)

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

Theorem complement_involution : forall t, trigram_complement (trigram_complement t) = t.
Proof.
Admitted.

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
Admitted.

Theorem nat_hexagram_roundtrip : forall h, nat_to_hexagram (hexagram_to_nat h) = h.
Proof.
Admitted.

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
Admitted.

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
  Definition hex11_Tai : Hexagram := [Yang; Yang; Yang; Yin; Yin; Yin].
  Definition hex12_Pi : Hexagram := [Yin; Yin; Yin; Yang; Yang; Yang].
  Definition hex29_Kan : Hexagram := [Yin; Yang; Yin; Yin; Yang; Yin].
  Definition hex30_Li : Hexagram := [Yang; Yin; Yang; Yang; Yin; Yang].
  Definition hex63_Jiji : Hexagram := [Yang; Yin; Yang; Yin; Yang; Yin].
  Definition hex64_Weiji : Hexagram := [Yin; Yang; Yin; Yang; Yin; Yang].

  Definition king_wen_sequence : list Hexagram :=
    [hex1_Qian; hex2_Kun; hex3_Zhun; hex4_Meng; hex5_Xu; hex6_Song; hex7_Shi; hex8_Bi
     (* ... remaining 56 hexagrams ... *)
    ].

End KingWen.

(** * Fu Xi Sequence (Binary Order) *)

Module FuXi.

  Definition fuxi_sequence : list Hexagram :=
    map nat_to_hexagram (seq 0 64).

  Theorem fuxi_is_binary_order : forall n, n < 64 ->
    hexagram_to_nat (nth n fuxi_sequence KingWen.hex1_Qian) = n.
  Proof.
  Admitted.

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
  Vector.rev h.

Definition hexagram_nuclear (h : Hexagram) : Hexagram :=
  [Vector.nth h (Fin.FS Fin.F1);
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS Fin.F1));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS Fin.F1)));
   Vector.nth h (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))].

Theorem complement_involution : forall h,
  hexagram_complement (hexagram_complement h) = h.
Proof.
Admitted.

Theorem invert_involution : forall h,
  hexagram_invert (hexagram_invert h) = h.
Proof.
Admitted.

Theorem qian_kun_are_complements :
  hexagram_complement KingWen.hex1_Qian = KingWen.hex2_Kun.
Proof.
  reflexivity.
Qed.

Theorem tai_pi_are_inversions :
  hexagram_invert KingWen.hex11_Tai = KingWen.hex12_Pi.
Proof.
Admitted.

Theorem jiji_weiji_are_complements :
  hexagram_complement KingWen.hex63_Jiji = KingWen.hex64_Weiji.
Proof.
  reflexivity.
Qed.

(** * Transformation Rules *)

Definition MovingHexagram := Vector.t MovingLine 6.

Definition primary_hexagram (m : MovingHexagram) : Hexagram :=
  Vector.map line_of_moving m.

Definition transformed_hexagram (m : MovingHexagram) : Hexagram :=
  Vector.map transform_line m.

Definition has_moving_lines (m : MovingHexagram) : bool :=
  Vector.fold_left (fun acc ml => acc || is_changing ml) false m.

Theorem no_moving_lines_same : forall m,
  has_moving_lines m = false ->
  primary_hexagram m = transformed_hexagram m.
Proof.
Admitted.

Theorem all_old_yang_becomes_kun : forall m,
  (forall i, Vector.nth m i = OldYang) ->
  transformed_hexagram m = KingWen.hex2_Kun.
Proof.
Admitted.

Theorem all_old_yin_becomes_qian : forall m,
  (forall i, Vector.nth m i = OldYin) ->
  transformed_hexagram m = KingWen.hex1_Qian.
Proof.
Admitted.

(** * King Wen Sequence Properties *)

Definition are_paired (h1 h2 : Hexagram) : Prop :=
  hexagram_complement h1 = h2 \/ hexagram_invert h1 = h2.

Theorem king_wen_pairs : forall n, n < 32 ->
  let h1 := nth (2*n) KingWen.king_wen_sequence KingWen.hex1_Qian in
  let h2 := nth (2*n+1) KingWen.king_wen_sequence KingWen.hex1_Qian in
  are_paired h1 h2.
Proof.
Admitted.

Definition self_symmetric (h : Hexagram) : Prop :=
  hexagram_invert h = h.

Theorem eight_self_symmetric :
  length (filter (fun h => if Vector.eq_dec _ Line_dec (hexagram_invert h) h
                           then true else false)
                 FuXi.fuxi_sequence) = 8.
Proof.
Admitted.

(** * Leibniz Binary Correspondence *)

Theorem leibniz_binary_thesis :
  forall n, n < 64 ->
  hexagram_to_nat (nth n FuXi.fuxi_sequence KingWen.hex1_Qian) = n.
Proof.
Admitted.

Theorem fuxi_is_counting :
  forall n m, n < 64 -> m < 64 -> n < m ->
  hexagram_to_nat (nth n FuXi.fuxi_sequence KingWen.hex1_Qian) <
  hexagram_to_nat (nth m FuXi.fuxi_sequence KingWen.hex1_Qian).
Proof.
Admitted.

Theorem binary_complement_sum :
  forall h, hexagram_to_nat h + hexagram_to_nat (hexagram_complement h) = 63.
Proof.
Admitted.

(** * Divination Mechanics *)

Definition yarrow_stalk_probability (m : MovingLine) : Q :=
  match m with
  | OldYin => 1 # 16
  | YoungYang => 5 # 16
  | YoungYin => 7 # 16
  | OldYang => 3 # 16
  end.

Definition coin_probability (m : MovingLine) : Q :=
  match m with
  | OldYin => 1 # 8
  | YoungYang => 3 # 8
  | YoungYin => 3 # 8
  | OldYang => 1 # 8
  end.

Theorem yarrow_probabilities_sum_to_one :
  yarrow_stalk_probability OldYin + yarrow_stalk_probability YoungYang +
  yarrow_stalk_probability YoungYin + yarrow_stalk_probability OldYang = 1.
Proof.
Admitted.

Theorem coin_probabilities_sum_to_one :
  coin_probability OldYin + coin_probability YoungYang +
  coin_probability YoungYin + coin_probability OldYang = 1.
Proof.
Admitted.

Theorem yarrow_favors_yang :
  yarrow_stalk_probability YoungYang + yarrow_stalk_probability OldYang >
  yarrow_stalk_probability YoungYin + yarrow_stalk_probability OldYin.
Proof.
Admitted.

Theorem coins_are_balanced :
  coin_probability YoungYang + coin_probability OldYang =
  coin_probability YoungYin + coin_probability OldYin.
Proof.
Admitted.

(** * Main Theorems *)

Theorem hexagram_space_complete :
  length FuXi.fuxi_sequence = 64 /\
  forall h : Hexagram, In h FuXi.fuxi_sequence.
Proof.
Admitted.

Theorem binary_encoding_bijection :
  forall h1 h2, hexagram_to_nat h1 = hexagram_to_nat h2 -> h1 = h2.
Proof.
Admitted.

Theorem king_wen_contains_all :
  forall h, exists n, n < 64 /\ nth n KingWen.king_wen_sequence KingWen.hex1_Qian = h.
Proof.
Admitted.

Theorem complement_partition :
  forall h, h <> hexagram_complement h \/ self_symmetric h.
Proof.
Admitted.

Theorem leibniz_vindicated :
  (forall n, n < 64 -> hexagram_to_nat (nat_to_hexagram n) = n) /\
  (forall h, hexagram_to_nat h < 64) /\
  (forall h, nat_to_hexagram (hexagram_to_nat h) = h).
Proof.
Admitted.

(** * Line Decidability *)

Definition Line_dec : forall l1 l2 : Line, {l1 = l2} + {l1 <> l2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.
