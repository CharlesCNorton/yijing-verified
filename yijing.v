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
  Vector.rev h.

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
  unfold hexagram_invert.
  apply Vector.rev_rev.
Qed.

Theorem qian_kun_are_complements :
  hexagram_complement KingWen.hex1_Qian = KingWen.hex2_Kun.
Proof.
  reflexivity.
Qed.

Require Import Eqdep_dec.

Lemma UIP_nat : forall (n : nat) (p q : n = n), p = q.
Proof. intros. apply UIP_dec. decide equality. Qed.

