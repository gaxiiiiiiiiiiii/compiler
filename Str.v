
Require Export Base.
From mathcomp Require Import ssrnat eqtype.
Require Wf.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* 各種方の定義 *)
(* symbol     : 記号 *)
(* seq symbol : 文字列 *)
(* Σ          : 文字列の有限集合 *)

Axiom symbol : finType.
Axiom str : seq (seq symbol).

Axiom uniq_str : uniq str.
Axiom mem_str : forall x : seq symbol, x \in str.
Definition str_finMixin := UniqFinMixin uniq_str mem_str. 
Canonical finStr := FinType _ str_finMixin.

Definition Σ := {set finStr}.
Definition ϵ : Σ := [set (nil : finStr)].


(* 文字列の結合を文字列集合へ拡張 *)
(* X ⋅ Y := [x ++ y | x ∈ Y, y ∈ Y] *)

Definition setA (X Y : Σ) : Σ :=
    [set ((x : finStr) ++ (y : finStr) : finStr) | x in X, y in Y].
Notation "X ⋅ Y" := (setA X Y)(at level 50).

Lemma setAP (X Y : Σ) xy: 
    reflect (exists x y, x ∈ X /\ y ∈ Y /\ xy = x ++ y)(xy ∈ X ⋅ Y).
Proof.
    apply (iffP idP).
    +   move /imset2P => [x y Hx Hy Hxy].
        exists x, y => //.
    +   move => [x [y [Hx [Hy Hxy]]]].
        apply /imset2P.
        eapply (Imset2spec Hx Hy) => //.
Qed.


(* クリーネ閉包 *)
(* setK X := ⊔ [X^n | 0 <= n ] *)


Fixpoint setE X n : Σ :=
    match n with
    | O => ϵ 
    | S n' => setE X n' ⋅ X
    end.
Notation "X ^ n" := (setE X n).

Axiom setK : Σ -> Σ.
Notation "X ^*" := (setK X)(at level 30).
Axiom setKP : forall (X : Σ) (x : finStr),
    reflect (exists n, x ∈ X ^ n)(x ∈ X^* ).





(* 各種定理 *)       

Lemma setAA X Y Z :
     X ⋅ (Y ⋅ Z)= (X ⋅ Y) ⋅ Z.
Proof.
    apply extension; apply /subsetP => xyz H.
    +   move /setAP : H => [x [yz [Hx [Hyz H]]]].
        move /setAP : Hyz => [y [z [Hy [Hz Hyz]]]].
        rewrite Hyz in H.
        rewrite catA in H.
        apply /setAP; exists (x ++ y), z; split; [|split] => //.
        apply /setAP; exists x, y; split; [|split] => //.
    +   move /setAP : H => [xy [z [Hxy [Hz Hxyz]]]].
        move /setAP : Hxy => [x [y [Hx [Hy Hxy]]]].
        rewrite Hxy in Hxyz.
        rewrite -catA in Hxyz.
        apply /setAP; exists x, (y ++ z); split; [|split] => //.
        apply /setAP; exists y, z; split; [|split] => //.
Qed.


Lemma setA0l X : ϵ ⋅ X = X.
Proof.
    apply extension; apply /subsetP => x H.
    +   move /setAP : H => [n [x_ [Hn [Hx Hnx]]]].
        move /set1P : Hn => nn.
        rewrite nn in Hnx.
        rewrite cat0s in Hnx; subst => //.
    +   apply /setAP; exists nil, x; repeat split => //.
        apply /set1P => //.
Qed.

Lemma setA0r X : X ⋅ ϵ = X.
Proof.
    apply extension; apply /subsetP => x H.
    +   move /setAP : H => [x_ [n [Hx [Hn Hxn]]]].
        move /set1P : Hn => nn.
        rewrite nn in Hxn.
        rewrite cats0 in Hxn; subst => //.
    +   apply /setAP; exists x, nil; repeat split => //.
        apply /set1P => //.
        rewrite cats0 => //.
Qed.




Goal forall (X : Σ) x xx, x ∈ X -> xx ∈ X^* -> (xx ++ x) ∈ X^*.
Proof.
    move => X x xx Hx /setKP [n Hxx].
    apply /setKP.
    exists (S n) => /=.
    apply /setAP; exists xx, x; repeat split => //.
Qed.    