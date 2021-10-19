From mathcomp Require Export ssrnat eqtype ssrbool.
Require Export Base.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 各種方の定義 *)
(* symbol     : 記号 *)
(* seq symbol : 文字列 *)
(* Σ          : 文字列の有限集合 *)


Section Str.

Parameter symbol : finType.
Parameter base_str : seq (seq symbol).

Axiom uniq_str : uniq base_str.
Axiom mem_str : forall x : seq symbol, x \in base_str.
Definition str_finMixin := UniqFinMixin uniq_str mem_str.
Canonical finStr := FinType (seq symbol) str_finMixin.

Definition Σ := {set finStr}.
Definition ϵ : finStr := nil.

End Str.





Ltac str_ind R := rewrite -(set_enum R); induction (enum R). 
Ltac nil_set0 := rewrite -enum_set0; rewrite (set_enum set0).  




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
    | O => [set ϵ] 
    | S n' => setE X n' ⋅ X
    end.
Notation "X ^ n" := (setE X n).


Axiom setK : Σ -> Σ.
Notation "X ^*" := (setK X)(at level 30).
Axiom setKP : forall (X : Σ) (x : finStr),
    reflect (exists n, x ∈ X ^ n)(x ∈ X^* ).

Notation "X ^+" := (X^* // [set ϵ])(at level 30).    





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


Lemma setAnill X : [set ϵ] ⋅ X = X.
Proof.
    apply extension; apply /subsetP => x H.
    +   move /setAP : H => [n [x_ [Hn [Hx Hnx]]]].
        move /set1P : Hn => nn.
        rewrite nn in Hnx.
        rewrite cat0s in Hnx; subst => //.
    +   apply /setAP; exists nil, x; repeat split => //.
        apply /set1P => //.
Qed.

Lemma setAnilr X : X ⋅ [set ϵ] = X.
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

Lemma setA0l X : ∅ ⋅ X = ∅.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [y [_ [F _]]].
        move : (in_set0 y); rewrite F => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.

Lemma setA0r X : X ⋅ ∅ = ∅.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [_ [y [_ [F _]]]].
        move : (in_set0 y); rewrite F => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.     


Lemma cat1A (x y : finStr) :
    [set x ++ y : finStr] = [set x] ⋅ [set y].
Proof.
    apply extension; apply /subsetP => a.
    move /set1P ->; apply /setAP; exists x, y; 
        repeat split;apply /set1P => //.
    move /setAP => [x0 [y0 [/set1P Hx0 [/set1P Hy0 Ha]]]]; 
        subst; apply /set1P => //.
Qed.

Lemma enum_nil {T : finType}:
    [set x in ([::] : seq T)] = set0.
Proof.
    rewrite -enum_set0 (set_enum set0) => //.
Qed.  

Lemma set0A : 
    ∅ ⋅ ∅ = ∅.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [_ [y [_ [Hy _]]]].
        move : (in_set0 y); rewrite Hy => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.

Lemma set0K : 
    ∅^* = [set ϵ].
Proof.
    apply extension; apply /subsetP => x; first last.
    +   move /set1P ->; apply /setKP; exists 0 => /=; apply /set1P => //.
    +   move /setKP => [n Hn]; move : Hn.
        induction n => //=.
        rewrite setA0r => F; move : (in_set0 x); rewrite F => //.
Qed.  






Goal forall (X : Σ) x xx, x ∈ X -> xx ∈ X^* -> (xx ++ x) ∈ X^*.
Proof.
    move => X x xx Hx /setKP [n Hxx].
    apply /setKP.
    exists (S n) => /=.
    apply /setAP; exists xx, x; repeat split => //.
Qed.    

Lemma setE1 X : X^1 = X.
Proof.
    by simpl; rewrite setAnill.
Qed.



Lemma setEA : forall X n m,
    X^n ⋅ X^m = X^(n + m).
Proof.
Admitted.

Lemma setEE : forall X n m,
    (X^n)^m = X^(n*m).
Proof.
    move => X n; induction n => /=.
    +   elim => [|m Hm] => //=.
        rewrite Hm.
        rewrite setAnilr => //. 
Admitted.




