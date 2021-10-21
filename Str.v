From mathcomp Require Export ssrnat eqtype ssrbool.
Require Export Base.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Module Str.

Record str: Type := mkStr {
    char_ : finType;
    base : seq (seq char_);
    uniq_str : uniq base;
    total_str : forall x : seq char_, x \in base;
}.


Coercion FinStr (string : str) :=
    FinType (seq (char_ string)) (UniqFinMixin (uniq_str  string) (total_str  string)).

Canonical FinStr.


End Str.


Module Lang.
Export Str.



Record lang : Type := mkLang {
    finStr_ : str;
    setA_ : {set finStr_} -> {set finStr_} -> {set finStr_};
    setE_ : {set finStr_} -> nat -> {set finStr_};
    setK_ : {set finStr_} -> {set finStr_};
    setAP_ : forall (X Y : {set finStr_}) xy,
            reflect (exists x y, x ∈ X /\ y ∈ Y /\ xy = x ++ y)(xy ∈ setA_ X Y);
    setEP_ : forall (X : {set finStr_}) n xx,
            reflect 
                (match n with 
                    | O => xx == [::]
                    | S n' => xx ∈ setA_ (setE_ X n') X
                end)
                (xx ∈ setE_ X n);
    setKP_ : forall (X : {set finStr_}) xx,
            reflect (exists n, xx ∈ setE_ X n)(xx ∈ setK_ X)

}.

Coercion Lang (Σ : lang) := {set (finStr_ Σ)}.
Notation finStr := (finStr_ _).
Notation char := (char_ finStr).
Notation "X ⋅ Y" := (setA_ _ X Y)(at level 30).
Notation "X ^ n" := (setE_ _ X n).
Notation "X ^*"  := (setK_ _ X)(at level 30).
Notation setAP := (setAP_ _).
Notation setEP := (setEP_ _).
Notation setKP := (setKP_ _).
Notation ϵ := ([::] : finStr).




End Lang.




Section Properties.
Import Lang.

Variable Σ : lang.


Lemma setAA (X Y Z : Σ):
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


Lemma setAnill (X : Σ) : 
    [set ϵ] ⋅ X = X.
Proof.
    apply extension; apply /subsetP => x H.
    +   move /setAP : H => [n [x_ [Hn [Hx Hnx]]]].
        move /set1P : Hn => nn.
        rewrite nn in Hnx.
        rewrite cat0s in Hnx; subst => //.
    +   apply /setAP; exists nil, x; repeat split => //.
        apply /set1P => //.
Qed.

Lemma setAnilr (X : Σ) : 
    X ⋅ [set ϵ] = X.
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

Lemma setA0l (X : Σ) :
    ∅ ⋅ X = ∅.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [y [_ [F _]]].
        move : (in_set0 y); rewrite F => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.

Lemma setA0r (X : Σ) : 
    X ⋅ ∅ = ∅.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [_ [y [_ [F _]]]].
        move : (in_set0 y); rewrite F => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.     


(* Lemma cat1A (x y : (@finStr Σ)) :
    [set x ++ y : finStr] = [set x] ⋅ [set y].
Proof.
    apply extension; apply /subsetP => a.
    move /set1P ->; apply /setAP; exists x, y; 
        repeat split;apply /set1P => //.
    move /setAP => [x0 [y0 [/set1P Hx0 [/set1P Hy0 Ha]]]]; 
        subst; apply /set1P => //.
Qed. *)

Lemma enum_nil {T : finType}:
    [set x in ([::] : seq T)] = set0.
Proof.
    rewrite -enum_set0 (set_enum set0) => //.
Qed.  

Lemma set0A : 
    ∅ ⋅ ∅ = (∅ : Σ).
Proof.
    apply extension; apply /subsetP => x.
    +   move /setAP => [_ [y [_ [Hy _]]]].
        move : (in_set0 y); rewrite Hy => //.
    +   move => F; move : (in_set0 x); rewrite F => //.
Qed.



Lemma set0K : 
    (∅ : Σ)^* = [set ϵ].
Proof.
    apply extension; apply /subsetP => x; first last.
    +   move /set1P ->; apply /setKP; exists 0; apply /setEP => //.
    +   move /setKP => [n Hn]; move : Hn.
        induction n => /=.
        -   move /setEP /eqP ->; apply /set1P => //.
        -   move /setEP /setAP => [a [b [Ha [Hb H]]]].
            move : (in_set0 b); rewrite Hb=> //.
Qed.  






Goal forall (X : Σ) x xx, x ∈ X -> xx ∈ X^* -> (xx ++ x) ∈ X^*.
Proof.
    move => X x xx Hx /setKP [n Hxx].
    apply /setKP.
    exists (S n) => /=.
    apply /setEP.
    apply /setAP; exists xx, x; repeat split => //.
Qed.    

Lemma setE1 (X : Σ) : 
    X^1 = X.
Proof.
    apply extension; apply /subsetP => x.
    +   move /setEP /setAP => [n [x_ [Hn [Hx_ Hnx]]]].
        move /setEP : Hn; move /eqP => nn; subst => //.
    +   move => H; apply /setEP /setAP.
        exists ϵ, x; repeat split => //.
        apply /setEP => //.
Qed.



Lemma setEA : forall (X : Σ) n m,
    (X^n) ⋅ (X^m) = X^(n + m).
Proof.
Admitted.

Lemma setEE : forall (X : Σ) n m,
    (X^n)^m = X^(n*m).
Proof.
Admitted.

End Properties.




