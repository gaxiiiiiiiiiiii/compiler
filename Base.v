From mathcomp Require Export fintype ssrbool seq choice ssreflect finset.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation "∅" := set0.
Notation "x ∈ X" := (x \in X)(at level 60). 
Notation "A ∩ B" := (setI A B)(at level 40).
Notation "A ∪ B" := (setU A B)(at level 40).
Notation "A ⊂ B" := (A \subset B)(at level 30).
Notation "A // B" := (setD A B)(at level 40).
Notation "¬ A" := (setC A)(at level 40).
Notation "pow[ A ]" := (powerset A).
Notation "∅" := set0.

Lemma extension {T : finType} (A B : {set T}) :
    A ⊂ B -> B ⊂ A -> A = B.
Proof.
    move => AB BA; apply /setP /subset_eqP /andP => //.
Qed.


Lemma set_enum {T : finType} (A : {set T}) :
    [set x | x \in enum A] = A.
Proof.
    by apply/setP => x; rewrite inE mem_enum .
Qed.    

Axiom bigcup : forall {T : finType}, {set {set T}} -> {set T}.
Axiom bigcupP : forall {T : finType} (XX : {set {set T}}) (X : T),
    reflect (exists (Y : {set T}), X ∈ Y /\ Y ∈ XX) (X ∈ bigcup XX).

Axiom bigcap : forall {T : finType}, {set {set T}} -> {set T}.
Axiom bigcapP : forall {T : finType} (XX : {set {set T}}) (X : T),
    reflect (forall (Y : {set T}), Y ∈ XX -> X ∈ Y) (X ∈ bigcup XX).

    