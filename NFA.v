
Require Export Str Reg.





Record chars {finStr : str}: Type := mkChar {
    c :> finStr;
    _ : c ∈ ([set [::x]| x in [set : char]] ∪ [set ϵ]);
}.



Definition ϵ_ {finStr : str}: chars.
    apply (mkChar _ ϵ).
    rewrite inE; apply /orP; right.
    rewrite inE => //.
Qed.

Definition charOf {finStr : str} (a : char) : chars.
Proof.
    apply (mkChar _ [:: a]).
    rewrite inE; apply /orP; left.
    apply /imsetP; exists a => //.
Qed.

Class nfa {finStr : str} : Type := mkNFA {
    state : finType;
    Q : {set state};
    F : {set state};
    p0 : state;
    δ : state -> chars -> {set state}
}.




Reserved Notation "p -ϵ-> q"(at level 50).
Inductive Closure {finStr : str} {N : nfa}: state -> state -> Prop :=
    | CL_refl p : p -ϵ-> p
    | CL_single p q : q ∈ δ p ϵ_ -> p -ϵ-> q
    | CL_trans p q r : p -ϵ-> q -> q -ϵ-> r ->  p -ϵ-> r
    where "p -ϵ-> q" := (Closure p q).

Axiom closure : forall {finStr : str} {N : nfa}, {set state} -> {set state}.
Axiom closureP : forall {finStr : str} {N : nfa} (P : {set state}) q,
    reflect (forall p, p ∈ P -> p -ϵ-> q) (q ∈ closure P).


Fixpoint δ' {finStr : str} {N : nfa} (p : state) (s : finStr) : {set state} :=
    match s with
    | [::] => closure [set p]
    | a :: w => closure (bigcup [set δ x (charOf a) | x in δ' p w])
    end.

Definition L {finStr : str} (N : nfa) := [set w : finStr | (δ' p0 w ∩ F) == ∅].




Section Properties.

Context (finStr : str) (lo : lang_op finStr)(Σ : lang).

Theorem reg_nfa :
    forall l : Σ, Reg l -> exists N : nfa, L N = l.
Proof.
Admitted.



 



