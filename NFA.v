
Require Export Str.



Section NFA.


Record sym : Type := mkSym {
    symb :> finStr;
    _ : symb ∈ ([set [::x]| x in [set : symbol]] ∪ [set ϵ]);
}.



Definition ϵ_ : sym.
    apply (mkSym nil).
    rewrite inE; apply /orP; right.
    rewrite inE => //.
Qed.

Definition toSym (a : symbol) : sym.
Proof.
    apply (mkSym [:: a]).
    rewrite inE; apply /orP; left.
    apply /imsetP; exists a => //.
Qed.


Variable state : finType.
Variables Q F : {set state}.
Hypotheses FQ : F ⊂ Q.
Variable p0 : state.
Hypotheses pQ : p0 ∈ Q.
Variable δ : state -> sym ->  {set state}.






Reserved Notation "p -ϵ-> q"(at level 50).
Inductive Closure : state -> state -> Prop :=
    | CL_refl p : p -ϵ-> p
    | CL_single p q : q ∈ δ p ϵ_ -> p -ϵ-> q
    | CL_trans p q r : p -ϵ-> q -> q -ϵ-> r ->  p -ϵ-> r
    where "p -ϵ-> q" := (Closure p q).

Axiom closure : {set state} -> {set state}.
Axiom closureP : forall (P : {set state}) q,
    reflect (forall p, p ∈ P -> p -ϵ-> q) (q ∈ closure P).





Fixpoint δ' (p : state) (s : finStr) : {set state} :=
    match s with
    | [::] => closure [set p]
    | a :: w => closure (bigcup [set δ x (toSym a) | x in δ' p w])
    end.

Definition L := [set w : finStr | (δ' p0 w ∩ F) == ∅].


End NFA.

 



