Require Export Lang Reg.
From mathcomp Require Import finset.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NFA.
Context (L : Lang) (state : finType).








Inductive chars : Type :=
    | char0  
    | char1 of char.


Notation ϵ_ := char0.  

Definition chars2finStr (c : chars) : finStr :=
    match c with
    | char0 => ϵ
    | char1 a => [:: a]
    end.

Coercion chars2finStr : chars >-> Finite.sort.

Definition chars_eqb (a b : chars) := 
    match a, b with
    | char0 , char0 => true
    | char1 a_, char1 b_ => a_ == b_
    | _,_ => false
    end.

Definition chars_eqAxiom : Equality.axiom chars_eqb.
Proof.
    move => x y; destruct x,y => /=; try constructor => //.
    remember (s == s0).
    destruct b; symmetry in Heqb; constructor.
    +   move /eqP : Heqb -> => //.
    +   move => F; inversion F; subst s0.
        rewrite (eq_refl s) in Heqb; inversion Heqb.
Qed.

Definition chars_eqMixin := EqMixin chars_eqAxiom.
Canonical chars_eqType := EqType chars chars_eqMixin.




  
Definition subsetOf {T : finType} (X : {set T}) := {x | x ∈ X}.
Notation  "{ 'sub' X }" := (subsetOf X).




Class nfa := mkNfa{
    Q : {set state};
    p0 : state;
    δ : state -> chars -> {set state};
    F : {set state};
    _ : F ⊂ Q;
    _ : p0 ∈ Q;
}.


Reserved Notation "p -ϵ-> q"(at level 50).
Inductive Closure {N : nfa}: state -> state -> Prop :=
    | CL_refl p : p -ϵ-> p
    | CL_single p q :  q ∈ δ p ϵ_ -> p -ϵ-> q
    | CL_trans p q r : p -ϵ-> q -> q -ϵ-> r ->  p -ϵ-> r
    where "p -ϵ-> q" := (Closure p q).




Axiom closure : forall {N : nfa}, {set state} -> {set state}.
Axiom closureP : forall (N : nfa) (P : {set state}) q,
    reflect (exists p, p ∈ P /\ p -ϵ-> q) (q ∈ closure P).


Fixpoint δ' {N : nfa}  (p : state) (s : finStr) : {set state} :=
    match s with
    | [::] => closure [set p]
    | a :: w => closure (\bigcup_(x in  δ' p w) (δ x (char1 a)))
    (* closure (bigcup [set δ x (char1 a) | x in δ' p w])    *)
    end.


        

Definition LangOf (N : nfa) := 
    [set w : finStr | ~~ ((δ' p0 w ∩ F) == ∅)].



Variable p q : state.
Definition dQ := [set p; q].
Definition dF := [set q].
Hypotheses npq : p <> q.

Lemma dFQ : dF ⊂ dQ.
Proof.
    apply /subsetP => x /set1P H; subst; apply /set2P; right => //.
Qed. 

Lemma pQ : p ∈ dQ.
Proof.
    apply /set2P; left => //.
Qed.



Lemma nfa0 : exists N, LangOf N = ∅.
Proof.
    pose N := (mkNfa dQ p (fun _ _ => ∅) ∅ (sub0set dQ) pQ).
    exists N.
    rewrite /LangOf.
    apply extension; apply /subsetP => x. 
    -   rewrite in_set setI0 => /=.
        move /eqP => F.
        contradiction F => //.
    -   move : (in_set0 x) -> => //.
Qed. 



Lemma nfae : exists N, LangOf N = [set ϵ].
Proof.
    pose f := fun (s : state) (c : chars)=> if (c == ϵ_) && (s == p) then [set q] else ∅.
    pose N := (mkNfa dQ p f dF dFQ pQ).
    exists N.
    rewrite /LangOf.
    apply extension; apply /subsetP => w.        
    -   rewrite in_set => /=.
        move /set0Pn => [x /setIP [Hx /set1P H1]]; subst x.
        move : q Hx; induction w => q0 Hx.
        *   apply /set1P => //. 
        *   move /(closureP N _ q0) : Hx => [p0 [Hp pq0]].
            move /bigcupP : Hp => [s Hs Hp].
            rewrite /δ /N /f /= in Hp.
            rewrite (in_set0 p0) in Hp; inversion Hp.
        -  move /set1P ->.
        rewrite in_set.
        apply /eqP => /= F.
        have : (q ∈ ∅).
            rewrite -F.
            apply /setIP; split.
            *   apply /closureP.
                exists p; split.
                apply /set1P => //.
                apply CL_single => /=.
                rewrite /f => /=.
                rewrite eq_refl.
                apply /set1P => //.
            *   apply /set1P => //.
        rewrite (in_set0 q) => //.  
Qed. 

Lemma nfa1 a : exists N, LangOf N = [set [::a]].
Proof.
    pose f := fun (s : state) (c : chars)=> if (c == char1 a ) && (s == p) then [set q] else ∅.
    pose N := (mkNfa dQ p f dF dFQ pQ).
    have F0 : forall r, r ∈ dQ -> ~ exists s, r <> s /\ r -ϵ-> s.        
        move => r H [s [nrs sr]].
        case /set2P : H => r_; subst.
        +   induction sr.
            -   contradiction nrs => //.
            -   rewrite (in_set0 q0) in H; inversion H.
            -   remember (p1 == q0); symmetry in Heqb.
                destruct b; move /eqP : Heqb => H; subst.
                *   remember (q0 == r); symmetry in Heqb.
                    destruct b; move /eqP : Heqb => H; subst.
                    +   contradiction nrs => //.
                    +   apply IHsr2 => //.
                *   apply IHsr1 => //.
        +   induction sr.
            -   contradiction nrs => //.
            -   rewrite (in_set0 q0) in H; inversion H.
            -   remember (p1 == q0); symmetry in Heqb.
                destruct b; move /eqP : Heqb => H; subst.
                *   remember (q0 == r); symmetry in Heqb.
                    destruct b; move /eqP : Heqb => H; subst.
                    +   contradiction nrs => //.
                    +   apply IHsr2 => //.
                *   apply IHsr1 => //.
    exists N.
    rewrite /LangOf.
    apply extension; apply /subsetP => w; first last.
    -   move /set1P ->.
        rewrite in_set => /=.
        apply /eqP => F.
        have : (q ∈ ∅).
            rewrite -F.
            apply /setIP; split; first last.
            *   apply /set1P => //.
            *   apply /closureP.
                exists q; split.
                +   apply /bigcupP.
                    exists p.
                    -   apply /closureP.
                        exists p; split; [apply /set1P => //|constructor].
                    -   rewrite /f; rewrite !eq_refl => /=; apply /set1P => //.           
                +   constructor.
        rewrite (in_set0 q) => //.
    -   rewrite in_set => /=; rewrite /dF.
        move /set0Pn => [p0 /setIP [Hp /set1P pF]]; subst p0.
        induction w.
        *   move /closureP : Hp => [p1 [/set1P H1 pq]]; subst p1; simpl in pq.
            contradiction (F0 p pQ).
            exists q => //.           
        *   move /closureP : Hp => [s [Hs sq]].
            move /bigcupP : Hs => [r Hr Hs].
            destruct w.
            +   remember (a == a0); symmetry in Heqb.
                destruct b; move /eqP in Heqb.
                -   subst a0; apply /set1P => //.
                -   rewrite /δ /N /f in Hs.
                    suff F : char1 a0 == char1 a = false.
                        rewrite F /= in Hs.
                        rewrite (in_set0 s) in Hs; inversion Hs.
                    apply /eqP => F; inversion F.
                    contradiction Heqb => //.
            +   rewrite /δ /N /f in Hs.
                move /closureP : Hr => [t[Ht tr]].
                move /bigcupP : Ht => [u Hu Ht].
                rewrite /δ /N /f in Ht.
                admit.
Admitted.             



Theorem reg_nfa :
    forall l , Reg l -> exists N : nfa, LangOf N = l.
Proof.
    move => l Hl; induction Hl.
    +   apply nfa0.        
    +   apply nfae.    
    +   apply nfa1.
    +   admit.
    +   admit.
    +   admit.
Admitted.    
 



