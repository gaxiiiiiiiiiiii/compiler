
Require Export Lang Reg.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NFA.
Context (L : Lang) (state : finType).


hogehoge



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
    | CL_single p q : q ∈ δ p ϵ_ -> p -ϵ-> q
    | CL_trans p q r : p -ϵ-> q -> q -ϵ-> r ->  p -ϵ-> r
    where "p -ϵ-> q" := (Closure p q).



Axiom closure : forall {N : nfa}, {set state} -> {set state}.
Axiom closureP : forall (N : nfa) (P : {set state}) q,
    reflect (exists p, p ∈ P /\ p -ϵ-> q) (q ∈ closure P).


Fixpoint δ' {N : nfa}  (p : state) (s : finStr) : {set state} :=
    match s with
    | [::] => closure [set p]
    | a :: w => closure (bigcup [set δ x (char1 a) | x in δ' p w])   
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



Theorem reg_nfa :
    forall l , Reg l -> exists N : nfa, LangOf N = l.
Proof.
    move => l Hl; induction Hl.
    +   pose N := (mkNfa dQ p (fun _ _ => ∅) ∅ (sub0set dQ) pQ).
        exists N.
        rewrite /LangOf.
        apply extension; apply /subsetP => x. 
        -   rewrite in_set setI0 => /=.
            move /eqP => F.
            contradiction F => //.
        -   move : (in_set0 x) -> => //.
    +   pose f := fun (s : state) (c : chars)=> if (c == ϵ_) && (s == p) then [set q] else ∅.
        pose N := (mkNfa dQ p f dF dFQ pQ).
        exists N.
        rewrite /LangOf.
        apply extension; apply /subsetP => w.        
        -   rewrite in_set => /=.
            move /set0Pn => [x /setIP [Hx /set1P H1]]; subst x.
            move : q Hx; induction w => q0 Hx.
            *   apply /set1P => //. 
            *   move /(closureP N _ q0) : Hx => [p0 [Hp pq0]].
                move /bigcupP : Hp => /= [Y [pY HY]].
                move /imsetP : HY => [x Hx Yf]; subst Y.
                rewrite /f in pY.
                simpl in pY.
                rewrite (in_set0 p0) in pY; inversion pY.
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
    +   pose f := fun (s : state) (c : chars)=> if (c == char1 a ) && (s == p) then [set q] else ∅.
        pose N := (mkNfa dQ p f dF dFQ pQ).
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
                        exists [set q]; split.
                        -   apply /set1P => //.
                        -   apply /imsetP.
                            exists p.
                            *   apply /closureP.
                                exists p; split.
                                +   apply /set1P => //.
                                +   constructor.
                            *   rewrite /f.
                                rewrite !eq_refl => /=.
                                by [].
                    +   constructor.
            rewrite (in_set0 q) => //.
        -   rewrite in_set => /=; rewrite /dF.
            Search setI set0.
            move /set0Pn => [p0 /setIP [Hp /set1P pF]]; subst p0.
            induction w.
            *   move /closureP : Hp => [p1 [/set1P H1 pq]]; subst p1; simpl in pq.

                +   case  (npq H0).
                +   rewrite /δ /N /f /= in H.
                    rewrite (in_set0 q) in H; inversion H.
                +   subst.
                admit.
            *   admit. *)
    +   move : IHHl1 => [NX HX].
        move : IHHl2 => [NY HY].
        inversion NX as [Qx px fx Fx Hx].
        inversion NY as [Qy py fy Fy Hy].
        pose f := fun s c => fx s c ∪ fy s c.
        pose N := mkNfa state (Qx ∪ Qy) px f (Fx ∪ Fy) (setUSS Hx Hy).
        exists N.
        rewrite /LangOf.
        apply extension; apply /subsetP => z.
        -   rewrite in_set.
            move /set0Pn => [xy /setIP [Hxy /setUP bF]].
            induction z.
            *   move /closureP : Hxy => [p_ [/set1P pp Hp]]; subst p_; simpl in Hp.



 



