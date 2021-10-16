Require Export Str.
From mathcomp Require Export eqtype ssrnat.



Inductive Reg : Σ -> Prop :=
    | set0reg : Reg ∅
    | emptyreg_ : Reg [set nil : finStr]
    | set1reg (a : symbol) :  Reg [set ([:: a] : finStr)]   
    | setUreg X Y : Reg X -> Reg Y -> Reg (X ∪ Y)
    | setAreg X Y : Reg X -> Reg Y -> Reg (X ⋅ Y)
    | setKreg X : Reg X -> Reg (X ^*).


Lemma cat1A (x y : finStr) :
    [set x ++ y : finStr] = [set x] ⋅ [set y].
Proof.
    apply extension; apply /subsetP => a.
    move /set1P ->; apply /setAP; exists x, y; 
        repeat split;apply /set1P => //.
    move /setAP => [x0 [y0 [/set1P Hx0 [/set1P Hy0 Ha]]]]; 
        subst; apply /set1P => //.
Qed.        



Lemma reg1 a : Reg [set a].
Proof.
    induction a; first constructor.
    suff : a :: a0 = [::a] ++ a0.
        move ->.
        rewrite cat1A; constructor => //; constructor.
    induction a0 => //.
Qed.    


Lemma setDreg (R S : Σ) :
    Reg R -> Reg S -> Reg (R // S).
Proof.
    move => HR HS; move : S HS.
    rewrite -(set_enum R).
    induction (enum R) => S HS.    
    +   rewrite -enum_set0.
        rewrite (set_enum ∅).
        rewrite set0D; constructor.
    +   rewrite set_cons setDUl; constructor.
        -   Search set1 setD.
            remember (a ∈ S).
            destruct b.
            *   suff : [set a] // S = ∅.
                    move ->; constructor.
                apply extension; apply /subsetP => x.
                +   case /setDP.
                    move /set1P ->.
                    rewrite -Heqb => //.
                +   rewrite (in_set0) => //.
            *   have : [set a] // S = [set a].
                    apply extension; apply /subsetP => b.
                    +   case /setDP; move /set1P -> => _; apply /set1P => //.
                    +   move /set1P ->; apply /setDP; split.
                        -   apply /set1P => //.
                        -   rewrite -Heqb => //.
                move ->; apply reg1.
        -   apply IHl => //.
Qed.              

Lemma setIreg : forall R S,
    Reg R -> Reg S -> Reg (R ∩ S).
Proof.
    move => R S HR HS; move : S HS.
    rewrite -(set_enum R).
    induction (enum R) => S HS.
    +   rewrite -enum_set0.
        rewrite (set_enum ∅).
        rewrite set0I; constructor.
    +   rewrite set_cons setIUl; constructor; first last.
        apply IHl => //.
        remember (a ∈ S).
        destruct b.
        -   suff : [set a] ∩ S = [set a].
                move ->; apply reg1.
            apply extension; apply /subsetP => x.
            *   case /setIP => //.
            *   move /set1P ->; apply /setIP; split => //; apply /set1P => //.
        -   suff : [set a] ∩ S = ∅.
                move ->; constructor.
            apply extension; apply /subsetP => x.
            *   case /setIP; move /set1P ->; rewrite -Heqb => //.
            *   rewrite (in_set0 x) => //.
Qed.

Lemma setTreg : Reg setT.
Proof.
    rewrite -(set_enum setT).
    induction (enum setT).
    +   rewrite -enum_set0.
        rewrite (set_enum ∅).
        constructor.
    +   rewrite set_cons; constructor => //.
        apply reg1.
Qed.   

Lemma setTDreg R : Reg R -> Reg (setT // R).
Proof.
    move => H; apply setDreg => //; apply setTreg.
Qed.

Lemma setCreg R : Reg R -> Reg (¬ R).
Proof.
    rewrite -setTD; apply setTDreg.
Qed.

Lemma setEreg R n :  Reg R -> Reg (R^n).
Proof.
    induction n => /= H.
    +   apply reg1.
    +   constructor => //; apply IHn => //.
Qed.

Lemma setK'reg R : Reg R -> Reg (R^+).
Proof.
    move => H.
    apply setDreg.
    +   by apply setKreg.
    +   by apply reg1.
Qed.    

    




    





    






  

   