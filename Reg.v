Require Export Str.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Inductive Reg {finStr : str}{lo : lang_op finStr}{Σ : lang}: Σ -> Prop :=
    | reg0 : Reg ∅
    | regnil : Reg [set nil : finStr]
    | rega (a : char) :  Reg [set ([:: a] : finStr)]   
    | regU X Y : Reg X -> Reg Y -> Reg (X ∪ Y)
    | regA X Y : Reg X -> Reg Y -> Reg (X ⋅ Y)
    | regK X : Reg X -> Reg (X ^*).
    

Record reg {finStr : str}{lo : lang_op finStr}: Type := mkReg {
    L :> lang;
    axiom : forall str : L, Reg str
}.
Coercion Lang {finStr : str} {lo : lang_op finStr} (r : @reg finStr lo) := {set finStr}.



Section Properties.

Context (finStr : str) (lo : lang_op finStr) (Σ : lang).




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


Lemma regI : forall (R S : Σ),
    Reg R -> Reg S -> Reg (R ∩ S).
Proof.
    move => R S HR HS.
    move : S HS => /=.
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




Lemma regD (R S : Σ) :
    Reg R -> Reg S -> Reg (R // S).
Proof.
    move => HR HS; move : S HS.
    rewrite -(set_enum R).
    induction (enum R) => S HS.    
    +   rewrite -enum_set0.
        rewrite (set_enum ∅).
        rewrite set0D; constructor.
    +   rewrite set_cons setDUl; constructor.
        -   remember (a ∈ S).
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


Lemma regT : Reg setT.
Proof.
    rewrite -(set_enum setT).
    induction (enum setT).
    +   rewrite -enum_set0.
        rewrite (set_enum ∅).
        constructor.
    +   rewrite set_cons; constructor => //.
        apply reg1.
Qed.   

Lemma regTD R : Reg R -> Reg (setT // R).
Proof.
    move => H; apply regD => //; apply regT.
Qed.

Lemma regC R : Reg R -> Reg (¬ R).
Proof.
    rewrite -setTD; apply regTD.
Qed.


Lemma regE R n :  Reg R -> Reg (R^n).
Proof.
    induction n => /= H.
    +   rewrite setE0; apply reg1.
    +   rewrite -addn1.
        rewrite setES.        
        constructor => //; apply IHn => //.
Qed.

(* Lemma regK' R : Reg R -> Reg (R^+).
Proof.
    move => H.
    apply regD.
    +   by apply regK.
    +   by apply reg1.
Qed. *)














    




    





    






  

   