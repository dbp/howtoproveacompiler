Require Import LiterateCoq.Tactics.
Require Import Compiler.
Require Import ZArith.


Lemma list_pointless_split : forall A B:Type, forall l : list A, forall x : B,
        match l with | nil => x | (_ :: _)%list => x end = x.
Proof.
  destruct l; eauto.
Qed.
Lemma list_pointless_split' : forall A B:Type, forall l : list A, forall x : B,
        match l with | nil => x | (_ :: nil)%list => x | (_ :: _ :: _)%list => x end = x.
Proof.
  destruct l; intros; eauto. destruct l; eauto.
Qed.


Lemma eval_step : forall a : Arith, forall s : list Num.Int, forall xs : list StackOp, 
        eval s (compile a ++ xs) = eval (eval' a :: s) xs.
Proof.
  hint_rewrite List.app_assoc_reverse.
  hint_rewrite list_pointless_split, list_pointless_split'.
  
  induction a; intros; simpl; iauto;

    hint_rewrite IHa1, IHa2; iauto'.
Qed.

Lemma compiler_correctness' : forall a : Arith, forall s : list Num.Int, 
      eval s (compile a) = Data.Either.Right (eval' a).
Proof.
  hint_rewrite eval_step.
  hint_rewrite list_pointless_split, list_pointless_split'.
  
  induction a; intros; simpl; hint_simpl; iauto'.
Qed.  
  

Theorem compiler_correctness : forall a : Arith, eval nil (compile a) = Data.Either.Right (eval' a).
Proof.
  hint compiler_correctness'.
  intros; iauto.
Qed.
