(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require GHC.Integer.Type.

(* Converted type declarations: *)

Inductive StackOp : Type := SNum : GHC.Integer.Type.Integer -> StackOp
                         |  SPlus : StackOp
                         |  STimes : StackOp.

Inductive Arith : Type := Num : GHC.Integer.Type.Integer -> Arith
                       |  Plus : Arith -> Arith -> Arith
                       |  Times : Arith -> Arith -> Arith.
(* Converted value declarations: *)

Definition compile : list Arith -> list StackOp :=
  fix compile arg_0__
        := match arg_0__ with
             | nil => nil
             | cons (Num n) xs => cons (SNum n) (compile xs)
             | cons (Plus a1 a2) xs => Coq.Init.Datatypes.app (compile (cons a1 nil))
                                                              (Coq.Init.Datatypes.app (compile (cons a2 nil)) (cons
                                                                                      SPlus (compile xs)))
             | cons (Times a1 a2) xs => Coq.Init.Datatypes.app (compile (cons a1 nil))
                                                               (Coq.Init.Datatypes.app (compile (cons a2 nil)) (cons
                                                                                       STimes (compile xs)))
           end.