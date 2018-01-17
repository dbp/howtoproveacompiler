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
Require Data.Either.
Require GHC.Num.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive StackOp : Type := SNum : GHC.Num.Int -> StackOp
                         |  SPlus : StackOp
                         |  STimes : StackOp.

Inductive Arith : Type := Num : GHC.Num.Int -> Arith
                       |  Plus : Arith -> Arith -> Arith
                       |  Times : Arith -> Arith -> Arith.
(* Converted value declarations: *)

(* Translating `instance GHC.Show.Show Compiler.StackOp' failed: OOPS! Cannot
   find information for class Qualified "GHC.Show" "Show" unsupported *)

Definition compile : Arith -> list StackOp :=
  fix compile arg_0__
        := match arg_0__ with
             | Num n => cons (SNum n) nil
             | Plus a1 a2 => Coq.Init.Datatypes.app (compile a1) (Coq.Init.Datatypes.app
                                                    (compile a2) (cons SPlus nil))
             | Times a1 a2 => Coq.Init.Datatypes.app (compile a1) (Coq.Init.Datatypes.app
                                                     (compile a2) (cons STimes nil))
           end.

Definition eval : list GHC.Num.Int -> list StackOp -> Data.Either.Either (list
                                                                         GHC.Num.Int * list StackOp)%type GHC.Num.Int :=
  fix eval arg_0__ arg_1__
        := match arg_0__ , arg_1__ with
             | cons n _ , nil => Data.Either.Right n
             | ns , cons (SNum n) xs => eval (cons n ns) xs
             | cons n2 (cons n1 ns) , cons SPlus xs => eval (cons (n1 GHC.Num.+ n2) ns) xs
             | cons n2 (cons n1 ns) , cons STimes xs => eval (cons (n1 GHC.Num.* n2) ns) xs
             | vals , instrs => Data.Either.Left (pair vals instrs)
           end.

Definition eval' : Arith -> GHC.Num.Int :=
  fix eval' arg_0__
        := match arg_0__ with
             | Num n => n
             | Plus a1 a2 => (eval' a1) GHC.Num.+ (eval' a2)
             | Times a1 a2 => (eval' a1) GHC.Num.* (eval' a2)
           end.

(* Unbound variables:
     cons list nil op_zt__ pair Coq.Init.Datatypes.app Data.Either.Either
     Data.Either.Left Data.Either.Right GHC.Num.Int GHC.Num.op_zp__ GHC.Num.op_zt__
*)
