Require Import Bvector ZArith Zdigits.
Require Vector.

Set Implicit Arguments.
Set Strict Implicit.

Arguments binary_value [n] _.
Arguments two_compl_value [n] _.

Definition testbit {n} (v : Bvector n) (i : Z) : bool :=
  Z.testbit (binary_value v) i.

Definition setbit {n} (v : Bvector n) (i : Z) : (Bvector n) :=
  Z_to_binary n (Z.setbit (binary_value v) i).

Definition clearbit {n} (v : Bvector n) (i : Z) : (Bvector n) :=
  Z_to_binary n (Z.clearbit (binary_value v) i).

Definition msb {n} (v : Bvector (S n)) : bool :=
  testbit v (Z.of_nat n).

Definition zero n := Z_to_binary n 0.

Definition one n := Z_to_binary n 1.

Definition ones n := Z_to_binary n (-1).

Definition add {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.add (binary_value a) (binary_value b)).

Definition sub {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.sub (binary_value a) (binary_value b)).

Definition opp {n} (v : Bvector n) : Bvector n :=
  Z_to_binary n (Z.opp (binary_value v)).

Definition mul {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.mul (binary_value a) (binary_value b)).

Definition neg {n} (a : Bvector n) : Bvector n :=
  Z_to_binary n (Z.opp (binary_value a)).

Definition udiv {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.div (binary_value a) (binary_value b)).

Definition udiv_rem {n} (a b: Bvector n) : (Bvector n * Bvector n) :=
  match Z.div_eucl (binary_value a) (binary_value b) with
    | (quotient, remainder) => (Z_to_binary _ quotient, Z_to_binary _ remainder)
  end.

Definition sdiv {n} (a b : Bvector (S n)) : Bvector (S n) :=
  Z_to_two_compl n (Z.quot (two_compl_value a) (two_compl_value b)).

Definition lnot {n} (v : Bvector n) : Bvector n :=
  Z_to_binary n (Z.lnot (binary_value v)).

Definition lor {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.lor (binary_value a) (binary_value b)).

Definition land {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.land (binary_value a) (binary_value b)).

Definition lxor {n} (a b : Bvector n) : Bvector n :=
  Z_to_binary n (Z.lxor (binary_value a) (binary_value b)).

Definition shl {n} (v : Bvector n) (i : Z) : Bvector n :=
  Z_to_binary n (Z.shiftl (binary_value v) i).

Definition lshr {n} (v : Bvector n) (i : Z) : Bvector n :=
  Z_to_binary n (Z.shiftr (binary_value v) i).

Definition ashr {n} (v : Bvector (S n)) (i : Z) : Bvector (S n) :=
  Z_to_two_compl n (Z.shiftr (two_compl_value v) i).

Definition blt {n} (v1 v2: Bvector n) : Prop :=
  Zlt (binary_value v1) (binary_value v2).

Definition sblt {n} (v1 v2: Bvector (S n)) : Prop :=
  Zlt (two_compl_value v1) (two_compl_value v2).

Definition ble {n} (v1 v2: Bvector n) : Prop :=
  Zle (binary_value v1) (binary_value v2).

Definition sble {n} (v1 v2: Bvector (S n)) : Prop :=
  Zle (two_compl_value v1) (two_compl_value v2).

Definition bgt {n} (v1 v2: Bvector n) : Prop :=
  Zgt (binary_value v1) (binary_value v2).

Definition sbgt {n} (v1 v2: Bvector (S n)) : Prop :=
  Zgt (two_compl_value v1) (two_compl_value v2).

Definition bge {n} (v1 v2: Bvector n) : Prop :=
  Zge (binary_value v1) (binary_value v2).

Definition sbge {n} (v1 v2: Bvector (S n)) : Prop :=
  Zge (two_compl_value v1) (two_compl_value v2).

Definition zero_cast m {n} (v : Bvector n) : Bvector m :=
  Z_to_binary m (binary_value v).

Definition sign_cast m {n} (v : Bvector (S n)) : Bvector m :=
  Z_to_binary m (two_compl_value v).

Definition trunc p {n} (v : Bvector n) : Bvector (n - p) :=
  zero_cast (n - p) v.

Definition extract hi lo {n} (v : Bvector n) : Bvector (S (hi - lo)) :=
  zero_cast (S (hi - lo)) (lshr v (Z.of_nat lo)).

Definition append {n m} (v1 : Bvector n) (v2 : Bvector m) : Bvector (n + m) :=
  lor (zero_cast (n + m) v1) (shl (zero_cast (n + m) v2) (Z.of_nat n)).

Definition zero_extend p {n} (v : Bvector n) : Bvector (n + p) :=
  zero_cast (n + p) v.

Definition sign_extend p {n} (v : Bvector (S n)) :=
  sign_cast (S (n + p)) v.

Fixpoint repeat {n : nat} (m : nat) (xs : Bvector n) : Bvector (m * n) :=
  match m with
    | O => Bnil
    | S m' => append xs (repeat m' xs)
  end.

Delimit Scope B_scope with B.

Infix "+" := (@add _) : B_scope.
Infix "*" := (@mul _) : B_scope.
Infix "-" := (@sub _) : B_scope.
Infix "<" := (@blt _) : B_scope.
Infix "<=" := (@ble _) : B_scope.
Infix ">" := (@bgt _) : B_scope.
Infix ">=" := (@bge _) : B_scope.
Notation "- x" := (opp x) : B_scope.
