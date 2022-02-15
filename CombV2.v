(* Combinational.v

   # Contents

   1. Relations as Semantic Domain Model
   2. ...

   # Explanation of Basic Idea

   First, we will provide a bunch of definitions
   for relations, as well as a notion of equivalence
   between two similarly typed relations.

   Relations will serve as the objects our
   circuits denote, and <=> as the equivalence
   between those objects.  Thus we will define
   equivalence of circuits.
 *)

(* **********************************************************
    Syntax Definition for Combinational Circuits
 ********************************************************** *)

Section CircuitSyntax.
  (* relying on Adam Chlipala's PHOAS notes here *)

  Inductive WType : Set :=
    | wUnit   : WType
    | wBit    : WType
    | wPair   : WType -> WType -> WType
    .

  Variable var : WType -> Type.

  (*
     Below is the desired raw code for an SR latch
     We can probably even improve on the whole Fst Snd thing,
     But let's get the basics down first.

  (cFun (wPair wBit wBit) (fun SR =>
      (cWire wBit (fun Qn =>
      (cBind (gFst SR) (fun S =>
      (cBind (gSnd SR) (fun R =>
      (cBind (gNand S Qn) (fun Q =>
      (cEqn  (gNand Q R) Qn
      (cReturn Q)
     )))))))))))
   *)

  Inductive Gate : WType -> Type :=
    | gtt   : Gate wUnit
    | g0    : Gate wBit
    | g1    : Gate wBit
    | gNot  : (var wBit) -> Gate wBit
    | gAnd  : (var wBit) -> (var wBit) -> Gate wBit
    | gOr   : (var wBit) -> (var wBit) -> Gate wBit
    | gNand : (var wBit) -> (var wBit) -> Gate wBit
    | gNor  : (var wBit) -> (var wBit) -> Gate wBit
    | gFst  : forall A B, (var (wPair A B)) -> Gate A
    | gSnd  : forall A B, (var (wPair A B)) -> Gate B
    | gPair : forall A B, (var A) -> (var B) -> Gate (wPair A B)
    .

  (* all statements except for the terminal statement cReturn
     take a continuation CStmt.  In other words, a statement s1 is
     expressed in the normal form s1 ; s_more with `;` right associative. *)
  Inductive CStmt : WType -> Type :=
    (* cWire allows us to forward declare wires.  We can use this to
       create circular or backwards wiring patterns in conjunction with cEqn *)
    | cWire   : forall T_ret,
                forall T : WType, (var T -> CStmt T_ret) -> CStmt T_ret
    (* cBind evaluates a given Gate and binds
       the result to a new, guaranteed to be fresh name output wire *)
    | cBind   : forall T_ret T, 
                Gate T -> (var T -> CStmt T_ret)
                -> CStmt T_ret
    (* cEqn evaluates a given Gate and forces the output
       to match a specified output wire *)
    | cEqn    : forall T_ret T,
                Gate T -> var T -> (CStmt T_ret)
                -> CStmt T_ret
    | cReturn : forall T_ret, var T_ret -> CStmt T_ret
    .

  Inductive cCircuitDecl : WType -> WType -> Type :=
    | cFun : forall T_ret T_in,
             (var T_in -> CStmt T_ret)
             -> (cCircuitDecl T_in T_ret)
    .
End CircuitSyntax.
Arguments gNot  [var].
Arguments gAnd  [var].
Arguments gOr   [var].
Arguments gNand [var].
Arguments gNor  [var].
Arguments gFst  [var A B].
Arguments gSnd  [var A B].
Arguments gPair [var A B].

Arguments cWire [var T_ret].
Arguments cBind [var T_ret T].
Arguments cEqn  [var T_ret T].
Arguments cReturn [var T_ret].
Arguments cFun    [var T_ret].

Definition Circuit W_in W_out := forall var, cCircuitDecl var W_in W_out.


Example SR_Raw_Syntax : Circuit (wPair wBit wBit) wBit := (fun var =>
  (cFun (wPair wBit wBit) (fun SR =>
      (cWire wBit (fun Qn =>
      (cBind (gFst SR) (fun S =>
      (cBind (gSnd SR) (fun R =>
      (cBind (gNand S Qn) (fun Q =>
      (cReturn Q)
     ))))))))))).

(* We ought to be able to do a lot better than that.
   So, let's try to come up with a better syntax / notation.

   CktFun (SR : B*B)
      wire Qn : B;
      S := SR.0;
      R := SR.1;
      Q := gNand S Qn;
      Qn = gNand Q R;
      return Q
   end

 *)

Declare Custom Entry wtype_syntax.
Declare Custom Entry gate_syntax.
Declare Custom Entry cstmt_syntax.

Notation "'Unit'" := wUnit (in custom wtype_syntax at level 0).
Notation "'B'"  := wBit  (in custom wtype_syntax at level 0).
Notation "x * y" := (wPair x y)
  (in custom wtype_syntax at level 10, left associativity).

Notation "0"        := g0 (in custom gate_syntax at level 0).
Notation "1"        := g1 (in custom gate_syntax at level 0).
Notation "! x"      := (gNot x) (in custom gate_syntax at level 0).
Notation "x && y"   := (gAnd x y) (in custom gate_syntax at level 20).
Notation "x || y"   := (gOr  x y) (in custom gate_syntax at level 20).
Notation "! ( x && y )" := (gNand x y) (in custom gate_syntax at level 20,
  format "'!' '(' x '&&' y ')'").
Notation "! ( x || y )" := (gNor x y) (in custom gate_syntax at level 20).
Notation "x .0"     := (gFst x)   (in custom gate_syntax at level 0).
Notation "x .1"     := (gSnd x)   (in custom gate_syntax at level 0).
Notation "< x , y >" := (gPair x y) (in custom gate_syntax at level 0).
Notation "x"        := x (in custom gate_syntax at level 0, x constr).

Notation "'return' x" := (cReturn x)
  (in custom cstmt_syntax at level 20,
   x name).
Notation "y = g ; s" := (cEqn g y s)
  (in custom cstmt_syntax at level 0, right associativity,
   y name,
   g custom gate_syntax at level 20,
   s custom cstmt_syntax).
Notation "y := g ; s" :=
  (cBind g (fun y => s))
  (in custom cstmt_syntax at level 0, right associativity,
   y name,
   g custom gate_syntax at level 20,
   s custom cstmt_syntax).
Notation "'wire' x : W ; s" := (cWire W (fun x => s))
  (in custom cstmt_syntax at level 0, right associativity,
   x name,
   W custom wtype_syntax,
   s custom cstmt_syntax).

Notation "'CktFun' ( x : W ) body 'end'" :=
  ((fun var => cFun W (fun x => body)) : Circuit W _)
  (x name,
   W custom wtype_syntax,
   body custom cstmt_syntax).

Print Custom Grammar cstmt_syntax.

Definition SR_latch_test_syntax :=
   CktFun (SR : B*B)
      wire Qn : B;
      S := SR.0;
      R := SR.1;
      Q := gNand S Qn;
      Qn = gNand Q R;
      return Q
   end.

(* Note: I am currently having trouble with pretty printing the notation... *)




(* **********************************************************
    Definition of Semantic Domain and Denotation
 ********************************************************** *)

Definition Pred (X : Type)  := X -> Prop.
Definition Rel (X Y : Type) := X -> Y -> Prop.


Fixpoint WType_denotes (T : WType) : Set :=
  match T with
  | wUnit => unit
  | wBit => bool
  | wPair x y => (WType_denotes x) * (WType_denotes y)
  end.

Definition Gate_denotes T (g : Gate WType_denotes T)
  : Pred (WType_denotes T)
:=
  match g in Gate _ A return Pred (WType_denotes A) with
  | gtt _         => fun _ => True
  | g0 _          => fun r => r = false
  | g1 _          => fun r => r = true
  | gNot x        => fun r => r = negb x
  | gAnd x y      => fun r => r = andb x y
  | gOr  x y      => fun r => r = orb x y
  | gNand x y     => fun r => r = negb (andb x y)
  | gNor  x y     => fun r => r = negb (orb x y)
  | gFst xy       => fun r => r = fst xy
  | gSnd xy       => fun r => r = snd xy
  | gPair x y     => fun r => r = pair x y
  end.

Fixpoint CStmt_denotes rT (s : CStmt WType_denotes rT)
  : Pred (WType_denotes rT)
:=
  match s with
  | cWire wT f => fun r => exists (w : WType_denotes wT),
                                  CStmt_denotes _ (f w) r
  | cBind g f  => fun r => exists (w : WType_denotes _),
                                  (Gate_denotes _ g w) /\
                                  (CStmt_denotes _ (f w) r)
  | cEqn g y K => fun r => (Gate_denotes _ g y) /\
                           (CStmt_denotes _ K r)
  | cReturn x  => fun r => r = x
  end.

Definition circuitDecl_denotes Tin Tout
  (cdecl : cCircuitDecl WType_denotes Tin Tout)
  : Rel (WType_denotes Tin) (WType_denotes Tout)
:=
  match cdecl with
  | cFun _ body => fun arg r => CStmt_denotes _ (body arg) r
  end.

Definition Circuit_denotes Tin Tout (ckt : Circuit Tin Tout)
  : Rel (WType_denotes Tin) (WType_denotes Tout)
:=
  circuitDecl_denotes Tin Tout (ckt WType_denotes).

(* *********************************************************************
    Prelude to Definition of Operational Semantics:
      - Decidability of various basic types
      - Enumerability of various basic types
 ***********************************************************************
    First, generic definitions of decidability and enumerability
 ********************************************************************* *)

Require Import List.
Require Import ListSet.
Require Import Bool.

(* most of these should be in some library, but I couldn't find it *)
Definition dec_pred {A : Type} (P : Pred A) :=
  forall a, {P a} + {~P a}.
Definition dec_rel {A B : Type} (R : Rel A B) :=
  forall a b, {R a b} + {~R a b}.
Definition dec_eq (A : Type) :=
  forall x y : A, {x = y} + {x <> y}.

Record enumerable {X : Type} (P : Pred X) :=
  mkEnum {
    enum_set    : set X ;
    enum_dec_eq : dec_eq X ;
    enum_prop   : forall x, set_In x enum_set <-> P x
  }.
Arguments enum_dec_eq [X P].
Arguments enum_set [X P].
Arguments enum_prop [X P].

(* In order to say that an entire type X is enumerable, we will
   write (enumerable (AllOf T)).  This slight inconvenience means
   that we can also talk about enumerating "subsets" of types.
   Question: Maybe there's a more elegant way to do this? *)
Definition AllOf (X : Type) := (fun x : X => True).

(* note that if a predicate is enumerable, it must
   therefore be decidable, since it is a finite set *)
Definition enum_dec {X : Type} {P : Pred X}
  (enum_P : enumerable P)
  : dec_pred P.
Proof.
  destruct enum_P as (xset, xdec_eq, prop).
  intros x.
  destruct (set_In_dec xdec_eq x xset).
  - (* in the set *)
    left. apply prop; auto.
  - (* not in the set *)
    right; intro; apply n; apply prop; auto.
Defined.

(* Further, if a set is enumerable, then of course any decidable
   predicate on it is enumerable *)
Definition dec_enum {X : Type} {P : Pred X}
  (enum_X : enumerable (AllOf X))
  (dec_P  : dec_pred P)
  : enumerable P.
Proof.
  (* proof is overly messy *)
  destruct enum_X as (xs, X_dec_eq, all_xs).
  pose (x_P := fun x => if dec_P x then true else false).
  exists (filter x_P xs);
  subst x_P; unfold AllOf in *; auto.
  intro x. destruct (dec_P x); split; simpl.
  - auto.
  - intro; apply filter_In.
    destruct (dec_P x); split; try (apply all_xs); auto.
  - intro. apply filter_In in H.
    destruct (dec_P x); destruct H. contradiction. inversion H0.
  - intro; contradiction.
Defined.


(* *********************************************************************
    Second, we define *computable* lemmas for various basic
    types that do not depend on our language definition in any way.
 ********************************************************************* *)

Definition unit_dec_eq : dec_eq unit.
Proof. unfold dec_eq; intros x y; destruct x; destruct y; auto. Defined.

Definition unit_enum_set : set unit := tt :: nil.
Definition unit_enum : enumerable (AllOf unit).
Proof. exists unit_enum_set; auto using unit_dec_eq;
       intro x; destruct x;
       unfold AllOf; simpl; split; auto.
Defined.

Definition True_dec_eq : dec_eq True.
Proof. unfold dec_eq; intros x y; destruct x; destruct y; auto. Defined.

(* rename the result from the standard library
   so that it is consistent with our naming conventions here *)
Definition bool_dec_eq : dec_eq bool := bool_dec.

Definition bool_enum_set : set bool := false :: true :: nil.
Definition bool_enum : enumerable (AllOf bool).
Proof. exists bool_enum_set; auto using bool_dec_eq;
       intro x; destruct x;
       unfold AllOf; simpl; split; auto.
Defined.

Definition prod_dec_eq {A B : Type}
  (A_dec : dec_eq A) (B_dec : dec_eq B)
  : dec_eq (A * B).
Proof.
 intros x y. 
 destruct x as (xa,xb); destruct y as (ya,yb).
 destruct (A_dec xa ya) as [aeq|aneq].
 - destruct (B_dec xb yb) as [beq|bneq].
   + rewrite aeq; rewrite beq. auto.
   + right. intro H. inversion H. contradiction.
 - right. intro H; inversion H. contradiction.
Defined.

Definition prod_enum {A B : Type} 
  (enumA : enumerable (AllOf A))
  (enumB : enumerable (AllOf B))
  : enumerable (AllOf (A * B)).
Proof.
  destruct enumA as (A_set, A_dec_eq, A_prop);
  destruct enumB as (B_set, B_dec_eq, B_prop).
  exists (set_prod A_set B_set);
  auto using prod_dec_eq;
  intros (a,b);
  destruct (A_prop a);
  destruct (B_prop b);
  unfold AllOf in *; unfold set_In in *; simpl;
  split; auto.
  -  intro; apply in_prod; auto.
Defined.


(*
Definition proj1 {A B : Prop} (xy : A /\ B) : A
:= let '(conj x y) := xy in x.

Definition proj2 {A B : Prop} (xy : A /\ B) : B
:= let '(conj x y) := xy in y.

Definition conj_dec {A B : Prop}
  (A_dec : dec_eq A) (B_dec : dec_eq B)
  : dec_eq (A /\ B).
Proof.
  intros (xa,xb) (ya,yb);
  destruct (A_dec xa ya) as [aeq|aneq];
  destruct (B_dec xb yb) as [beq|bneq];
  (try rewrite aeq; try rewrite beq); auto;
  right; intro H.
  - apply (f_equal proj2) in H; auto.
  - apply (f_equal proj1) in H; auto.
  - apply (f_equal proj1) in H; auto.
Qed.
 *)

Definition conj_dec {A B : Prop}
  (A_dec : {A} + {~A}) (B_dec : {B} + {~B})
  : {A /\ B} + {~(A /\ B)}.
Proof.
  destruct A_dec; destruct B_dec;
  auto; (* auto handles the true,true case *)
  right; (* in all other cases, the conjunction is false *)
  intro AB; destruct AB; (* so assume A /\ B for the sake of ... *)
  contradiction.
Defined.

(* This is a key lemma.  It requires some non-obvious juggling
   to define it.  The main idea is that if the domain of an existential
   is enumerable and the predicate of the existential is decidable,
   then we can decide the existential by enumerating the potential
   first arguments and just checking each one. *)
Definition exists_dec {A : Type} {B : Pred A}
  (A_enum : enumerable (AllOf A))
  (B_dec  : dec_pred B)
  : {exists a:A, B a} + {~exists a:A, B a}.
Proof.
  destruct A_enum as (A_set, A_dec_eq, A_prop).
  pose (some_A := Exists_dec B A_set B_dec).
  destruct some_A as [ex_A | nex_A].
  - (* there IS some a : A satisfying B *)
    left.
    apply Exists_exists in ex_A.
    destruct ex_A as (a, (_,b)).
    exists a; auto.
  - (* there IS NO a : A satisfying B *)
    right.
    intros (a,b). (* assume there is an a,b satisfying for contradiction... *)
    apply nex_A.
    apply Exists_exists.
    exists a.
    split; auto.
    apply A_prop; unfold AllOf; auto.
Defined.

(*
Definition exists_enum_set {A : Type} {B : Pred A}
  (A_enum : enumerable (AllOf A))
  (B_enum : dec_pred B)
  : set (exists a:A, B a)
:=
  match A_enum with
  | (A_set, A_dec_eq, A_prop) =>
      match B_enum with
      | (B_set, B_dec_eq, B_prop) => 
          set_map (
          (fix union_map (xs : set A) :=
            match xs with
            | nil => nil
            | x : xs2 => set_union B_dec_eq (
      end
  end.
Proof.

Fixpoint union_map {X Y : Type}
  (y_dec : dec_eq Y)
  (f : X -> set Y) (xs : set X)
  : set Y
:=
  match xs with
  | nil => nil
  | x :: xs2 => set_union y_dec (f x) (union_map y_dec f xs2)
  end.
 *)

(* *********************************************************************
    Operational Semantics as Decidability
 ********************************************************************* *)

Definition WType_dec_eq (T : WType) : dec_eq (WType_denotes T).
Proof.
  induction T;
  intros x y;
  destruct x;
  destruct y;
  try (apply prod_dec_eq);
  auto using bool_dec.
Defined.

Definition WType_enum (T : WType) : enumerable (AllOf (WType_denotes T)).
Proof.
  induction T;
  try (apply prod_enum);
  auto using unit_enum, bool_enum.
Defined.

Definition Gate_dec T (g : Gate WType_denotes T)
  : dec_pred (Gate_denotes T g).
Proof.
  intro r;
  destruct g; simpl;
  (* handle boolean gate cases *)
  try (destruct r); auto using bool_dec_eq;
  (* handle pair elimination cases *)
  try (destruct w; apply WType_dec_eq);
  (* handle pair introduction case *)
  apply prod_dec_eq; apply WType_dec_eq.
Defined.

Definition CStmt_dec rT (s : CStmt WType_denotes rT)
  : dec_pred (CStmt_denotes rT s).
Proof.
  induction s; intro r; simpl.
  (* cWire *)
  - apply exists_dec; auto using WType_enum.
    intro x; apply X.
  (* cBind *)
  - apply exists_dec; auto using WType_enum.
    intro x; apply conj_dec; auto using (Gate_dec _ g); apply X.
  (* cEqn  *)
  - apply conj_dec; auto using (Gate_dec _ g); apply X.
  (* cReturn *)
  - apply WType_dec_eq.
Defined.

Definition circuitDecl_dec Tin Tout
  (cdecl : cCircuitDecl WType_denotes Tin Tout)
  : dec_rel (circuitDecl_denotes Tin Tout cdecl).
Proof.
  destruct cdecl as (Tout,Tin,body).
  intros x r; simpl.
  apply CStmt_dec.
Defined.

Definition Circuit_dec Tin Tout (ckt : Circuit Tin Tout)
  : dec_rel (Circuit_denotes Tin Tout ckt).
Proof.
  intros; apply circuitDecl_dec.
Defined.

(* *********************************************************************
    Simulate the SR Latch
 ********************************************************************* *)

Definition SR_latch :=
   CktFun (SR : B*B)
      wire Qn : B;
      S := SR.0;
      R := SR.1;
      Q := gNand S Qn;
      Qn = gNand Q R;
      return Q
   end.

Definition circuit_sim {Tin} {Tout}
  (ckt : Circuit Tin Tout) 
  (x : WType_denotes Tin)
:=
  enum_set (dec_enum (WType_enum _)
                     (Circuit_dec _ _ ckt x)).

Definition SR_sim := circuit_sim SR_latch.

Compute SR_sim (true, true).
Compute SR_sim (true, false).
Compute SR_sim (false, true).
Compute SR_sim (false, false).




