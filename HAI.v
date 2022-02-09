



(* First, we will provide a bunch of definitions
   for relations, as well as a notion of equivalence
   between two similarly typed relations.

   Relations will serve as the objects our
   circuits denote, and <=> as the equivalence
   between those objects.  Thus we will define
   equivalence of circuits.
 *)

Definition Rel (X Y : Type) := X -> Y -> Prop.

Definition iff_rel {X Y : Type} (R S : Rel X Y) :=
  forall x y, R x y <-> S x y.

Notation "R <=> S" := (iff_rel R S) (at level 90) : type_scope.

Theorem iff_rel_refl {X Y : Type} : forall (R : Rel X Y), R <=> R.
Proof.
  intros R x y.
  apply iff_refl.
Qed.

Theorem iff_rel_trans {X Y : Type} :
  forall (R S T : Rel X Y), (R <=> S) -> (S <=> T) -> (R <=> T).
Proof.
  intros R S T RS ST x y.
  apply (iff_trans (B := S x y)); auto.
Qed.

Theorem iff_rel_sym {X Y : Type} :
  forall (R S : Rel X Y), (R <=> S) -> (S <=> R).
Proof.
  intros R S RS x y.
  apply iff_sym; auto.
Qed.

Section Relational_Operators.
  
  (* parallel composition of relations
     is equivalent to their tensor product

           +-----+
     X ----|  R  |---- Y
           +-----+

           +-----+
     Z ----|  S  |---- W
           +-----+
  *)
  Definition par_rel {X Y Z W : Type} (R : Rel X Y) (S : Rel Z W)
    : Rel (X * Z) (Y * W) :=
    fun '(x,z) '(y,w) => (R x y) /\ (S z w).
  
  (* Sequential composition of relations
     is equivalent to a relational algebra join

           +-----+           +-----+
     X ----|  R  |---- Y ----|  S  |---- Z
           +-----+           +-----+

  *)
  Definition seq_rel {X Y Z : Type} (R : Rel X Y) (S : Rel Y Z) : Rel X Z :=
    fun x z => exists (y : Y), (R x y) /\ (S y z).

  (* transposition flips the circuit horizontally,
     exchanging input and output *)
  Definition transp_rel {X Y : Type} (R : Rel X Y) : Rel Y X :=
    fun y x => R x y.

  (* an easy way to define a bunch of relations is by
     just lifting functions up to relations *)
  Definition lift_f_rel {X Y : Type} (f : X -> Y) : Rel X Y :=
    fun x y => f x = y.

  (* a trivial wire component is the identity relation

     X ---- X

  *)
  Definition id_rel {X : Type} : Rel X X := lift_f_rel (fun x => x).

  (* we need to be able to split and join wires, so...

     X ---+
            \
             +--- X
            /
     X ---+

  *)
  Definition jam_rel (X : Type) : Rel (X * X) X :=
    fun '(x1,x2) x3 => x1 = x3 /\ x2 = x3.
  Definition dup_rel (X : Type) : Rel X (X * X) := transp_rel (jam_rel X).

  (* also we need to be able to leave loose ends

     +---- X

  *)
  Definition any_rel (X : Type) : Rel unit X := fun tt x => True.


  (* also likely a bit of overkill, but it would make sense to
     be able to commute and associate using relations too *)
  Definition cross_rel (X Y : Type) : Rel (X * Y) (Y * X) :=
    lift_f_rel (fun '(x,y) => (y,x)).
  Definition assoc_rel (X Y Z : Type) : Rel ((X * Y) * Z) (X * (Y * Z)) :=
    lift_f_rel (fun '((x,y),z) => (x,(y,z))).

End Relational_Operators.

(* just a random sanity check here right now *)
Lemma id_transp_id {X} : transp_rel (@id_rel X) <=> (@id_rel X).
Proof.
  intros x x'.
  unfold id_rel; unfold transp_rel; unfold lift_f_rel; simpl.
  split; intro H; auto.
Qed.





(*
  Now that we've done a bit of leg-work to model the semantic domain,
  let's define a syntax for circuits
 *)

(* basic shape types on wires *)
Inductive Wtype : Type :=
  | Wunit
  | Wbit
  | Wpair (w1 w2 : Wtype)
  .

(* probably can remove?  I thought I needed it at some point *)
Definition Wtype_eq_dec : forall w1 w2 : Wtype, { w1 = w2 } + { w1 <> w2 }.
Proof.
  decide equality.
Defined.


(* description of circuits themselves *)
Inductive Circuit : Type :=
  | Cnull
  | C0
  | C1
  | Cand
  | Cor
  | Cnot
  | Cid (w : Wtype)
  | Cpar (c1 c2 : Circuit)
  | Cseq (c1 c2 : Circuit)
  | Cflip (c : Circuit)
  | Cjam (w : Wtype)
  | Cnew (w : Wtype)
  | Ccross (w1 w2 : Wtype)
  | Cassoc (w1 w2 w3 : Wtype)
  .

(* Typing relation for circuits *)
Inductive has_type : Circuit -> Wtype -> Wtype -> Type :=
  | T_null  : has_type Cnull Wunit Wunit
  | T_0     : has_type C0    Wunit Wbit
  | T_1     : has_type C1    Wunit Wbit
  | T_and   : has_type Cand  (Wpair Wbit Wbit) Wbit
  | T_or    : has_type Cor   (Wpair Wbit Wbit) Wbit
  | T_not   : has_type Cnot  Wbit Wbit
  | T_id    : forall w, has_type (Cid w) w w
  | T_par   : forall c1 w1i w1o c2 w2i w2o,
                has_type c1 w1i w1o ->
                has_type c2 w2i w2o ->
                has_type (Cpar c1 c2) (Wpair w1i w2i) (Wpair w1o w2o)
  | T_seq   : forall c1 c2 w1 w2 w3,
                has_type c1 w1 w2 ->
                has_type c2 w2 w3 ->
                has_type (Cseq c1 c2) w1 w3
  | T_flip  : forall c w1 w2,
                has_type c w1 w2 ->
                has_type (Cflip c) w2 w1
  | T_jam   : forall w, has_type (Cjam w) (Wpair w w) w
  | T_new   : forall w, has_type (Cnew w) Wunit w
  | T_cross : forall w1 w2, has_type (Ccross w1 w2) (Wpair w1 w2) (Wpair w2 w1)
  | T_assoc : forall w1 w2 w3, has_type (Cassoc w1 w2 w3)
                                        (Wpair (Wpair w1 w2) w3)
                                        (Wpair w1 (Wpair w2 w3))
  .

Hint Constructors has_type.


(* denotation of syntactic types *)
Fixpoint wt_comb (w : Wtype) : Set :=
  match w with
  | Wunit => unit
  | Wbit => bool
  | Wpair w1 w2 => (wt_comb w1) * (wt_comb w2)
  end.

(* denotation of circuits as relations
   modeling atemporal, i.e. combinational circuits*)
Fixpoint rel_comb {wA wB : Wtype} (c : Circuit)
  (well_typed : has_type c wA wB)
  : Rel (wt_comb wA) (wt_comb wB)
:=
    match well_typed with
    | T_null           => (fun tt tt => True)
    | T_0              => (fun a b => b = false)
    | T_1              => (fun a b => b = true)
    | T_and            => (fun '(a0,a1) b => andb a0 a1 = b)
    | T_or             => (fun '(a0,a1) b => orb a0 a1 = b)
    | T_not            => lift_f_rel negb
    | T_id _           => id_rel
    | T_par c1 _ _ c2 _ _ wt1 wt2
        => par_rel (rel_comb c1 wt1) (rel_comb c2 wt2)
    | T_seq c1 c2 _ _ _ wt1 wt2
        => seq_rel (rel_comb c1 wt1) (rel_comb c2 wt2)
    | T_flip c _ _ wt  => transp_rel (rel_comb c wt)
    | T_jam w          => jam_rel (wt_comb w)
    | T_new w          => any_rel (wt_comb w)
    | T_cross w1 w2    => cross_rel (wt_comb w1) (wt_comb w2)
    | T_assoc w1 w2 w3 => assoc_rel (wt_comb w1) (wt_comb w2) (wt_comb w3)
    end.


(*
  Operational Semantics
   in terms of enumeration of
   potential solution sets
   follows
*)

Require Import List.
Require Import ListSet.
Require Import Bool.

(* most of these should be in a library, but I couldn't find it *)
Definition dec_eq (A : Type) := forall x y : A, {x = y} + {x <> y}.

Definition unit_dec : dec_eq unit.
Proof.
  left. destruct x. destruct y. trivial.
Defined.

(* bool_dec already defined *)
(* redefining so we have a version that will beta reduce *)
(*Definition bool_dec : dec_eq bool.
Proof.
  intros x y.
  destruct x; destruct y; auto.
  (* one case remains *)
  right; intro H; inversion H.
Defined.
 *)
Lemma fst_eq {A B : Type} {x y : A * B} (eq : x = y)
  : fst x = fst y.
Proof.
  destruct x; destruct y. simpl. inversion eq. trivial.
Qed.

Definition prod_dec {A B : Type}
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


Definition wt_comb_dec (w : Wtype) : dec_eq (wt_comb w).
Proof.
  intros x y.
  induction w; simpl in x,y.
  - apply unit_dec.
  - apply bool_dec.
  - apply (prod_dec IHw1 IHw2).
Defined.

Fixpoint union_map {X Y : Type}
  (y_dec : dec_eq Y)
  (f : X -> set Y) (xs : set X)
  : set Y
:=
  match xs with
  | nil => nil
  | x :: xs2 => set_union y_dec (f x) (union_map y_dec f xs2)
  end.

Lemma union_map_intro :
  forall {X Y : Type} (y_dec : dec_eq Y) (f : X -> set Y)
         (y : Y) (xs : set X) (x : X),
         set_In x xs -> set_In y (f x)
  -> set_In y (union_map y_dec f xs).
Proof.
  intros X Y y_dec f y xs.
  induction xs; auto; simpl. (* base case done *)
  intros x [Eax | inX] inY; try (rewrite Eax); apply set_union_intro; auto.
  (* x in xs *) right. apply (IHxs x); auto.
Qed.

Lemma union_map_elim :
  forall {X Y : Type} (y_dec : dec_eq Y) (f : X -> set Y)
         (y : Y) (xs : set X),
         set_In y (union_map y_dec f xs)
         -> exists (x:X), set_In x xs /\ set_In y (f x).
Proof.
  intros X Y y_dec f y xs.
  induction xs; simpl.
  - intro H; contradiction.
  - intro inUnion. apply set_union_elim in inUnion.
    destruct inUnion as [infa|inUnion].
    + exists a; auto.
    + apply IHxs in inUnion. destruct inUnion as (x,(in_xs,in_fx)).
      exists x; auto.
Qed.

Definition set_filter {A : Type} (f : A -> bool) := filter f.


(*
   Now, wrapping the building blocks up into an "enumeration" 
*)

Definition enum (X : Type) := set X.

Definition enum_bit := set_add bool_dec false
                               (set_add bool_dec true (empty_set bool)).
Definition enum_bit0 := set_add bool_dec false (empty_set bool).
Definition enum_bit1 := set_add bool_dec true  (empty_set bool).
Definition enum_unit := set_add unit_dec tt    (empty_set unit).

Definition enum_only {A : Type} (a : A) := a :: nil.

Fixpoint enum_type (w : Wtype) : enum (wt_comb w) :=
  match w with
  | Wunit         => enum_unit
  | Wbit          => enum_bit
  | Wpair w1 w2   => set_prod (enum_type w1) (enum_type w2)
  end.

Lemma enum_type_In (w : Wtype) (x : wt_comb w)
  : set_In x (enum_type w).
Proof.
  induction w; simpl.
  - destruct x; auto.
  - destruct x; auto.
  - destruct x as (x1,x2). apply (proj2 (in_prod_iff _ _ x1 x2)).
    split; [ apply IHw1 | apply IHw2 ].
Qed.



(* note that the following definition is slightly convoluted.
   We cannot simply project out the input enumeration to the A and B
   components, independently transform those enumerations/lists,
   and then recombine to find all products.  Doing so would destroy
   any correlations between A and B that we had discovered. *)
Definition enum_prod {A B C D : Type}
  (f : A -> enum C)
  (g : B -> enum D)
  : A * B -> enum (C * D)
:=
  fun '(a,b) => set_prod (f a) (g b).

Lemma enum_prod_intro {A B C D : Type}
  (f : A -> enum C)
  (g : B -> enum D)
  (a : A) (b : B) (c : C) (d : D)
  : set_In c (f a) -> set_In d (g b) -> set_In (c,d) (enum_prod f g (a,b)).
Proof.
  apply in_prod.
Qed.

Lemma enum_prod_fst {A B C D : Type}
  (f : A -> enum C)
  (g : B -> enum D)
  (a : A) (b : B) (c : C) (d : D)
  : set_In (c,d) (enum_prod f g (a,b)) -> set_In c (f a).
Proof.
  intro H. apply (in_prod_iff (f a) (g b) c d); auto.
Qed.

Lemma enum_prod_snd {A B C D : Type}
  (f : A -> enum C)
  (g : B -> enum D)
  (a : A) (b : B) (c : C) (d : D)
  : set_In (c,d) (enum_prod f g (a,b)) -> set_In d (g b).
Proof.
  intro H. apply (in_prod_iff (f a) (g b) c d); auto.
Qed.

Definition enum_transp
  (wA wB : Wtype)
  (f : wt_comb wA -> enum (wt_comb wB))
  (b : wt_comb wB) : enum (wt_comb wA)
:=
  set_filter (fun a => set_mem (wt_comb_dec wB) b (f a)) (enum_type wA).

Definition enum_jam (w : Wtype)
  (xy : wt_comb (Wpair w w)) : enum (wt_comb w)
:= let '(x,y) := xy in if (wt_comb_dec w x y) then x :: nil else nil.

Fixpoint enum_comb {wA wB : Wtype} (c : Circuit)
  (well_typed : has_type c wA wB)
  : wt_comb wA -> enum (wt_comb wB)
:=
  match well_typed with
  | T_null              => fun tt => enum_only tt
  | T_0                 => fun _ => false :: nil
  | T_1                 => fun _ => true :: nil
  | T_and               => fun '(x,y) => enum_only (andb x y)
  | T_or                => fun '(x,y) => enum_only (orb x y)
  | T_not               => fun x      => enum_only (negb x)
  | T_id _              => fun input  => enum_only input
  | T_par c1 _ w1o c2 _ w2o wt1 wt2
      => enum_prod (enum_comb c1 wt1) (enum_comb c2 wt2)
  | T_seq c1 c2 _ _ w3 wt1 wt2
      => fun a => (union_map (wt_comb_dec w3)
                             (enum_comb c2 wt2) (enum_comb c1 wt1 a))
  | T_flip c wi wo wt   => enum_transp wi wo (enum_comb c wt)
  | T_jam w             => enum_jam w
  | T_new w             => fun tts => enum_type w
  | T_cross w1 w2       => fun '(x,y) => enum_only (y,x)
  | T_assoc w1 w2 w3    => fun '((x,y),z) => enum_only (x,(y,z))
  end.


(*
  Finally!
   The main theorem states that the enumeration semantics,
   which is computable, corresponds perfectly with the
   non-computable denotational semantics in terms of relations.

   Specifically but still informally, given a circuit c of type wA -> wB,
   and given an input value a and output value b,
   then b is in (enum c a) iff. (denote c) a b holds.

   I am unsure about whether "P iff. Q" can equally well be encoded as 
     P <-> Q
   or whether
     P -> Q /\ ~P -> ~Q
   is necessarily different due to Coq being constructive.
 *)

Theorem enum_implies_rel
  {wA wB : Wtype} (c : Circuit) (wt : has_type c wA wB)
: forall (a : wt_comb wA) (b : wt_comb wB),
    set_In b (enum_comb c wt a)
    -> rel_comb c wt a b.
Proof.
  induction wt; intros a b; simpl in a, b; simpl.
  - (* Cnull  *) destruct b; auto.
  - (* C0     *) destruct b; simpl; auto. intros [H0|H1]; auto; contradiction.
  - (* C1     *) destruct b; simpl; auto. intros [H0|H1]; auto; contradiction.
  - (* Cand   *) destruct a as (a1,a2); intros [H0|H1]; auto; contradiction.
  - (* Cor    *) destruct a as (a1,a2); intros [H0|H1]; auto; contradiction.
  - (* Cnot   *) destruct a; intros [H0|H1]; auto; contradiction.
  - (* Cid    *) intros [H0|H1]; auto; contradiction.
  - (* Cpar   *) destruct b as (bi,bo); destruct a as (ai,ao); simpl.
    intro Hin. split. 
    + apply IHwt1. apply enum_prod_fst in Hin; auto.
    + apply IHwt2. apply enum_prod_snd in Hin; auto.
  - (* Cseq   *) intro Hin. apply union_map_elim in Hin. unfold seq_rel.
    destruct Hin as (x, (xin, bin)). exists x; auto.
  - (* Cflip  *) unfold enum_transp; unfold set_filter. intro Hinb.
    unfold transp_rel; apply IHwt.
    apply filter_In in Hinb. destruct Hinb as (_,Hinb).
    apply set_mem_correct1 in Hinb. auto.
  - (* Cjam   *) destruct a as (x,y); simpl.
    destruct (wt_comb_dec w x y). 
    + rewrite e; simpl. intros [H|H]; auto; contradiction.
    + intro H; contradiction.
  - (* Cnew   *) induction w; unfold any_rel; intro; auto.
  - (* Ccross *) destruct a as (a1,a2); destruct b as (b1,b2).
    unfold cross_rel; unfold lift_f_rel; intros [H|H]; auto; contradiction.
  - (* Cassoc *) destruct a as ((ax,ay),az); destruct b as (bx,(b_y,bz)).
    unfold assoc_rel; unfold lift_f_rel; intros [H|H]; auto; contradiction.
Qed.

Theorem rel_implies_enum
  {wA wB : Wtype} (c : Circuit) (wt : has_type c wA wB)
: forall (a : wt_comb wA) (b : wt_comb wB),
    rel_comb c wt a b
    -> set_In b (enum_comb c wt a).
Proof.
  induction wt; intros a b; simpl in a, b; simpl.
  - (* Cnull  *) destruct a; destruct b; auto.
  - (* C0     *) destruct b; auto.
  - (* C1     *) destruct b; auto.
  - (* Cand   *) destruct a as (a0,a1); destruct a0, a1, b; simpl; auto.
  - (* Cor    *) destruct a as (a0,a1); destruct a0, a1, b; simpl; auto.
  - (* Cnot   *) destruct a, b; simpl; auto.
  - (* Cid    *) auto.
  - (* Cpar   *) destruct a as (ai,ao); destruct b as (bi,bo); simpl.
    intros (Rc1, Rc2). apply in_prod; [ apply IHwt1 | apply IHwt2 ]; auto.
  - (* Cseq   *) unfold seq_rel; intros (x,(Rc1,Rc2)).
    apply (union_map_intro _ _ _ _ x); [ apply IHwt1 | apply IHwt2 ]; auto.
  - (* Cflip  *) unfold transp_rel, enum_transp; intro Rc.
    apply (proj2 (filter_In _ _ _)); split; auto.
    + apply enum_type_In.
    + apply set_mem_correct2. apply IHwt; auto.
  - (* Cjam   *) destruct a as (x,y); simpl.
    destruct (wt_comb_dec w x y); intros (exb,eyb).
    + unfold set_In, In; auto.
    + rewrite exb in n; rewrite eyb in n. contradiction.
  - (* Cnew   *) intro; apply enum_type_In.
  - (* Ccross *) destruct a as (ax,ay); destruct b as (b_y, bx); simpl.
    unfold cross_rel, lift_f_rel; auto.
  - (* Cassoc *) destruct a as ((ax,ay),az); destruct b as (bx,(b_y,bz)).
    unfold assoc_rel, lift_f_rel; simpl; auto.
Qed.



Definition Cdup (w : Wtype) := Cflip (Cjam w).

Definition Ccup (w : Wtype) := Cseq (Cnew w) (Cdup w).
Definition Ccap (w : Wtype) := Cseq (Cjam w) (Cflip (Cnew w)).

Definition Cassocinv (w1 w2 w3 : Wtype) := Cflip (Cassoc w1 w2 w3).

Hint Unfold Cdup Ccup Ccap Cassocinv.

(*
 * S  ---+--+
 *       |   \
 *       |    +O---- Q
 *       |   /
 *    ---+--+
 *
 *    ---+     +----
 *        \   /
 *         \ /
 *          X
 *         / \   
 *        /   \ 
 *    ---+     +----
 *
 *    ---+--+
 *       |   \
 *       |    +O---- Qnot
 *       |   /
 * R  ---+--+
 *)
Definition RS_mid := Cpar (Cpar
  (Cseq Cand Cnot)
  (Ccross Wbit Wbit))
  (Cseq Cand Cnot).

Definition P := Wpair.
Definition B := Wbit.
Hint Unfold P B.
Definition RS_mid_wt : has_type RS_mid (P (P (P B B) (P B B)) (P B B))
                                  (P (P B (P B B)) B).
Proof.
  unfold RS_mid, P, B.
  repeat (simple apply T_par); auto; apply (T_seq _ _ _ B); auto.
Defined.

(* working out reassociation component...
   ((S X) (Qn Q)) (Y R)
   (S (X (Qn Q))) (Y R)
   (S ((X Qn) Q)) (Y R)
   ((S (X Qn)) Q) (Y R)
   (S (X Qn)) (Q (Y R)
   (S (X Qn)) ((Q Y) R)
*)
Definition assoc_chain :
  Circuit
    (*(P (P (P B B) (P B B)) (P B B))
      (P (P B (P B B)) (P (P B B) B))*)
:=
(Cseq (Cseq (Cseq (Cseq
  (Cpar (Cassoc B B (P B B)) (Cid (P B B)))
  (Cpar (Cpar (Cid B) (Cassocinv B B B)) (Cid (P B B))))
  (Cpar (Cassocinv B (P B B) B) (Cid (P B B))))
  (Cassoc (P B (P B B)) B (P B B)))
  (Cpar (Cid (P B (P B B))) (Cassocinv B B B)))
  .

Definition assoc_chain_wt : has_type assoc_chain
  (P (P (P B B) (P B B)) (P B B))
  (P (P B (P B B)) (P (P B B) B)).
Proof.
  unfold assoc_chain, P, B, Cassocinv.
  repeat (eapply T_seq); repeat (apply T_par); auto. 
Defined.

(* now apply caps and jams to get the full RS *)
Definition RS
:=
(Cseq (Cseq (Cseq (Cseq (Cseq
(Cpar (Cpar (Cid B) (Ccup B)) (Cpar (Ccup B) (Cid B)))
(Cflip assoc_chain))
RS_mid)
(Cpar (Cassocinv B B B) (Cid B)))
(Cassoc (P B B) B B))
(Cpar (Cjam Wbit) (Cjam Wbit))).

Definition RS_wt : has_type RS (P (P B Wunit) (P Wunit B)) (P B B).
Proof.
  unfold RS, P, B, Ccup, Cdup, Cassocinv.
  repeat (eapply T_seq); repeat (apply T_par);
  repeat (eapply T_seq); auto; try (apply T_flip; apply assoc_chain_wt);
  auto; try (apply T_and); repeat (apply T_not).
Defined.

Definition RS_enum (S : bool) (R : bool) : enum (bool) := 
  map fst (enum_comb RS RS_wt ((S,tt),(tt,R)) ).

Compute (RS_enum true true).
Compute (RS_enum true false).
Compute (RS_enum false true).
Compute (RS_enum false false).


