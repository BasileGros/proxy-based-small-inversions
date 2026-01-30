From Examples Require Import examples_header.



Inductive color := Red | Orange | Green.
Inductive nextcolor : color -> color -> Prop :=
| ncGO : nextcolor Green Orange
| ncOR : nextcolor Orange Red
| ncRG : nextcolor Red Green
| nc_warn : nextcolor Orange Orange.

Derive InvProxy for nextcolor.

Print nextcolor_proxy.


Inductive nextcolor_green : color -> Prop :=
| ncGO_green : nextcolor_green Orange.

Inductive nextcolor_orange : color -> Prop :=
| ncOR_orange : nextcolor_orange Red
| nc_warn_orange : nextcolor_orange Orange.

Inductive nextcolor_red : color -> Prop :=
| ncRG_red  : nextcolor_red Green.

Inductive nextcolor_green_orange : Prop :=
| ncGO_green_orange : nextcolor_green_orange.

Inductive nextcolor_orange_orange : Prop :=
| nc_warn_orange_orange : nextcolor_orange_orange.

Inductive nextcolor_orange_red : Prop :=
| ncOR_orange_red : nextcolor_orange_red.

Inductive nextcolor_red_green : Prop :=
| ncRG_red_green : nextcolor_red_green.

Definition next_color_proxy_type (c1 c2 : color) : Prop :=
  match c1, c2 with
  |Green, Orange => nextcolor_green_orange
  |Green, _ => False
  |Orange, Green => False
  |Orange, Orange => nextcolor_orange_orange
  |Orange, Red => nextcolor_orange_red
  |Red, Green => nextcolor_red_green
  |Red, _ => False
  end.

Definition next_color_proxy (c1 c2 : color)(r : nextcolor c1 c2) :
  next_color_proxy_type c1 c2 :=
  match r with
  | ncGO => ncGO_green_orange
  | ncOR => ncOR_orange_red
  | ncRG => ncRG_red_green
  | nc_warn => nc_warn_orange_orange
  end.


Lemma no_green_stutter : not (nextcolor Green Green).
Proof.
  intro i.
  sinv i.
Qed.


Lemma no_green_stutter' : not (nextcolor Green Green).
Proof.
  intro i.
  destruct (next_color_proxy _ _ i).
Qed.
