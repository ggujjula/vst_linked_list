Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import linked_list.linked_list.

Local Open Scope Z_scope.

Section proof.
Context `{!VSTGS OK_ty Σ}.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition model := list Z.
Definition t_ll := Tstruct _ll noattr.
Definition t_stack := Tstruct _stack noattr.

Fixpoint is_list (p:val) (m: model) : mpred :=
match m with
| [] => ⌜ p = nullval ⌝ ∗ emp
| x :: xs => ∃ next:val,
    malloc_token Ews (t_ll) p ∗ 
    data_at Ews (t_ll) (Vint (Int.repr x), next) p ∗
    is_list next xs
end.

Lemma is_list_local_facts: ∀ l m,
is_list l m ⊢ ⌜ is_pointer_or_null l ∧
                (l=nullval <-> m=nil) ⌝.
Proof.
    intros.
    unfold is_list.
    destruct m.
    { entailer. split.
    { auto. }
    split; auto.
    }
    Intros next.
    entailer!.
    split; intros; apply field_compatible_nullval1 in H0.
    { contradiction. }
    { discriminate. }
Qed.

Lemma is_list_valid_pointer: ∀ l m,
is_list l m ⊢ valid_pointer l.
Proof.
    intros.
    unfold is_list.
    destruct m.
    { entailer. }
    { Intros next. entailer!. }
Qed.

Definition is_stack (p:val) (m: model) : mpred := ∃ top:val,
malloc_token Ews t_stack p ∗ 
data_at Ews t_stack top p ∗
is_list top m.

Lemma is_stack_local_facts: ∀ p m,
is_stack p m ⊢ ⌜ isptr p ⌝.
Proof.
    intros.
    unfold is_stack.
    Intros top.
    entailer!.
Qed.

Lemma is_stack_valid_pointer: ∀ l m,
is_stack l m ⊢ valid_pointer l.
Proof.
    intros.
    unfold is_stack.
    Intros *. entailer!.
Qed.

Hint Resolve is_list_local_facts : saturate_local.
Hint Resolve is_list_valid_pointer : valid_pointer.
Hint Resolve is_stack_local_facts : saturate_local.
Hint Resolve is_stack_valid_pointer : valid_pointer.

Definition ll_empty_spec: ident * funspec :=
DECLARE _ll_empty
WITH m:model, gv:globals
PRE[]
    PROP(m = [])
    PARAMS()
    GLOBALS(gv)
    SEP(mem_mgr gv)
POST[tptr (t_stack)] ∃ p:val,
    PROP()
    RETURN(p)
    SEP(mem_mgr gv; (if eq_dec p nullval then
    emp
    else
    is_stack p m)).

Definition ll_push_spec: ident * funspec :=
DECLARE _ll_push
WITH s:val, m:model, v:Z, gv:globals
PRE[tptr (t_stack), tint]
    PROP(Int.min_signed <= v <= Int.max_signed)
    PARAMS(s; Vint(Int.repr v))
    GLOBALS(gv)
    SEP(mem_mgr gv ; is_stack s m)
POST[tint] ∃ (success:Z),
    PROP()
    RETURN(Vint (Int.repr success))
    SEP(mem_mgr gv ; (if zeq success 0 then 
            is_stack s (v::m)
        else
            is_stack s m)).

Definition ll_pop_spec: ident * funspec :=
DECLARE _ll_pop
WITH s:val, p:val, x:Z, xs:model, gv:globals, sh: share
PRE[tptr (t_stack), tptr tint]
    PROP(writable_share sh)
    PARAMS(s; p)
    GLOBALS(gv)
    SEP(mem_mgr gv ; is_stack s (x::xs); data_at_ sh tint p)
POST[tint] ∃ (retval:val),
    PROP(retval = Vint(Int.repr 0))
    RETURN(retval)
    SEP(mem_mgr gv ;
            data_at sh tint (Vint (Int.repr x)) p ∗
            is_stack s xs).

Definition Gprog := ltac:(with_library prog [ll_empty_spec; ll_push_spec; ll_pop_spec]).

Lemma ll_empty_proof: semax_body Vprog Gprog f_ll_empty ll_empty_spec.
Proof.
    start_function.
    forward_call (t_stack, gv).
    Intros vret.
    if_tac; forward_if.
    { forward. Exists nullval. simpl. auto. }
    { contradiction. }
    { contradiction. }
    Intros.
    fastforward! 2.
    Exists vret. simpl. entailer!.
    rewrite if_false.
    { unfold is_stack. Exists nullval. entailer!. auto. }
    apply H0.
Qed.

Lemma ll_push_proof: semax_body Vprog Gprog f_ll_push ll_push_spec.
Proof.
    start_function.
    forward_call (t_ll, gv); Intros vret.
    if_tac; forward_if.
    { forward. Exists 1. simpl. entailer!. }
    { contradiction. }
    { contradiction. }
    Intros.
    fastforward! 5.
    Exists 0. 
    simpl.
    unfold is_stack.
    Exists vret.
    unfold is_list.
    Exists top.
    entailer!.
Qed.
    
Lemma ll_pop_proof: semax_body Vprog Gprog f_ll_pop ll_pop_spec.
Proof.
    start_function.
    fastforward 7.
    forward_call (t_ll, top, gv).
    { entailer!. rewrite if_false.
    { entailer!. }
    { apply field_compatible_nullval1 in H3. exact. }
    }
    forward.
    unfold is_stack.
    Exists (Vint(Int.repr 0)).
    Exists next.
    fold is_list.
    entailer!.
Qed.

End proof.
