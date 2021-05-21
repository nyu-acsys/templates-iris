From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.proofmode Require Import tactics.
Set Default Proof Using "All".
Require Export multicopy.

Section multicopy_util.
  Context {Σ} `{!multicopyG Σ}.
  Notation iProp := (iProp Σ).

  Lemma MCS_agree γ_te γ_he t H t' H':
    MCS_auth γ_te γ_he t H -∗ MCS γ_te γ_he t' H' -∗ ⌜t = t'⌝ ∗ ⌜H = H'⌝.
  Proof.
    iIntros "(Ht● & HH●) (Ht'◯ & HH'◯ & _)".
    iDestruct (own_valid_2 with "Ht● Ht'◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "HH● HH'◯")
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
    by iPureIntro.
  Qed.

  Lemma map_of_set_lookup_cases H1 k:
        (∃ T, (k, T) ∈ H1 ∧ (∀ t, (k,t) ∈ H1 → t ≤ T) ∧ map_of_set H1 !! k = Some T)
      ∨ ((∀ t, (k,t) ∉ H1) ∧ map_of_set H1 !! k = None).
  Proof.
    set (P := λ (m: gmap K nat) (X: gset KT),
                (∃ T, (k, T) ∈ X ∧ (∀ t, (k,t) ∈ X → t ≤ T)
                          ∧ m !! k = Some T)
              ∨ ((∀ t, (k,t) ∉ X) ∧ m !! k = None)).
    apply (set_fold_ind_L P); try done.
    - unfold P. right. split; try done.
    - intros [k' t'] X m Hnotin Hp.
      destruct (decide (k' = k)).
      + replace k'. unfold P. left. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [T Hp].
          destruct (decide (T < t')).
          ** exists t'. repeat split; first set_solver.
             intros t. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t = t') by set_solver.
             lia. destruct Hp as [_ [Hp _]].
             pose proof Hp t Hv. lia. simpl.
             assert (m !!! k <= t') as Hm.
             { unfold lookup_total, map_lookup_total.
               destruct Hp as [_ [_ Hp]]. rewrite Hp.
               simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.
             by rewrite lookup_insert.
          ** assert (t' = T ∨ t' < T) as Ht by lia. clear n.
             exists T. destruct Hp as [Hp1 [Hp2 Hp3]].
             repeat split; first set_solver.
             intros t. rewrite elem_of_union.
             intros [Hv | Hv]. assert (t = t') by set_solver.
             lia. pose proof Hp2 t Hv. lia. simpl.
             destruct Ht as [Ht | Ht].
             assert (m !!! k <= t') as Hm.
             { unfold lookup_total, map_lookup_total.
               rewrite Hp3. simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.
             rewrite lookup_insert. by rewrite Ht.
             assert (m !!! k > t') as Hm.
             { unfold lookup_total, map_lookup_total.
               rewrite Hp3. simpl. lia. }
             destruct (decide (m !!! k ≤ t')); try done.
             exfalso. lia.
        * exists t'. simpl. repeat split; first set_solver.
          intros t. rewrite elem_of_union. intros [Hv | Hv].
          assert (t = t') by set_solver. lia.
          destruct Hp as [Hp _].
          pose proof Hp t as Hp. set_solver.
          assert (m !!! k ≤ t') as Hm.
          { unfold lookup_total, map_lookup_total.
            destruct Hp as [_ Hp]. rewrite Hp. simpl; lia. }
          destruct (decide (m !!! k ≤ t')); try done.
          by rewrite lookup_insert.
      + unfold P. unfold P in Hp.
        destruct Hp as [Hp | Hp].
        * destruct Hp as [T [Hp1 [Hp2 Hp3]]].
          left. exists T. repeat split; first set_solver.
          intros t Hkt. assert ((k,t) ∈ X) as Hx by set_solver.
          by pose proof Hp2 t Hx.
          simpl.
          destruct (decide (m !!! k' <= t')).
          rewrite lookup_insert_ne; try done. done.
        * destruct Hp as [Hp1 Hp2]. right.
          repeat split; first set_solver. simpl.
          destruct (decide (m !!! k' <= t')).
          rewrite lookup_insert_ne; try done. done.
  Qed.

  Lemma map_of_set_lookup H k T :
        (k, T) ∈ H → (∀ t, (k, t) ∈ H → t ≤ T) →
           map_of_set H !! k = Some T.
  Proof.
    intros Hkt Hmax.
    pose proof (map_of_set_lookup_cases H k) as Hp.
    destruct Hp as [Hp | Hp].
    - destruct Hp as [T' [Hp1 [Hp2 Hp3]]].
      pose proof Hmax T' Hp1 as Ht1.
      pose proof Hp2 T Hkt as Ht2.
      assert (T = T') as Ht by lia.
      by rewrite Ht.
    - destruct Hp as [Hp _].
      pose proof Hp T. set_solver.
  Qed.

  Lemma map_of_set_lookup_some_aux (H: gset KT) k :
          (∀ t, (k,t) ∉ H) ∨ (∃ T, (k, T) ∈ H ∧ (∀ t', (k,t') ∈ H → t' ≤ T)).
  Proof.
    set (P := λ (X: gset KT), (∀ t, (k,t) ∉ X) ∨
                  (∃ T, (k, T) ∈ X ∧ (∀ t', (k,t') ∈ X → t' ≤ T))).
    apply (set_ind_L P); try done.
    - unfold P. left. intros t. set_solver.
    - intros [k' t'] X Hkt HP. subst P.
      simpl in HP. simpl. destruct (decide (k' = k)).
      + subst k'. destruct HP as [H' | H'].
        * right. exists t'. split.
          set_solver. intros t. destruct (decide (t' = t)).
          subst t'. intros; done.
          intros H''. assert ((k,t) ∈ X).
          set_solver. pose proof H' t as H'.
          done.
        * right. destruct H' as [T H'].
          destruct (decide (t' < T)).
          ** exists T. split.
             destruct H' as [H' _].
             set_solver. intros t Hkt'.
             rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H'']. apply H''; try done.
          ** exists t'. split. set_solver.
             intros t Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
             destruct Hkt' as [Hkt' | Hkt'].
             rewrite elem_of_singleton in Hkt'*; intros Hkt'.
             inversion Hkt'. lia.
             destruct H' as [_ H''].
             apply (Nat.le_trans _ T _); try lia.
             apply H''. try done.
      + destruct HP as [H' | H'].
        * left. intros t. set_solver.
        * right. destruct H' as [T H'].
          exists T. destruct H' as [H' H''].
          split. set_solver. intros t.
          intros Hkt'. rewrite elem_of_union in Hkt'*; intros Hkt'.
          destruct Hkt' as [Hkt' | Hkt'].
          rewrite elem_of_singleton in Hkt'*; intros Hkt'.
          inversion Hkt'. done. apply H''; try done.
  Qed.

  Lemma map_of_set_lookup_some (H: gset KT) k t :
              (k, t) ∈ H → is_Some(map_of_set H !! k).
  Proof.
    intros Hkt.
    pose proof map_of_set_lookup_some_aux H k as Hkt'.
    destruct Hkt' as [Hkt' | Hkt'].
    { pose proof Hkt' t as H'. set_solver. }
    pose proof (map_of_set_lookup_cases H k) as H'.
    destruct H' as [H' | H'].
    - destruct H' as [T' H'].
      destruct H' as [_ [_ H']].
      rewrite H'. by exists T'.
    - destruct Hkt' as [T Hkt'].
      destruct Hkt' as [Hkt' _].
      destruct H' as [H' _].
      pose proof H' T as H'.
      set_solver.
  Qed.

  Lemma map_of_set_lookup_lb H k t :
    (k,t) ∈ H → t ≤ map_of_set H !!! k.
  Proof.
    intros kt_in_H.
    pose proof map_of_set_lookup_cases H k as [H' | H'].
    - destruct H' as [T [kT_in_H [H' H_k]]].
      rewrite lookup_total_alt. rewrite H_k.
      simpl. apply H'; try done.
    - destruct H' as [H' _].
      pose proof H' t as H'.
      contradiction.
  Qed.

  Lemma set_of_map_member_ne (C: gmap K nat) k :
            C !! k = None →
              ∀ t, (k, t) ∉ set_of_map C.
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat),
                   m !! k = None → ∀ t, (k, t) ∉ s).
    apply (map_fold_ind P); try done.
    intros kx tx m r Hm HP. unfold P.
    unfold P in HP. destruct (decide (kx = k)).
    - subst kx. rewrite lookup_insert. try done.
    - rewrite lookup_insert_ne; try done.
      intros Hm'. pose proof HP Hm' as HP.
      intros t. intros Hnot.
      rewrite elem_of_union in Hnot*; intros Hnot.
      destruct Hnot as [Hnot | Hnot].
      + by apply HP in Hnot.
      + rewrite elem_of_singleton in Hnot*; intros Hnot.
        inversion Hnot. try done.
  Qed.

  Lemma map_of_set_union_ne H k t k' :
          k' ≠ k → map_of_set (H ∪ {[(k, t)]}) !! k' = map_of_set H !! k'.
  Proof.
    intros Hk.
    pose proof (map_of_set_lookup_cases H k') as Hp.
    pose proof (map_of_set_lookup_cases (H ∪ {[(k,t)]}) k') as Hu.
    destruct Hp as [Hp | Hp].
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [T [Hp1 [Hp2 Hp3]]].
        destruct Hu as [T' [Hu1 [Hu2 Hu3]]].
        assert (T ≤ T') as Ht1.
        { assert ((k', T) ∈ H ∪ {[k, t]}) as Ht by set_solver.
          by pose proof Hu2 T Ht. }
        assert (T' ≤ T) as Ht2.
        { assert ((k', T') ∈ H) as Ht by set_solver.
          by pose proof Hp2 T' Ht. }
        rewrite Hp3 Hu3. assert (T = T') as Ht by lia.
        by rewrite Ht.
      + destruct Hp as [T [Hp1 [Hp2 Hp3]]].
        destruct Hu as [Hu1 Hu2].
        pose proof Hu1 T as Hu1. set_solver.
    - destruct Hu as [Hu | Hu].
      + destruct Hp as [Hp1 Hp2].
        destruct Hu as [T' [Hu1 [Hu2 Hu3]]].
        pose proof Hp1 T' as Hp1. set_solver.
      + destruct Hp as [Hp1 Hp2].
        destruct Hu as [Hu1 Hu2].
        by rewrite Hp2 Hu2.
  Qed.

  Lemma map_of_set_insert_eq (C: gmap K nat) k T H :
        (∀ t, (k, t) ∈ H → t < T) →
                  C = map_of_set H →
                 <[k := T]> C = map_of_set (H ∪ {[(k, T)]}).
  Proof.
    intros Hmax Hc. apply map_eq. intros k'.
    destruct (decide (k' = k)).
    - replace k'. rewrite lookup_insert.
      rewrite (map_of_set_lookup _ _ T); try done.
      set_solver. intros t'. rewrite elem_of_union.
      intros [Hk | Hk]. pose proof Hmax t' Hk. lia.
      assert (t' = T) by set_solver. by replace t'.
    - rewrite map_of_set_union_ne; try done.
      rewrite lookup_insert_ne; try done.
      by rewrite Hc.
  Qed.

  Lemma set_of_map_member (C: gmap K nat) k t :
            C !! k = Some(t) →
              (k, t) ∈ set_of_map C.
  Proof.
    intros Hc. unfold set_of_map.
    set (P := λ (s: gset KT) (m: gmap K nat),
                  ∀ j x, m !! j = Some x → (j,x) ∈ s).
    apply (map_fold_ind P); try done.
    intros i x m s Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert.
      intros H'; inversion H'. set_solver.
    - rewrite lookup_insert_ne; try done.
      pose proof Hp j x' as Hp'. set_solver.
  Qed.

  Lemma set_of_map_member_rev (C: gmap K nat) k t :
            (k, t) ∈ set_of_map C →
                C !! k = Some(t).
  Proof.
    set (P := λ (s: gset KT) (m: gmap K nat),
                  ∀ j x, (j,x) ∈ s → m !! j = Some x).
    apply (map_fold_ind P); try done.
    intros i x m r Hmi Hp. unfold P.
    intros j x'. destruct (decide (i = j)).
    - replace j. rewrite lookup_insert.
      rewrite elem_of_union. intros [Hr | Hr].
      unfold P in Hp. pose proof Hp i x' Hr as Hp.
      rewrite Hp in Hmi. inversion Hmi.
      assert (x = x') by set_solver. by replace x.
    - intros H'. assert ((j,x') ∈ r) as Hj by set_solver.
      pose proof Hp j x' Hj as Hp.
      rewrite lookup_insert_ne; try done.
  Qed.

  Lemma set_of_map_insert_subseteq (C: gmap K nat) k t :
    set_of_map (<[k := t]> C) ⊆ set_of_map C ∪ {[(k, t)]}.
  Proof.
    intros [k' t'] Hkt. destruct (decide (k' = k)).
    - replace k'. rewrite e in Hkt.
    apply set_of_map_member_rev in Hkt.
    rewrite lookup_insert in Hkt.
    inversion Hkt. set_solver.
    - apply set_of_map_member_rev in Hkt.
    rewrite lookup_insert_ne in Hkt; try done.
    apply set_of_map_member in Hkt.
    set_solver.
  Qed.

End multicopy_util.
