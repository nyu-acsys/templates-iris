From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export lock multicopy multicopy_util.

Parameter inContents : val.
Parameter findNext : val.
Parameter addContents: val.

(** Template algorithms *)

Definition search (r d: Node) : val := 
  λ: "k",
    lockNode #r;;
    match: (inContents #r "k") with
      SOME "t" => unlockNode #r;; "t"
    | NONE => unlockNode #r;;
              lockNode #d;;
              match: (inContents #d "k") with
                SOME "t" => unlockNode #d;; "t"
              | NONE => unlockNode #d;; #0 end end.
  
Definition readClock : val :=
  λ: "l", !"l".
  
Definition incrementClock : val :=
  λ: "l", let: "t" := !"l" in
          "l" <- "t" + #1.

Definition upsert (lc: loc) (r: Node) : val :=
  rec: "upsert_rec" "k" := 
    lockNode #r ;;
    let: "t" := readClock #lc in
    let: "res" := addContents #r "k" "t" in
    if: "res" then 
      incrementClock #lc;;
      unlockNode #r
    else
      unlockNode #r;;
      "upsert_rec" "k".

(** Proof setup *)

Definition frac_contR := frac_agreeR (gmapUR K natUR).
Definition timeR := authR (max_natUR).

Class multicopy_dfG Σ := MULTICOPY_DF {
                            multicopy_df_frac_contG :> inG Σ frac_contR;
                            multicopy_df_timeG :> inG Σ timeR;
                      }.

Definition multicopy_dfΣ : gFunctors :=
  #[GFunctor frac_contR; GFunctor timeR ].

Instance subG_multicopy_dfΣ {Σ} : subG multicopy_dfΣ Σ → multicopy_dfG Σ.
Proof. solve_inG. Qed.

Section multicopy_df.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Assumptions on the implementation made by the template algorithms. *)

  Parameter node : Node → Node → (gmap K natUR) → iProp.

  Parameter nodeSpatial : Node → iProp.
  
  Parameter node_timeless_proof : ∀ r n C, Timeless (node r n C).
  Global Instance node_timeless r n C: Timeless (node r n C).
  Proof. apply node_timeless_proof. Qed.

  Parameter node_sep_star: ∀ r n C C',
    node r n C ∗ node r n C' -∗ False.

  (** The DF multicopy structure invariant *)

  Definition clock lc (t: nat) : iProp := lc ↦ #t.

  Definition nodePred γ_s γ_t γ_cn lc r n (Cn: gmap K nat) t : iProp :=
      node r n Cn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ (if (decide (n = r)) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t 
       else True)%I.

  Definition cir (H: gset KT) (Cr Cd: gmap K nat) :=
                   ∀ k t, ((Cr !! k = Some t → map_of_set H !! k = Some t)
                 ∧ (Cr !! k = None → map_of_set H !! k = Cd !! k)). 
      
  Definition Inv_DF γ_s γ_t γ_cr γ_cd (γ_d: gmap K gname) lc r d t H : iProp :=
    ∃ (Cr Cd: gmap K nat),
      own γ_t (●{1/2} MaxNat t)
    ∗ ⌜r ≠ d⌝  
    ∗ ⌜cir H Cr Cd⌝
    ∗ ([∗ set] k ∈ KS, own (γ_d !!! k) (● (MaxNat (Cd !!! k))))
    ∗ (∃ br, lockR br r (nodePred γ_s γ_t γ_cr lc r r Cr t))
    ∗ own (γ_cr) (to_frac_agree (1/2) (Cr))
    ∗ (∃ bd, lockR bd d (nodePred γ_s γ_t γ_cd lc r d Cd t))
    ∗ own (γ_cd) (to_frac_agree (1/2) (Cd)).

  Global Instance Inv_DF_timeless γ_s γ_t γ_cr γ_cd γ_d lc r d t H:
    Timeless (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d t H).
  Proof.
    rewrite /Inv_DF.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    destruct x1; try apply _.    
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (r = r)); try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct x1; try apply _.
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (d = r)); try apply _.
  Qed.
  
  (** Helper functions specs *)

  Parameter inContents_spec : ∀ r n Cn (k: K),
     ⊢ ({{{ node r n Cn }}}
           inContents #n #k
       {{{ (t: option nat), 
              RET (match t with Some t => SOMEV #t | None => NONEV end);
                  node r n Cn ∗ ⌜Cn !! k = t⌝ }}})%I.

  Lemma readClock_spec: ∀ γ_t lc q t, 
     ⊢ ({{{ own γ_t (●{q} MaxNat t) ∗ clock lc t }}}
           readClock #lc
       {{{ RET #t; own γ_t (●{q} MaxNat t) ∗ clock lc t }}})%I.
  Proof.
    intros γ_t lc q t.
    iIntros (Φ) "!# (Hqt & Hclock) HCont".
    wp_lam. wp_load. iApply "HCont". 
    iFrame; try done.
  Qed.  

  Parameter addContents_spec : ∀ r n Cn (k: K) (t:nat),
     ⊢ ({{{ node r n Cn ∗ ⌜n = r⌝ }}}
           addContents #r #k #t
       {{{ (succ: bool) (Cn': gmap K natUR),
              RET #succ;
                  node r n Cn' ∗ if succ then ⌜Cn' = <[k := t]> Cn⌝ 
                                else ⌜Cn' = Cn⌝ }}})%I.            
                                                                   
  (** Lock module **)
  
  Global Instance HnP_t_laterable (r n: Node) γ_t lc T : 
              Laterable (if decide (n = r) 
                         then own γ_t (●{1 / 2} MaxNat T) ∗ clock lc T 
                         else True)%I.
  Proof.
    destruct (decide (n = r)); apply timeless_laterable; apply _.
  Qed.
  
  Lemma lockNode_spec_high N γ_te γ_he γ_s Prot γ_t γ_cr γ_cd γ_d lc r d n:
    ⊢ mcs_inv N γ_te γ_he γ_s Prot (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d) -∗
        ⌜n = r ∨ n = d⌝ -∗
              <<< True >>>
                lockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< ∃ γ_cn Cn t, nodePred γ_s γ_t γ_cn lc r n Cn t
              ∗ ⌜(n = r ∧ γ_cn = γ_cr) ∨ (n = d ∧ γ_cn = γ_cd)⌝ , RET #() >>>.
  Proof.
    iIntros "#mcsInv %". rename H into n_eq_rd.
    iIntros (Φ) "AU".
    awp_apply (lockNode_spec n).
    iInv "mcsInv" as (T H) "(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr Cd)"(Ht & r_neq_d & Hcir & Hbigstar 
                & HlockR_r & Half_Cr & HlockR_d & Half_Cd)".
    destruct n_eq_rd as [? | ?]; subst n.            
    - iDestruct "HlockR_r" as (br)"HlockR_r".
      iAaccIntro with "HlockR_r".
      { iIntros "HlockR_r". iModIntro. 
        iFrame "AU". iNext. iExists T, H. 
        eauto 20 with iFrame. }              
      iIntros "(HlockR_r & HnP_r)".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! γ_cr Cr T).
      iAssert (⌜r = r ∧ γ_cr = γ_cr ∨ r = d ∧ γ_cr = γ_cd⌝)%I as "node_matches".
      {
        iPureIntro. left. done.
      }
      iCombine "HnP_r" "node_matches" as "HnP_r".
      iMod ("Hcomm" with "HnP_r") as "HΦ".
      iModIntro. iFrame "HΦ".
      iNext; iExists T, H. iFrame.
      iExists Cr, Cd. iFrame.
      iExists true; try done.
    - iDestruct "HlockR_d" as (bd)"HlockR_d".
      iAaccIntro with "HlockR_d".
      { iIntros "HlockR_d". iModIntro. 
        iFrame "AU". iNext. iExists T, H. 
        eauto 20 with iFrame. }              
      iIntros "(HlockR_d & HnP_d)".
      iMod "AU" as "[_ [_ Hcomm]]".
      iSpecialize ("Hcomm" $! γ_cd Cd T).
      iAssert (⌜d = r ∧ γ_cd = γ_cr ∨ d = d ∧ γ_cd = γ_cd⌝)%I as "node_matches".
      {
        iPureIntro. right. done.
      }
      iCombine "HnP_d" "node_matches" as "HnP_d".
      iMod ("Hcomm" with "HnP_d") as "HΦ".
      iModIntro. iFrame "HΦ".
      iNext; iExists T, H. iFrame.
      iExists Cr, Cd. iFrame.
      iExists true; try done.
  Qed.
  
  Lemma unlockNode_spec_high N γ_te γ_he γ_s Prot γ_t γ_cr γ_cd γ_d lc r d 
                             n Cn γ_cn t:
    ⊢ mcs_inv N γ_te γ_he γ_s Prot (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d) -∗
        ⌜(n = r ∧ γ_cn = γ_cr) ∨ (n = d ∧ γ_cn = γ_cd)⌝ -∗
          nodePred γ_s γ_t γ_cn lc r n Cn t -∗
              <<< True >>>
                unlockNode #n    @ ⊤ ∖ ↑(mcsN N)
              <<< True, RET #() >>>.
  Proof.
    iIntros "#mcsInv % Hnp". rename H into n_eq_rd.
    iIntros (Φ) "AU".
    awp_apply (unlockNode_spec n).
    iInv "mcsInv" as (T H) "(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Cr Cd)"(Ht & r_neq_d & Hcir & Hbigstar 
                & HlockR_r & Half_Cr & HlockR_d & Half_Cd)".
    destruct n_eq_rd as [[? ?] | [? ?]]; subst n γ_cn.            
    - iAssert (⌜Cn = Cr⌝)%I as "%".
      { iDestruct "Hnp" as "(_ & _ & Hf & _)".
        iPoseProof (own_valid_2 _ _ _ with "[$Hf] [$Half_Cr]") as "H'".
        iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
        destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
        by iPureIntro. } subst Cn.
      iAssert (⌜t = T⌝)%I as "%".
      { iDestruct "Hnp" as "(_ & _ & _ & H')".
        iEval (rewrite decide_True) in "H'".
        iDestruct "H'" as "(H' & _)".
        iPoseProof (own_valid_2 with "[$H'] [$Ht]") as "%".
        rename H0 into H'. apply auth_auth_frac_op_inv in H'.
        inversion H'. by iPureIntro. } subst t.   
      iAssert (lockR true r (nodePred γ_s γ_t γ_cr lc r r Cr T)
                ∗ nodePred γ_s γ_t γ_cr lc r r Cr T)%I 
                    with "[HlockR_r Hnp]" as "H".
      { iDestruct "HlockR_r" as (br)"HlockR_r".
        destruct br eqn: Hb.
        - (* Case n locked *)
          iFrame "∗".
        - (* Case n unlocked: impossible *)
          iDestruct "Hnp" as "(node & _)".
          iDestruct "HlockR_r" as "(_ & Hnp')".
          iDestruct "Hnp'" as "(node' & _)".
          iExFalso; iApply node_sep_star; try iFrame. }
      iAaccIntro with "H".
      { iIntros "(HlockR_r & Hnp)".
        iModIntro. iFrame.
        iNext; iExists T, H; iFrame.
        iExists Cr, Cd; iFrame.
        iExists true; try done. }
      iIntros "HlockR_r".
      iMod "AU" as "[_ [_ Hcomm]]".
      iMod ("Hcomm" with "[]") as "HΦ"; try done.
      iModIntro. iFrame "HΦ". iNext; iExists T, H.
      iFrame. iExists Cr, Cd. iFrame. iExists false; try done.                        
    - iAssert (⌜Cn = Cd⌝)%I as "%".
      { iDestruct "Hnp" as "(_ & _ & Hf & _)".
        iPoseProof (own_valid_2 _ _ _ with "[$Hf] [$Half_Cd]") as "H'".
        iDestruct "H'" as %H'. apply frac_agree_op_valid in H'.
        destruct H' as [_ H']. apply leibniz_equiv_iff in H'.
        by iPureIntro. } subst Cn.
      iDestruct "r_neq_d" as %r_neq_d.  
      iAssert (lockR true d (nodePred γ_s γ_t γ_cd lc r d Cd T)
                ∗ nodePred γ_s γ_t γ_cd lc r d Cd T)%I 
                    with "[HlockR_d Hnp]" as "H".
      { iDestruct "HlockR_d" as (bd)"HlockR_d".
        destruct bd eqn: Hb.
        - (* Case n locked *)
          iFrame "∗". iDestruct "Hnp" as "(?&?&?&?)".
          iFrame. destruct (decide (d = r)); try done. 
        - (* Case n unlocked: impossible *)
          iDestruct "Hnp" as "(node & _)".
          iDestruct "HlockR_d" as "(_ & Hnp')".
          iDestruct "Hnp'" as "(node' & _)".
          iExFalso; iApply node_sep_star; try iFrame. }
      iAaccIntro with "H".
      { iIntros "(HlockR_d & Hnp)".
        iModIntro.
        iDestruct "Hnp" as "(?&?&?&?)".
        iFrame. destruct (decide (d = r)); try done.
        iSplitL. iNext; iExists T, H; iFrame.
        iExists Cr, Cd; iFrame "∗%".
        iExists true; try done. done. }
      iIntros "HlockR_d".
      iMod "AU" as "[_ [_ Hcomm]]".
      iMod ("Hcomm" with "[]") as "HΦ"; try done.
      iModIntro. iFrame "HΦ". iNext; iExists T, H.
      iFrame. iExists Cr, Cd. iFrame "∗%". 
      iExists false; try done.
  Qed.                              


End multicopy_df.           
