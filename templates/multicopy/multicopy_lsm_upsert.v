From iris.algebra Require Import excl auth cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_lsm multicopy_lsm_util.

Section multicopy_lsm_upsert.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_lsmG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).
  
  Lemma upsert_spec N γ_te γ_he γ_s Prot γ_t γ_I γ_J γ_f γ_gh lc r (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he Prot k) -∗ 
        mcs_inv N γ_te γ_he γ_s Prot 
          (Inv_LSM γ_s γ_t γ_I γ_J γ_f γ_gh lc r) -∗
            <<< ∀ t H, MCS γ_te γ_he t H >>> 
                   upsert lc r #k @ ⊤ ∖ (↑(mcsN N))
            <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k,t)]}), RET #() >>>.
  Proof.
    iIntros "%". iLöb as "IH".
    rename H into k_in_KS.    
    iIntros "Ghost_updP #HInv" (Φ) "AU". wp_lam.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as (T0 H0)"(mcs_high & >Inv_LSM)".
    iDestruct "Inv_LSM" as (hγ0 I0 J0)"(Hglob & Hstar)".
    iDestruct "Hglob" as "(Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & #FP_r & domm_IR & domm_Iγ)".
    iModIntro. iSplitR "AU Ghost_updP". iNext. 
    iExists T0, H0. iFrame "mcs_high". 
    iExists hγ0, I0, J0. iFrame "∗ #". iModIntro.
    (** Lock the node r **)
    awp_apply lockNode_spec_high without "Ghost_updP"; try done.
    iAaccIntro with ""; try eauto with iFrame. 
    iIntros (Cr Qr)"HnP_n". iModIntro. 
    iIntros "Ghost_updP". wp_pures.
    iDestruct "HnP_n" as (γ_er γ_cr γ_qr γ_cirr es T)
                      "(node_r & #HnP_gh & HnP_frac & HnP_C & HnP_t)".
    iEval (rewrite decide_True) in "HnP_t".
    wp_apply (readClock_spec with "[HnP_t]"); try done.
    iIntros "HnP_t". wp_pures.
    wp_apply (addContents_spec with "[$node_r]"); try done.
    iIntros (b Cr')"(node_r & Hif)".
    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HCr. replace Cr'. wp_pures.
      awp_apply (unlockNode_spec_high 
          with "[] [] [HnP_gh HnP_frac HnP_C HnP_t node_r]") 
            without "Ghost_updP" ; try done.
      { iExists γ_er, γ_cr, γ_qr, γ_cirr, es, T.
        iFrame "∗#". iEval (rewrite decide_True); try done. }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro.
      iIntros "Ghost_updP". wp_pures.
      iApply ("IH" with "Ghost_updP"); try done.
    - (** Case : addContent successful **)
      (** Linearization Point: open invariant and update the resources **)
      wp_pures. wp_bind (incrementClock _)%E.
      wp_lam. iDestruct "HnP_t" as "(HnP_T & HnP_lc)".
      unfold clock. wp_load. wp_pures. 
      iInv "HInv" as (T1 H1)"(mcs_high & >Inv_LSM)".
      iDestruct "Inv_LSM" as (hγ1 I1 J1)"(Hglob & Hstar)".
      iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
      iDestruct "Hglob" as "(Ht & HI & Out_I & HR 
            & Out_J & Inf_J & Hf & Hγ & _ & domm_IR & domm_Iγ)".
      wp_store. 
      
      iDestruct "Hif" as %HCr.
      iAssert (⌜T = T1⌝)%I as %HT. 
      { iPoseProof ((own_valid_2 _ _ _) with "[$HnP_T] [$Ht]") as "H'".
        iDestruct "H'" as %H'. 
        pose proof (auth_auth_frac_op_inv _ _ _ _ H') as H''.
        inversion H''. by iPureIntro. } replace T1.
      iCombine "Ht HnP_T" as "HT".  
      iMod (own_update (γ_t) (● (MaxNat (T))) 
               (● (MaxNat (T+1))) with "HT") as "HT".
      { apply (auth_update_auth _ _ (MaxNat (T+1))).
        apply max_nat_local_update. simpl. lia. }
      iDestruct "HT" as "(Ht & HnP_T)".  

      iAssert (own γ_t (●{1 / 2} MaxNat (T + 1)) ∗ clock lc (T + 1))%I
        with "[HnP_T HnP_lc]" as "HnP_t".
      { iFrame "HnP_T". unfold clock.
        assert (#(T+1)%nat = #(T+1)) as H'.
        apply f_equal. apply f_equal. lia. 
        by rewrite H'. }  

      iPoseProof ((auth_own_incl γ_s H1 _) with "[$HH $HnP_C]") as "%".
      rename H into Cr_sub_H1. apply gset_included in Cr_sub_H1.
      iDestruct "MaxTS" as %MaxTS_H1.
      (** Re-establish maxTS for updated T and H **)
      assert (maxTS (T+1) (H1 ∪ {[(k, T)]})) as Max_ts.
      { split. intros k' t' H.
        assert (((k',t') ∈ H1) ∨ (k' = k ∧ t' = T)) as Hor by set_solver.
        destruct Hor as [Hor | Hor]. 
        destruct MaxTS_H1 as [MaxTS_H1 _].
        pose proof MaxTS_H1 k' t' Hor as Hres. lia.
        destruct Hor as [_ Hor]. replace t'. lia.
        destruct MaxTS_H1 as [_ MaxTS_H1]. lia. }       
      iAssert (⌜set_of_map Cr' ⊆ H1 ∪ {[(k,T)]}⌝)%I as %Cr_sub_H1'.
      { iPureIntro. replace Cr'.
        pose proof (set_of_map_insert_subseteq Cr k T) as H'.
        assert (set_of_map Cr = set_of_map Cr) as H'' by done. 
        set_solver. }
      (** Update the (● H) resource **)  
      iMod (own_update γ_s (● H1) (● (H1 ∪ {[(k,T)]})) with "[$HH]") as "HH".
      { apply (auth_update_auth _ _ (H1 ∪ {[(k,T)]})).
        apply gset_local_update. set_solver. }
      iMod (own_update γ_s (● (H1 ∪ {[(k, T)]})) 
             (● (H1 ∪ {[(k, T)]}) ⋅ ◯ (set_of_map Cr')) with "[$HH]") as "HH".
      { apply (auth_update_alloc _ (H1 ∪ {[(k,T)]}) (set_of_map Cr')).
        apply local_update_discrete. intros m Valid_H1 H1_eq.
        split; try done. rewrite /(ε ⋅? m) in H1_eq.
        destruct m. rewrite gset_op in H1_eq. 
        rewrite left_id in H1_eq *; intros H1_eq.
        rewrite <-H1_eq. 
        rewrite /(set_of_map Cr' ⋅? Some (H1 ∪ {[k, T]})).
        rewrite gset_op.
        rewrite /(ε) in H1_eq. unfold ucmra_unit in H1_eq.
        simpl in H1_eq.
        assert ((k,T) ∈ set_of_map Cr') as H'.
        { replace Cr'. apply set_of_map_member.
          apply lookup_insert. } 
        clear - H' Cr_sub_H1 Cr_sub_H1'. set_solver.
        exfalso. clear -H1_eq. set_solver. }
      (** Re-establish history_init **)   
      iAssert (⌜init (H1 ∪ {[(k, T)]})⌝)%I with "[Hist]" as "Hist".
      { iDestruct "Hist" as %Hist.
        unfold init. iPureIntro.
        clear -Hist k_in_KS. intros k' Hk'.
        pose proof Hist k' Hk' as H'. set_solver. }  
      iDestruct "HnP_C" as "_".  
      iDestruct "HH" as "(HH & HnP_C)".   
      iAssert (⌜r ∈ domm I1⌝)%I as %r_in_I.
      { by iPoseProof (inFP_domm _ _ _ with "[$FP_r] [$Hf]") as "H'". }
      rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
      iDestruct "Hstar" as "(H_r & Hstar')".
      iDestruct "H_r" as (br Cr'' Qr'')"(Hl_r & HnS_r)".
      iPoseProof (nodePred_lockR_true with "[$node_r] [$Hl_r]")
         as "%". subst br.
      iDestruct "HnS_r" as (γ_er' γ_cr' γ_qr' γ_cirr' es' Br Ir Jr) "HnS_r'".
      iPoseProof (nodePred_nodeShared_eq with "[$HnP_gh] [$HnP_frac] [$HnS_r']")
           as "(HnP_frac & HnS_r' &%&%&%)". subst es' Cr'' Qr''.   
      iDestruct "HnS_r'" as "(HnS_gh & HnS_frac & HnS_si & HnS_FP 
                            & HnS_cl & HnS_oc & HnS_Bn & HnS_H & HnS_star & Hφ)".


      (** Update contents-in-reach of r **)
      set (Br' := <[k := T]>Br).
      assert (Br' = <[k := T]>Br) as HBr'. try done.
      iEval (rewrite decide_True) in "HnS_H".
      iDestruct "HnS_H" as "(% & %)". 
      rename H into Br_eq_H1. rename H2 into Infz_Ir.

      iAssert (⌜contents_in_reach Br' Cr' Qr⌝)%I with "[HnS_Bn]" as "HnS_Bn".
      { iDestruct "HnS_Bn" as %H'. iPureIntro. 
        intros k0 t0 HKS. destruct (decide (k0 = k)).
        - subst k0. subst Cr' Br'.
          rewrite !lookup_insert.
          split; try done.
        - subst Cr' Br'. 
          rewrite !lookup_insert_ne; try done.
          pose proof H' k0 t0 HKS; try done. }

      
      iAssert (⌜Br' = map_of_set (H1 ∪ {[(k, T)]})⌝)%I as %Br'_eq_H1.
      { iPureIntro.
        apply map_of_set_insert_eq; try done.
        intros t. 
        destruct MaxTS_H1 as [MaxTS_H1 _].
        by pose proof MaxTS_H1 k t. }
      iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto) in "HnS_star".
      iDestruct "HnS_star" as "(Hk & HnS_star')".
      iAssert (⌜Br !!! k ≤ T⌝)%I as %Br_le_T. 
      { iPureIntro. rewrite lookup_total_alt.
        destruct (Br !! k) eqn: Hbrk; last first.
        - rewrite Hbrk. simpl; clear; lia.
        - rewrite Hbrk. simpl. 
          rewrite Br_eq_H1 in Hbrk.
          pose proof map_of_set_lookup_cases H1 k as H'.
          destruct H' as [H' | [_ H']]; last first.
          + rewrite H' in Hbrk. inversion Hbrk.
          + destruct H' as [Tk [H' [_ H'']]].
            rewrite H'' in Hbrk. inversion Hbrk.
            subst Tk.
            destruct MaxTS_H1 as [MaxTS_H1 _].
            pose proof MaxTS_H1 k u H' as H'''.
            clear -H'''; lia. }  
      iMod (own_update (γ_cirr !!! k) (● (MaxNat (Br !!! k))) 
                (● (MaxNat (Br' !!! k))) with "Hk") as "Hk".
      { apply (auth_update_auth _ _ (MaxNat (Br' !!! k))).
        apply max_nat_local_update.
        simpl. rewrite HBr'.
        by rewrite lookup_total_insert. }        
      iAssert ([∗ set] k0 ∈ KS, own (γ_cirr !!! k0) 
                  (● {| max_nat_car := Br' !!! k0 |}))%I 
          with "[HnS_star' Hk]" as "HnS_star".
      { iEval (rewrite (big_sepS_delete (_) (KS) k); last by eauto).
        iFrame "Hk".        
        iApply (big_opS_proper 
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br' !!! y |}))
             (λ y, own (γ_cirr !!! y) (● {| max_nat_car := Br !!! y |})) 
             (KS ∖ {[k]})).
        intros x Hx. assert (x ≠ k) as H' by set_solver.
        iFrame. iSplit. 
        iIntros "H". iEval (rewrite HBr') in "H".
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'') in "H".       
        iIntros "H". iEval (rewrite HBr').
        assert (<[k:=T]> Br !!! x = Br !!! x) as H''. 
        { apply lookup_total_insert_ne; try done. } 
        by iEval (rewrite H'').
        done. }
      iMod ((frac_update γ_er γ_cr γ_qr es Cr Qr es Cr' Qr) 
                  with "[$HnP_frac $HnS_frac]") as "(HnP_frac & HnS_frac)".
      iDestruct "Inf_J" as %Inf_J.
      iPoseProof ((auth_own_incl γ_J J1 Jr) with "[HR HnS_si]")
                                    as (Ro) "%". 
      { unfold singleton_interfaces_ghost_state.
        iDestruct "HnS_si" as "(_ & H' & _)". 
        iFrame. } rename H into Incl_J1.
      iPoseProof (own_valid with "HR") as "%".
      rename H into Valid_J1.
      iAssert (⌜domm Jr = {[r]}⌝)%I as "%".
      { by iDestruct "HnS_si" as "(_&_&_&H')". }
      rename H into Domm_Jr.
      iAssert (⌜φ1 es Qr⌝ ∗ ⌜φ2 r Br' Ir⌝ ∗ ⌜φ3 Br' Qr⌝ 
                ∗ ⌜φ4 r Br' Jr⌝ ∗ ⌜φ5 r Jr⌝ 
                ∗ ⌜φ6 r es Jr Qr⌝ ∗ ⌜φ7 r Ir⌝)%I
            with "[Hφ]" as "Hφ".
      { iDestruct "Hφ" as %Hφ. 
        destruct Hφ as [Hφ1 [Hφ2 [Hφ3 [Hφ4 [Hφ5 [Hφ6 Hφ7]]]]]].
        iPureIntro. repeat split; try done.
        - intros k' t' HKS Hins.
          pose proof Infz_Ir r as Infz_Ir.
          rewrite Infz_Ir in Hins.
          exfalso. clear -Hins. set_solver.
        - intros k' HKS. subst Br'. destruct (decide (k' = k)).
          + subst k'. rewrite lookup_total_insert.
            apply (Nat.le_trans _ (Br !!! k) _); try done.
            apply Hφ3; try done.
          + rewrite lookup_total_insert_ne; try done.
            apply Hφ3; try done.
        - intros k' HKS. right.
          apply (inset_monotone J1 Jr Ro); try done.
          by rewrite <-auth_auth_valid.
          pose proof Inf_J r k' HKS as Inf_J.
          by rewrite decide_True in Inf_J.
          rewrite Domm_Jr. clear. set_solver. }
            
            
      (** Linearization **)    
      iMod "AU" as (t' H1')"[MCS [_ Hclose]]".
      iAssert (⌜t' = T ∧ H1' = H1⌝)%I as "(% & %)". 
      { iPoseProof (MCS_agree with "[$MCS_auth] [$MCS]") as "(% & %)".
        by iPureIntro. } subst t' H1'. 
      iDestruct "MCS" as "(MCS◯t & MCS◯h & _)".
      iDestruct "MCS_auth" as "(MCS●t & MCS●h)".
      iMod ((auth_excl_update γ_te (T+1) T T) with "MCS●t MCS◯t") 
                                          as "(MCS●t & MCS◯t)".
      iMod ((auth_excl_update γ_he (H1 ∪ {[(k, T)]}) H1 H1) with "MCS●h MCS◯h") 
                                          as "(MCS●h & MCS◯h)".
      iCombine "MCS◯t MCS◯h" as "(MCS_t & MCS_h)".
      iCombine "MCS●t MCS●h" as "MCS_auth".
      iMod ("Hclose" with "[MCS_t MCS_h]") as "HΦ".
      iFrame. by iPureIntro.
      
      (** Use ghost_update_protocol to update Prot(H) **)
      iSpecialize ("Ghost_updP" $! T H1).
      iMod ("Ghost_updP" with "[] [$MCS_auth] [$Prot]") 
                        as "(Prot & MCS_auth)". 
      { pose proof map_of_set_lookup (H1 ∪ {[k, T]}) k T as H'.
        iPureIntro. rewrite lookup_total_alt.
        rewrite H'. by simpl. clear; set_solver.
        intros t. rewrite elem_of_union.
        clear H'. intros [H' | H'].
        destruct MaxTS_H1 as [MaxTS_H1 _].
        pose proof MaxTS_H1 k t H' as H''; clear -H''; lia.
        rewrite elem_of_singleton in H'*; intros H'.
        inversion H'. lia. }          
            
      iModIntro.
      iSplitR "HΦ node_r HnP_t HnP_C HnP_frac".
      { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}). iFrame "∗".
        iSplitR; first by iPureIntro.
        iExists hγ1, I1, J1. iFrame "∗ %".   
        rewrite (big_sepS_delete _ (domm I1) r); last by eauto.
        iSplitR "Hstar'".
        { iExists true, Cr', Qr. iFrame.
          iExists γ_er, γ_cr, γ_qr, γ_cirr, es, Br', Ir, Jr.
          iFrame "∗#". iEval (rewrite decide_True). 
          iFrame "%∗". }        
        iApply (big_sepS_mono 
                  (λ y, ∃ (bn : bool) (Cn Qn : gmap K natUR),
                          lockR bn y (nodePred γ_gh γ_t γ_s lc r y Cn Qn)
                        ∗ nodeShared γ_I γ_J γ_f γ_gh r y Cn Qn H1)%I
                  (λ y, ∃ (bn : bool) (Cn Qn : gmap K natUR),
                          lockR bn y (nodePred γ_gh γ_t γ_s lc r y Cn Qn)
                        ∗ nodeShared γ_I γ_J γ_f γ_gh r y Cn Qn 
                                                (H1 ∪ {[(k, T)]}))%I
                  (domm I1 ∖ {[r]})); try done.
        intros y y_dom. assert (y ≠ r) as Hy by set_solver. iFrame.
        iIntros "Hstar". iDestruct "Hstar" as (b C Q)"(Hl & HnS)".
        iExists b, C, Q. iFrame. 
        iDestruct "HnS" as (γ_e γ_c γ_q γ_cir esy By Iy Ry)
                    "(HnS_gh & domm_γcir & HnS_frac & HnS_si & HnS_FP 
                              & HnS_cl & HnS_oc & HnS_Bn & HnS_H & HnS_star 
                              & Hφ0 & Hφ2 & Hφ3 & Hφ4 & Hφ5 & Hφ7)".
        iExists γ_e, γ_c, γ_q, γ_cir, esy, By, Iy, Ry. iFrame.
        destruct (decide (y = r)); try done. } 
      wp_pures. 
      (** Unlock node r **) 
      awp_apply (unlockNode_spec_high with "[] [] 
        [HnP_t HnP_C HnP_frac node_r]") without "HΦ"; try done.   
      iExists γ_er, γ_cr, γ_qr, γ_cirr, es, (T + 1).
      iFrame "∗#". by iEval (rewrite decide_True).
      iAaccIntro with ""; try done.
      iIntros "_". iModIntro; iIntros "HΦ"; try done.
  Qed.


End multicopy_lsm_upsert.
