From iris.algebra Require Import excl auth frac cmra gmap agree gset numbers.
From iris.algebra.lib Require Import frac_agree.
From iris.heap_lang Require Export notation locations lang.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export atomic.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode par.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "All".
Require Export multicopy_df auth_ext.
Require Export multicopy_util.

Section multicopy_df_upsert.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_dfG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  Lemma nodePred_lockR_true γ_gh γ_t γ_s lc r bn n Cn Cn' Qn' : 
    node r n Cn -∗ 
      lockR bn n (nodePred γ_gh γ_t γ_s lc r n Cn' Qn') -∗
        ⌜bn = true⌝.
  Proof.
    
    iIntros "node Hl_n".
    destruct bn; try done.
    iDestruct "Hl_n" as "(Hl & HnP')".
    iDestruct "HnP'" as "(n' & _)".
    iExFalso. iApply (node_sep_star r n). iFrame.
  Qed.          

  Lemma upsert_spec N γ_te γ_he γ_s Prot γ_t γ_cr γ_cd γ_d lc r d (k: K) :
    ⊢ ⌜k ∈ KS⌝ -∗ 
        (ghost_update_protocol N γ_te γ_he Prot k) -∗ 
        mcs_inv N γ_te γ_he γ_s Prot 
          (Inv_DF γ_s γ_t γ_cr γ_cd γ_d lc r d) -∗
            <<< ∀ t H, MCS γ_te γ_he t H >>> 
                   upsert lc r #k @ ⊤ ∖ (↑(mcsN N))
            <<< MCS γ_te γ_he (t + 1) (H ∪ {[(k,t)]}), RET #() >>>.
  Proof.
    iIntros "%".
    rename H into k_in_KS.
    (* perform Löb induction by generating a hypothesis IH : ▷ goal *)
    iLöb as "IH".
    iIntros "Ghost_updP #HInv" (Φ) "AU". wp_lam.
    iApply fupd_wp. 
    (** Open invariant to establish root node in footprint **)
    iInv "HInv" as (T0 H0)"(mcs_high & >Inv_DF)".
    iDestruct "Inv_DF" as (Inv_Cr Inv_Cd)"(Hglob & Hstar)".
    iDestruct "Hstar" as "(#r_not_d & #Hcir & Hkeyset & Hstar)".
    iDestruct "Hstar" as "(root_pred & root_own & d_pred & d_own)".
    iModIntro. iSplitR "AU Ghost_updP". iNext. 
    iExists T0, H0. iFrame "mcs_high". 
    iExists Inv_Cr, Inv_Cd. iFrame "∗ #".
    
    iModIntro.
    awp_apply lockNode_spec_high without "Ghost_updP"; try done.
    iPureIntro. auto.
    (** Lock the node r **)
    iAaccIntro with ""; try eauto with iFrame.
     
    iIntros (γ_cn Cr T) "HnP_n". iModIntro. 
    iIntros "Ghost_updP". wp_pures.
    iDestruct "HnP_n" as "(HnP_n & #r_is_locked)".
    iDestruct "HnP_n" as "(node_r & HnP_C & HnP_frac & HnP_t)".
    iEval (rewrite decide_True) in "HnP_t".
    wp_apply (readClock_spec with "[HnP_t]"); try done.
    iIntros "HnP_t". wp_pures.
    wp_apply (addContents_spec with "[$node_r]"); try done.
    iIntros (b Cr') "(node_r & Hif)".


    (** Case analysis on whether addContents is successful **)
    destruct b; last first.
    - (** Case : addContents fails. Unlock root node and apply 
                 inductive hypothesis IH **) 
      iDestruct "Hif" as %HCr. replace Cr'. wp_pures.
      awp_apply (unlockNode_spec_high 
          with "[] [] [HnP_frac HnP_C HnP_t node_r ]") 
            without "Ghost_updP" ; try done.
      { 
        iFrame.
        iEval (rewrite decide_True); try done.
      }
      iAaccIntro with ""; try eauto with iFrame.
      iIntros "_". iModIntro.
      iIntros "Ghost_updP". wp_pures.
      iApply ("IH" with "Ghost_updP"); try done.
    - (** Case : addContent successful **)
      (** Linearization Point: open invariant and update the resources **)
      wp_pures. wp_bind (incrementClock _)%E.
      wp_lam. iDestruct "HnP_t" as "(HnP_T & HnP_lc)".
      unfold clock. wp_load. wp_pures. 
      iInv "HInv" as (T1 H1)"(mcs_high & >Inv_DF)".
      iDestruct "Inv_DF" as (Inv_Cr_2 Inv_Cd_2)"(Ht & Hstar)".

      iDestruct "Hstar" as "(#r_not_d_2 & #Hcir_2 & Hkeyset & Hstar)".
      iDestruct "Hstar" as "(root_pred & root_own & d_pred & d_own)".

      iDestruct "root_pred" as (br) "root_pred".
      iDestruct "d_pred" as (bd) "d_pred".

      iDestruct "mcs_high" as "(>MCS_auth & >HH & >Hist & >MaxTS & Prot)".
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
      iDestruct "HnP_C" as "Hown_Cr".  
      iDestruct "HH" as "(HH & HnP_C)".   

      rewrite (big_sepS_delete _ KS k); last by eauto.
      iDestruct "Hist" as %hist.

      iPoseProof (nodePred_lockR_true with "[$node_r] [root_pred]")
         as "%". iFrame.
        
      (** Update contents-in-reach of r **)
      iAssert (⌜map_of_set (H1 ∪ {[k, T]}) = <[k:=T]> (map_of_set H1)⌝)%I as %Htrans_union.
      {
        iPureIntro.
        pose proof map_of_set_insert_eq as mos_eq.
        set C := (map_of_set H1).
        specialize mos_eq with C k T H1.
        elim mos_eq; try done.
        unfold maxTS in MaxTS_H1.
        destruct MaxTS_H1 as [MaxTS T_gt_0].
        intro t.
        specialize MaxTS with k t.
        done.
      }

      iAssert (⌜γ_cn = γ_cr⌝)%I as %gamma_cn_cr.
      {

        iDestruct "r_is_locked" as %r_is_locked.
        iDestruct "r_not_d" as %r_not_d.
        destruct r_is_locked as [ r_is_locked | r_not_locked].
        destruct r_is_locked as [ r_is_r  gh_cn_cr ]. done.
        destruct r_not_locked as [ r_is_d  gh_cn_cr ]. done.
      }
      subst γ_cn.
      
      iAssert (⌜Cr = Inv_Cr_2⌝)%I as %HCr_equiv.
      {
        
        iPoseProof (own_valid_2 _ _ _ with "[$root_own] [$HnP_frac]") as "#HCr_equiv".
        iDestruct "HCr_equiv" as %HCr_equiv.
        apply frac_agree_op_valid in HCr_equiv.
        destruct HCr_equiv as [_ HCr_equiv].
        apply leibniz_equiv_iff in HCr_equiv.
        iPureIntro. done.
      }
      subst Cr.

      iAssert (⌜cir (H1 ∪ {[k, T]}) Cr' Inv_Cd_2 ⌝)%I with "[Hcir_2]" as "Hcir_2'".
      { 
        iDestruct "Hcir_2" as %H2'.
        iPureIntro. 
        intros k0 t0.
          rewrite -> Htrans_union.
        destruct (decide (k0 = k)).
        - subst k0. subst Cr'.
          rewrite !lookup_insert.
          split; try done. 
        - subst Cr'. 
          rewrite !lookup_insert_ne; try done.
      }

      iAssert (⌜(map_of_set H1) !!! k ≤ T⌝)%I as %H_le_T. 
      {
        iPureIntro.
        rewrite lookup_total_alt.
        destruct ((map_of_set H1) !! k) eqn: hist_has_k.
        - simpl.
          unfold maxTS in MaxTS_H1.
          destruct MaxTS_H1 as [MaxTS_H1 T_not_zero].
          pose proof map_of_set_lookup_cases H1 k as H'.
          destruct H' as [H' | [_ H']]; last first.
          + rewrite H' in hist_has_k. inversion hist_has_k.
          + destruct H' as [Tk [H' [_ H'']]].
            rewrite H'' in hist_has_k. inversion hist_has_k.
            subst Tk.
            pose proof MaxTS_H1 k n H' as H'''.
            clear -H'''; lia.
        - simpl. lia.
      }

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
        inversion H'. lia.
      }          
      

      (* Combine fractional ownerships of Cr. *)
      iCombine "HnP_frac root_own" as "root_own".
      iEval (rewrite <-frac_agree_op) in "root_own".
      iEval (rewrite Qp_half_half) in "root_own".

      (* Use combined ownerships to update Cr -> Cr'. *)
      iMod ((own_update (γ_cr) (to_frac_agree 1 Inv_Cr_2)
              (to_frac_agree 1 Cr')) with "[$root_own]") as "root_update".
      { apply cmra_update_exclusive.
        unfold valid, cmra_valid. simpl. unfold prod_valid_instance.
        split; simpl; try done. }

      (* Break apart ownerships to be used separately. *)
      iEval (rewrite <- Qp_half_half) in "root_update".
      iEval (rewrite frac_agree_op) in "root_update".
      iDestruct "root_update" as "(root_frac_1 & root_frac_2)".
        
      iModIntro.
      iSplitR "HΦ node_r HnP_t HnP_C root_frac_1".

      { iNext. iExists (T+1), (H1 ∪ {[(k, T)]}). iFrame "∗".
        iSplitR; first by iPureIntro.
        iExists Cr', Inv_Cd_2.
        iSplitL "Hcir".
        iFrame "r_not_d".
        rewrite (big_sepS_delete _ (KS) k); last by eauto.

        iFrame.
        iSplitR. iFrame "Hcir_2'".
        
        iSplitL "root_pred". 
        {
          iExists br. 
          subst br.
          iFrame.
        }
        {
          iExists bd.
          unfold lockR. iDestruct "d_pred" as "[d_lock d_pred]".
          iFrame. destruct bd; try done.
          unfold nodePred.
          iDestruct "d_pred" as "(d_node & d_set & d_own & d_if)".
          iFrame.
          iDestruct "r_not_d" as %r_not_d.
          destruct (decide (d = r)); try done.
        }
      }
  
      wp_pures. 
      (** Unlock node r **) 
      awp_apply (unlockNode_spec_high with "[] [] 
        [HnP_t HnP_C node_r root_frac_1]") without "HΦ"; try done.
      iFrame "∗#".
      rewrite decide_True; try done. 
      iAaccIntro with ""; try done.
      iIntros "_". 
      iModIntro. iIntros "HΦ". try done.
  Qed.
  
End multicopy_df_upsert.