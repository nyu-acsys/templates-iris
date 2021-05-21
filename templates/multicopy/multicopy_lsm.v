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
Parameter atCapacity: val.
Parameter chooseNext: val.
Parameter mergeContents: val.
Parameter allocNode: val.
Parameter insertNode: val.

(** Template algorithms *)

Definition traverse : val :=
  rec: "t_rec" "n" "k" :=
    lockNode "n" ;;
    match: (inContents "n" "k") with
      SOME "t" => unlockNode "n";; "t"
    | NONE => match: (findNext "n" "k") with
                SOME "n'" => unlockNode "n" ;; "t_rec" "n'" "k"
              | NONE => unlockNode "n" ;; #0 end end.
              
Definition search (r: Node) : val := 
  λ: "k", traverse #r "k".
  
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

Definition compact (r: Node) : val :=
  rec: "compact_rec" "n" :=
    lockNode "n" ;;
    if: atCapacity "n" then
      match: (chooseNext "n") with
        SOME "m" =>
          lockNode "m" ;;
          mergeContents "n" "m" ;;
          unlockNode "n" ;;
          unlockNode "m" ;;
          "compact_rec" "m"
      | NONE =>
          let: "m" := allocNode #() in
          insertNode #r "n" "m";;
          mergeContents "n" "m" ;;
          unlockNode "n" ;;
          unlockNode "m";;
          "compact_rec" "m" end
    else
      unlockNode "n".          


(** Proof setup **)

Definition esT : Type := gmap Node (gset K).
Canonical Structure esRAC := leibnizO esT.

(* RAs used in proof *)

Definition prod4O A B C D :=
  prodO (prodO (prodO A B) C) D.

Definition per_node_gl :=
    agreeR 
      (prod4O gnameO gnameO gnameO (gmapO K gnameO)).

Definition ghost_heapUR := gmapUR Node $ per_node_gl.

Definition flow_KTR := authR (multiset_flowint_ur KT).
Definition flow_KR := authR (multiset_flowint_ur K).
Definition set_nodeR := authR (gsetUR Node).
Definition frac_contR := frac_agreeR (gmapUR K natUR).
Definition frac_esR := frac_agreeR (esRAC).
Definition timeR := authR (max_natUR).
Definition ghR := authR $ ghost_heapUR.

Class multicopy_lsmG Σ := MULTICOPY_LSM {
                            multicopy_lsm_flow_KTG :> inG Σ flow_KTR;
                            multicopy_lsm_flow_KG :> inG Σ flow_KR;
                            multicopy_lsm_set_nodeG :> inG Σ set_nodeR;
                            multicopy_lsm_frac_contG :> inG Σ frac_contR;
                            multicopy_lsm_frac_esG :> inG Σ frac_esR;
                            multicopy_lsm_timeG :> inG Σ timeR;
                            multicopy_lsm_ghG :> inG Σ ghR;
                      }.

Definition multicopy_lsmΣ : gFunctors :=
  #[GFunctor flow_KTR; GFunctor flow_KR; GFunctor set_nodeR;
    GFunctor frac_contR; GFunctor frac_esR; 
    GFunctor timeR; GFunctor ghR ].

Instance subG_multicopy_lsmΣ {Σ} : subG multicopy_lsmΣ Σ → multicopy_lsmG Σ.
Proof. solve_inG. Qed.

Section multicopy_lsm.
  Context {Σ} `{!heapG Σ, !multicopyG Σ, !multicopy_lsmG Σ}.
  Notation iProp := (iProp Σ).
  Local Notation "m !1 i" := (nzmap_total_lookup i m) (at level 20).

  (** Assumptions on the implementation made by the template algorithms. *)

  (* The node predicate is specific to each template implementation. See GRASShopper files
     multicopy-lsm.spl for the concrete definition. *)
  Parameter node : Node → Node → esT → (gmap K natUR) → iProp.

  Parameter nodeSpatial : Node → iProp.
  
  Parameter needsNewNode : Node → Node → esT → (gmap K nat) → iProp. 

  (* The following assumption is justified by the fact that GRASShopper uses a
   * first-order separation logic. *)
  Parameter node_timeless_proof : ∀ r n es C, Timeless (node r n es C).
  Global Instance node_timeless r n es C: Timeless (node r n es C).
  Proof. apply node_timeless_proof. Qed.

  (* The following hypothesis are proved as a GRASShopper lemma in
   * multicopy-lsm.spl *)
  Parameter node_sep_star: ∀ r n es C es' C',
    node r n es C ∗ node r n es' C' -∗ False.

  Parameter node_es_disjoint: ∀ r n es C,
    node r n es C -∗ ⌜∀ n1 n2, n1 ≠ n2 → es !!! n1 ∩ es !!! n2 = ∅⌝.  

  Parameter node_es_empty: ∀ r n es C,
    node r n es C -∗ ⌜es !!! r = ∅ ∧ es !!! n = ∅⌝.

  (** The LSM multicopy structure invariant *)
  
  Definition inFP γ_f (n: Node) : iProp := own γ_f (◯ {[n]}).
  
  Definition closed γ_f (es: esT) : iProp := ∀ n, ⌜es !!! n  ≠ ∅⌝ → inFP γ_f n.

  Definition inflow_zero (I: multiset_flowint_ur KT) := ∀ n, inset KT I n = ∅. 

  Definition outflow_zero (I: multiset_flowint_ur KT) := out_map I = ∅. 

  Definition outflow_zero_J (I: multiset_flowint_ur K) := out_map I = ∅. 

  Definition inflow_J (R: multiset_flowint_ur K) r := 
    ∀ n k, k ∈ KS → if decide (n = r) then in_inset K k R n else ¬ in_inset K k R n. 

  Definition outflow_le_1 (I: multiset_flowint_ur KT) :=
    ∀ n kt, out I n !1 kt ≤ 1.

  Definition outflow_constraint_I (In: multiset_flowint_ur KT) (es: esT) 
                          (Qn: gmap K natUR) := 
    ∀ n' k t, k ∈ KS → ((k,t) ∈ outset KT In n' ↔ 
                          k ∈ es !!! n' ∧ (Qn !! k = Some t)).
                          
  Definition outflow_constraint_J (Rn: multiset_flowint_ur K) (es: esT) n := 
    ∀ n' k, k ∈ KS → (k ∈ outset K Rn n' ↔ k ∈ es !!! n' ∧ k ∈ inset K Rn n).

  (* This constraint is implicit in the paper. We track B_n 
     explicitly as ghost state here. That is the following 
     captures the definition of B_n in terms of C_n/Q_n given 
     in the paper. *)
  Definition contents_in_reach (Bn Cn Qn: gmap K natUR) :=
              ∀ k t, k ∈ KS → ((Cn !! k = Some t → Bn !! k = Some t)
                 ∧ (Cn !! k = None → Bn !! k = Qn !! k)). 

  (** ϕ_1 in the paper *)
  Definition φ1 (es: esT) (Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → ((∀ n', k ∉ es !!! n') → Qn !! k = None).

  (** ϕ_2 in the paper *)
  Definition φ2 n (Bn: gmap K natUR) In := 
              ∀ k t, k ∈ KS → ((k,t) ∈ inset KT In n → Bn !!! k = t).

  (** ϕ_3 in the paper *)
  Definition φ3 (Bn Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → (Qn !!! k ≤ Bn !!! k).            

  (** ϕ_4 in the paper *)
  Definition φ4 n (Bn: gmap K natUR) Jn :=
              ∀ k, k ∈ KS → (Bn !! k = None ∨ k ∈ inset K Jn n).

  (** ϕ_5 in the paper *)
  Definition φ5 n (Jn: multiset_flowint_ur K) := 
              ∀ k, inf Jn n !1 k ≤ 1.

  (** The following two constraints are inductive consequences of ϕ1..ϕ5. We track them explicitly in the invariant for convenience. *)
  Definition φ6 n (es: esT) (Jn: multiset_flowint_ur K) (Qn: gmap K natUR) :=
              ∀ k, k ∈ KS → ((∃ n', k ∈ es !!! n') ∧ k ∈ inset K Jn n 
                          → k ∈ dom (gset K) Qn).              

  Definition φ7 (n: Node) (In: multiset_flowint_ur KT) := 
              ∀ kt, inf In n !1 kt ≤ 1.

  
  Definition f_merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) := 
                    λ k o1 o2, 
                      if (decide (Cn !! k ≠ None)) then o1
                      else if (decide (k ∈ Es)) then o2 
                           else (None: option nat).
  
  Global Instance f_merge_diag_none Cn Es Cm k : DiagNone (f_merge Cn Es Cm k).
  Proof.
    unfold DiagNone. unfold f_merge.
    destruct (decide (Cn !! k ≠ None)); try by simpl.
    destruct (decide (k ∈ Es)); try by simpl.
  Qed.  
  
  Definition merge (Cn: gmap K nat) (Es: gset K) (Cm: gmap K nat) 
                          : (gmap K nat) :=
             gmap_imerge (f_merge Cn Es Cm) Cn Cm.            


  Definition frac_ghost_state γ_en γ_cn γ_qn (es: esT)
                                  (Cn Qn: gmap K natUR): iProp :=
      own (γ_en) (to_frac_agree (1/2) (es))
    ∗ own (γ_cn) (to_frac_agree (1/2) (Cn))
    ∗ own (γ_qn) (to_frac_agree (1/2) (Qn)).

  Definition singleton_interfaces_ghost_state (γ_I γ_J: gname) (n: Node) 
                  (In: multiset_flowint_ur KT) (Jn: multiset_flowint_ur K) : iProp :=
      own γ_I (◯ In)
    ∗ own γ_J (◯ Jn)
    ∗ ⌜domm In = {[n]}⌝
    ∗ ⌜domm Jn = {[n]}⌝.
    
  Definition outflow_constraints n In Jn es Qn : iProp :=
      ⌜outflow_constraint_I In es Qn⌝
    ∗ ⌜outflow_constraint_J Jn es n⌝
    ∗ ⌜outflow_le_1 In⌝.

  Definition clock lc (t: nat) : iProp := lc ↦ #t.
  
  Definition ghost_loc γ_en γ_cn γ_qn (γ_cirn: gmap K gnameO) : per_node_gl := 
        to_agree (γ_en, γ_cn, γ_qn, γ_cirn).

  Definition nodePred' γ_gh γ_t γ_s lc r n (Cn Qn : gmap K natUR) 
                        γ_en γ_cn γ_qn γ_cirn es t: iProp :=
      node r n es Cn
    ∗ own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]})  
    ∗ frac_ghost_state γ_en γ_cn γ_qn es Cn Qn
    ∗ own γ_s (◯ set_of_map Cn)
    ∗ (if decide (n = r) then own γ_t (●{1/2} MaxNat t) ∗ clock lc t else True)%I.

  (** Predicate N_L in the paper *)
  Definition nodePred γ_gh γ_t γ_s lc r n (Cn Qn : gmap K natUR) : iProp :=
    ∃ γ_en γ_cn γ_qn γ_cirn es t, nodePred' γ_gh γ_t γ_s lc r n Cn Qn 
                                             γ_en γ_cn γ_qn γ_cirn es t.

  Definition nodeShared' (γ_I γ_J γ_f: gname) γ_gh r n 
          (Cn Qn : gmap K natUR) H γ_en γ_cn γ_qn γ_cirn 
          es Bn In Jn: iProp :=
      own γ_gh (◯ {[n := ghost_loc γ_en γ_cn γ_qn γ_cirn]})
    ∗ frac_ghost_state γ_en γ_cn γ_qn es Cn Qn  
    ∗ singleton_interfaces_ghost_state γ_I γ_J n In Jn 
    ∗ inFP γ_f n
    ∗ closed γ_f es
    ∗ outflow_constraints n In Jn es Qn
    ∗ ⌜contents_in_reach Bn Cn Qn⌝
    ∗ (if decide (n = r) then ⌜Bn = map_of_set H⌝ ∗ ⌜inflow_zero In⌝ else True)%I
    ∗ ([∗ set] k ∈ KS, own (γ_cirn !!! (k)) (● (MaxNat (Bn !!! k))))
    ∗ ⌜φ1 es Qn⌝ ∗ ⌜φ2 n Bn In⌝ ∗ ⌜φ3 Bn Qn⌝ ∗ ⌜φ4 n Bn Jn⌝ 
    ∗ ⌜φ5 n Jn⌝ ∗ ⌜φ6 n es Jn Qn⌝ ∗ ⌜φ7 n In⌝.

  (** Predicate N_S in the paper *)
  Definition nodeShared (γ_I γ_J γ_f: gname) γ_gh r n 
          (Cn Qn : gmap K natUR) H: iProp :=
    ∃ γ_en γ_cn γ_qn γ_cirn es Bn In Jn, 
        nodeShared' γ_I γ_J γ_f γ_gh r n Cn Qn H 
                    γ_en γ_cn γ_qn γ_cirn es Bn In Jn.
                    
  
  (** Predicate G in the paper *)
  Definition global_state (γ_t γ_I γ_J γ_f γ_gh: gname) (r: Node) (t: nat) 
          (hγ: gmap Node per_node_gl) (I: multiset_flowint_ur KT) 
          (J: multiset_flowint_ur K) : iProp :=
      own γ_t (●{1/2} MaxNat t)
    ∗ own γ_I (● I) ∗ ⌜outflow_zero I⌝
    ∗ own γ_J (● J) ∗ ⌜outflow_zero_J J⌝ ∗ ⌜inflow_J J r⌝
    ∗ own γ_f (● domm I)
    ∗ own γ_gh (● hγ)
    ∗ inFP γ_f r
    ∗ ⌜domm I = domm J⌝ 
    ∗ ⌜domm I = dom (gset Node) hγ⌝.

  Definition Inv_LSM γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H : iProp :=
    ∃ hγ
      (I: multiset_flowint_ur KT) (R: multiset_flowint_ur K),
      global_state γ_t γ_I γ_J γ_f γ_gh r t hγ I R
    ∗ ([∗ set] n ∈ (domm I), ∃ (bn: bool) Cn Qn, 
        (lockR bn n (nodePred γ_gh γ_t γ_s lc r n Cn Qn))
        ∗ (nodeShared γ_I γ_J γ_f γ_gh r n Cn Qn H))%I.  

  Global Instance Inv_LSM_timeless γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H:
    Timeless (Inv_LSM γ_s γ_t γ_I γ_J γ_f γ_gh lc r t H).
  Proof.
    rewrite /Inv_LSM.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    apply big_sepS_timeless.
    repeat (intros; apply bi.exist_timeless; intros).
    apply bi.sep_timeless; try apply _.
    destruct x3; try apply _.    
    repeat apply bi.sep_timeless; try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x2 = r)); try apply _.
    repeat apply bi.sep_timeless; try apply _.
    repeat (apply bi.exist_timeless; intros).
    repeat apply bi.sep_timeless; try apply _.
    destruct (decide (x2 = r)); try apply _.
  Qed.

  (** Helper functions specs *)

  (* The following specs are proved for each implementation in GRASShopper
   * (see multicopy-lsm.spl *)
    
  Parameter inContents_spec : ∀ r n esn (Cn: gmap K natUR) (k: K),
     ⊢ ({{{ node r n esn Cn }}}
           inContents #n #k
       {{{ (t: option nat), 
              RET (match t with Some t => SOMEV #t | None => NONEV end);
                  node r n esn Cn ∗ ⌜Cn !! k = t⌝ }}})%I.

  Parameter findNext_spec : ∀ r n esn (Cn: gmap K natUR) (k: K),
     ⊢ ({{{ node r n esn Cn }}}
           findNext #n #k
       {{{ (n1: option Node),
              RET (match n1 with Some n1 => SOMEV #n1 | None => NONEV end);
                  node r n esn Cn 
                  ∗ (match n1 with Some n1 => ⌜k ∈ esn !!! n1⌝ 
                                 | None => ⌜∀ n1, k ∉ esn !!! n1⌝ end) }}})%I.

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

  Parameter addContents_spec : ∀ r n esn (Cn: gmap K natUR) (k: K) (t:nat),
     ⊢ ({{{ node r n esn Cn ∗ ⌜n = r⌝ }}}
           addContents #r #k #t
       {{{ (succ: bool) (Cn1: gmap K natUR),
              RET #succ;
                  node r n esn Cn1 ∗ if succ then ⌜Cn1 = <[k := t]> Cn⌝ 
                                else ⌜Cn1 = Cn⌝ }}})%I.

  Parameter atCapacity_spec : ∀ r n esn (Cn: gmap K natUR),
     ⊢ ({{{ node r n esn Cn }}}
           atCapacity #n
       {{{ (b: bool), RET #b;
           node r n esn Cn }}})%I.

  Parameter chooseNext_spec : ∀ r n esn (Cn: gmap K natUR),
     ⊢ ({{{ node r n esn Cn }}}
           chooseNext #n
       {{{ (n1: option Node), 
              RET (match n1 with Some n1 => SOMEV #n1 | None => NONEV end);
           node r n esn Cn 
           ∗ (match n1 with Some n1 => ⌜esn !!! n1 ≠ ∅⌝ 
                          | None => needsNewNode r n esn Cn end) }}})%I.  
    
  Parameter mergeContents_spec : ∀ r n m esn esm (Cn Cm: gmap K natUR),
     ⊢ ({{{ node r n esn Cn ∗ node r m esm Cm ∗ ⌜esn !!! m ≠ ∅⌝ }}}
           mergeContents #n #m
       {{{ Cn' Cm', RET #();
           node r n esn Cn' ∗ node r m esm Cm' 
           ∗ ⌜set_of_map Cn' ⊆ set_of_map Cn⌝
           ∗ ⌜set_of_map Cm' ⊆ set_of_map Cn ∪ set_of_map Cm⌝
           ∗ ⌜set_of_map Cn ∩ set_of_map Cm' ## set_of_map Cn'⌝
           ∗ ⌜dom (gset K) Cm ⊆ dom (gset K) Cm'⌝
           ∗ ⌜merge Cn (esn !!! m) Cm = merge Cn' (esn !!! m) Cm'⌝ }}})%I.

  Parameter allocNode_spec :
     ⊢ ({{{ True }}}
           allocNode #()
       {{{ (m: Node) (l:loc), RET #m; 
            nodeSpatial m 
            ∗ ⌜lockLoc m = l⌝ 
            ∗ l ↦ #true }}})%I.
            
  Parameter insertNode_spec : ∀ r n m esn Cn,
    ⊢ {{{ node r n esn Cn ∗ needsNewNode r n esn Cn 
          ∗ nodeSpatial m ∗ ⌜m ≠ r⌝ }}}
          insertNode #r #n #m
      {{{ esn1 esm Cm, RET #();
          node r n esn1 Cn ∗ node r m esm Cm
          ∗ ⌜esn1 = <[m:=esn1 !!! m]> esn⌝
          ∗ ⌜esn1 !!! m ≠ ∅⌝
          ∗ ⌜Cm = ∅⌝ ∗ ⌜esm = ∅⌝ }}}.


End multicopy_lsm.