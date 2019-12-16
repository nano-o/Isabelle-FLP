section{* FLPSystem *}

text {*
  \file{FLPSystem} extends \file{AsynchronousSystem} with concepts of consensus
  and decisions. It develops a concept of non-uniformity regarding pending
  decision possibilities, where non-uniform configurations can always
  reach other non-uniform ones.
*}

theory FLPSystem
imports AsynchronousSystem ListUtilities
begin

subsection{* Locale for the FLP consensus setting *}

locale flpSystem =
  asynchronousSystem trans sends start    
    for trans :: "'p::finite \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow>'s"
    and sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset"
    and start :: "'p \<Rightarrow> 's" +
assumes minimalProcs: "card Proc \<ge> 2"
    and finiteSends: "finite {v. v \<in># (sends p s m)}"
    and noInSends: " <p2, inM v> \<notin># sends p s m"
begin

subsection{* Decidedness and uniformity of configurations*}

abbreviation vDecided ::
  "bool \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "vDecided v cfg \<equiv> (<\<bottom>, outM v> \<in># msgs cfg)"

abbreviation decided ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "decided cfg \<equiv> (\<exists>v . vDecided v cfg)"

definition pSilDecVal ::
  "bool \<Rightarrow> 'p \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "pSilDecVal v p c \<equiv> 
    (\<exists> c'::('p, 'v, 's) configuration . (withoutQReachable c {p} c') 
    \<and> vDecided v c')"

definition pSilentDecisionValues ::
  "'p \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool set" ("val[_,_]")
where 
  pSilentDecisionValues_def[simp]:"val[p, c] \<equiv> {v. pSilDecVal v p c}"

definition vUniform ::
  "bool \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "vUniform v c \<equiv> (\<forall>p. val[p,c] = {v})"

abbreviation nonUniform ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "nonUniform c \<equiv>
    \<not>(vUniform False c) \<and> 
    \<not>(vUniform True c)"

subsection{* Agreement, validity, termination *}

text{*
  Völzer defines consensus in terms of the classical notions
  of agreement, validity, and termination. The proof then mostly applies a
  weakened notion of termination, which we refer to as ,,pseudo termination''.
*}

definition agreement ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "agreement c \<equiv> 
    (\<forall>v1. (<\<bottom>, outM v1> \<in># msgs c)
      \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># msgs c)
        \<longleftrightarrow> v2 = v1))"

definition agreementInit ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "agreementInit i c \<equiv> 
    initial i \<and> reachable i c \<longrightarrow> 
      (\<forall>v1. (<\<bottom>, outM v1> \<in># msgs c) 
        \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># msgs c) 
          \<longleftrightarrow> v2 = v1))"

definition validity ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "validity i c \<equiv>
    initial i \<and> reachable i c \<longrightarrow> 
      (\<forall>v. (<\<bottom>, outM v> \<in># msgs c) 
        \<longrightarrow> (\<exists>p. (<p, inM v> \<in># msgs i)))"

text{*
  The termination concept which is implied by the concept of "pseudo-consensus"
  in the paper.
*}
definition terminationPseudo ::
  "nat \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> 'p set \<Rightarrow> bool"
where
  "terminationPseudo t c Q \<equiv> ((initReachable c \<and> card Q + t \<ge> card Proc) 
    \<longrightarrow> (\<exists>c'. qReachable c Q c' \<and> decided c'))"

subsection {* Propositions about decisions *}

text{*
  For every process \var{p} and every configuration that is reachable from an
  initial configuration (i.e. \isb{initReachable} \var{c}) we have
  $\var{val(p,c)} \neq \emptyset$.

  This follows directly from the definition of \var{val} and the definition of
  \isb{terminationPseudo}, which has to be assumed to ensure that there is a
  reachable configuration that is decided.
  
  \voelzer{Proposition 2(a)}
*}
lemma DecisionValuesExist:
assumes
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Reachable: "initReachable c"      
shows
  "val[p,c] \<noteq> {}"  
proof -
  from Termination
    have "(initReachable c \<and> card Proc \<le> card (UNIV - {p}) + 1) 
      \<longrightarrow> (\<exists>c'. qReachable c (UNIV-{p}) c' \<and> (\<exists>v. <\<bottom>, outM v> \<in># msgs c' ))"
    unfolding terminationPseudo_def by simp
  with Reachable minimalProcs finite_UNIV
    have "\<exists>c'. qReachable c (UNIV - {p}) c' \<and> (\<exists>v.  <\<bottom>, outM v> \<in># msgs c')"
    unfolding terminationPseudo_def initReachable_def by simp
  thus ?thesis  using Reachable by (auto simp add:pSilDecVal_def)
qed

text{*
  The lemma \isb{DecidedImpliesUniform} proves that every \isb{vDecided}
  configuration \var{c} is also \isb{vUniform}. Völzer claims that this
  follows directly from the definitions of \isb{vDecided} and \isb{vUniform}.
  But this is not quite enough: One must also assume \isb{terminationPseudo}
  and \isb{agreement} for all reachable configurations.

  \voelzer{Proposition 2(b)}
*}
lemma DecidedImpliesUniform:
assumes
  Reachable:"initReachable c" and
  AllAgree: "\<forall> cfg . reachable c cfg \<longrightarrow> agreement cfg" and
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  VDec: "vDecided v c"
shows
  "vUniform v c"
  using AllAgree VDec unfolding agreement_def vUniform_def pSilDecVal_def pSilentDecisionValues_def
proof - 
  assume 
    Agree: "\<forall>cfg. reachable c cfg \<longrightarrow>
      (\<forall>v1. <\<bottom>, outM v1> \<in># msgs cfg 
      \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># msgs cfg ) = (v2 = v1)))" and 
    vDec: "<\<bottom>, outM v> \<in># msgs c"
  show 
    "(\<forall>p. {v. \<exists>c'. qReachable c (Proc - {p}) c' \<and> 
      <\<bottom>, outM v> \<in>#  msgs c'} = {v})" 
  proof clarify
    fix p 
    have "val[p,c] \<noteq> {}" using Termination DecisionValuesExist vDec Reachable by blast 
    hence NotEmpty: "{v. \<exists>c'. qReachable c (UNIV - {p}) c' 
      \<and> initReachable c' \<and>  (<\<bottom>, outM v>) \<in># msgs c'} \<noteq> {}"
      using pSilDecVal_def Reachable asynchronousSystem.InitQ vDec by blast 
    have U: "\<forall> u . u \<in> {v. \<exists>c'. qReachable c (UNIV - {p}) c'
      \<and>  <\<bottom>, outM v> \<in># msgs c'} \<longrightarrow> (u = v)" 
    proof clarify
      fix u c'
      assume "qReachable c (UNIV - {p}) c'"
      hence Reach: "reachable c c'" using QReachImplReach by simp
      from VDec have Msg: "<\<bottom>, outM v> \<in># msgs c" by simp
      from Reach NoOutMessageLoss have 
        "count (msgs c) <\<bottom>, outM v> \<le> count (msgs c') <\<bottom>, outM v>" by simp
      with Msg have VMsg: " <\<bottom>, outM v> \<in># msgs c'" 
        using NoOutMessageLoss Reach by (metis count_eq_zero_iff le_zero_eq) 
      assume " <\<bottom>, outM u> \<in># msgs c'"
      with Agree VMsg Reach show "u = v" by simp
    qed
    thus " {v. \<exists>c'. qReachable c (UNIV - {p}) c' \<and> 
       <\<bottom>, outM v> \<in># msgs c'} = {v}" using NotEmpty U by blast
  qed
qed

corollary NonUniformImpliesNotDecided:
assumes
  "\<forall> cfg . reachable c cfg \<longrightarrow> agreement cfg"
  "\<And>cc Q . terminationPseudo 1 cc Q"
  "nonUniform c"
  "vDecided v c"
  "initReachable c"
shows
  "False" by (metis (full_types) assms flpSystem.DecidedImpliesUniform flpSystem_axioms)
      
text{*
  All three parts of Völzer's Proposition 3 consider a single step from an
  arbitrary \isb{initReachable} configuration \var{c} with a message
  $\var{msg}$ to a succeeding configuration \var{c'}.
*}

text{*
  The silent decision values of a process which is not active in a step only
  decrease or stay the same.
  
  This follows directly from the definitions and the transitivity of the
  reachability properties \isb{reachable} and \isb{qReachable}.

  \voelzer{Proposition 3(a)}
*}
lemma InactiveProcessSilentDecisionValuesDecrease:
assumes 
  "p \<noteq> q" and
  "c \<turnstile> msg \<mapsto> c'" and
  "isReceiverOf p msg" and
  "initReachable c"
shows 
  "val[q,c'] \<subseteq> val[q,c]"
proof(auto simp add: pSilDecVal_def assms(4))
  fix x cfg'
  assume 
    Msg: "<\<bottom>, outM x> \<in># msgs cfg' " and 
    Cfg': "qReachable c' (Proc - {q}) cfg'"
  have "initReachable c'"
    using assms initReachable_def reachable.simps 
    by blast
  hence Init: "initReachable cfg'" 
    using Cfg' initReachable_def QReachImplReach[of c' "(Proc - {q})" cfg'] 
    ReachableTrans by blast
  have "p \<in> Proc - {q}"
    using assms by blast
  hence "qReachable c (Proc - {q}) c'"
    using assms qReachable.simps by metis
  hence "qReachable c (Proc - {q}) cfg'"
    using Cfg' QReachableTrans
    by blast
  with Msg Init show 
    "\<exists>c'a. qReachable c (Proc - {q}) c'a \<and>  <\<bottom>, outM x> \<in># msgs c'a" by blast
qed

text{*
  ...while the silent decision values of the process which is active in
  a step may only increase or stay the same.
  
  This follows as stated in \cite{Voelzer} from the \emph{diamond property}
  for a reachable configuration and a single step, i.e. \isb{DiamondTwo},
  and in addition from the fact that output messages cannot get lost, i.e.
  \isb{NoOutMessageLoss}.

  \voelzer{Proposition 3(b)}
*}
lemma ActiveProcessSilentDecisionValuesIncrease:
assumes 
  "p = q" and
  "c \<turnstile> msg \<mapsto> c'" and
  "isReceiverOf p msg" and
  "initReachable c"
shows "val[q,c] \<subseteq> val[q,c']"
proof (auto simp add: pSilDecVal_def assms(4))
  fix x cv 
  assume Cv: "qReachable c (Proc - {q}) cv"
    "<\<bottom>, outM x> \<in># msgs cv" 
  have "\<exists>c'a. (cv \<turnstile> msg \<mapsto> c'a) \<and> qReachable c' (Proc - {q}) c'a" 
    using DiamondTwo Cv(1) assms  by blast
  then obtain c'' where C'': "(cv \<turnstile> msg \<mapsto> c'')" 
    "qReachable c' (Proc - {q}) c''" by auto
  with Cv(2) initReachable_def reachable.simps
  have Init: "initReachable c''" by (meson Cv(1) QReachImplReach ReachableTrans assms(4))
  have "reachable cv c''" using C''(1) reachable.intros by blast    
  hence "count (msgs cv) <\<bottom>, outM x> \<le> count (msgs c'') <\<bottom>, outM x>" using NoOutMessageLoss  by simp
  hence "<\<bottom>, outM x> \<in># msgs c'' " using Cv(2) by (metis count_greater_eq_one_iff order_trans) 
  thus "\<exists>c'a. qReachable c' (Proc - {q}) c'a \<and> <\<bottom>, outM x> \<in># msgs c'a" 
    using C''(2) Init by blast
qed

text{*
  As a result from the previous two propositions, the silent decision values
  of a process cannot go from {0} to {1} or vice versa in a step.

  This is a slightly more generic version of Proposition 3 (c) from
  \cite{Voelzer} since it is proven for both values, while Völzer is only
  interested in the situation starting with $\var{val(q,c) = \{0\}}$.

  \voelzer{Proposition 3(c)}
*}
lemma SilentDecisionValueNotInverting:
assumes 
  Val: "val[q,c] = {v}" and
  Step:  "c \<turnstile> msg \<mapsto> c'" and
  Rec:  "isReceiverOf p msg" and
  Init: "initReachable c"
shows 
  "val[q,c'] \<noteq> {\<not> v}"
proof(cases "p = q")
  case False
    hence "val[q,c'] \<subseteq> val[q,c]"
      using Step Rec InactiveProcessSilentDecisionValuesDecrease Init by simp
    with Val show "val[q,c'] \<noteq> {\<not> v}" by auto
  next
  case True
    hence "val[q,c] \<subseteq> val[q,c']"
      using Step Rec ActiveProcessSilentDecisionValuesIncrease Init by simp
    with Val show "val[q,c'] \<noteq> {\<not> v}" by auto
qed

subsection{* Towards a proof of FLP *}

lemma inM_all_eq_imp_uniform:
  fixes i w
  assumes init:"initial i"
    and Validity: "\<And> i c . validity i c"
    and inM:"\<And> v . (\<exists>p. (<p, inM v> \<in># msgs i)) \<Longrightarrow> v = w"
    and Termination: "\<And>cc Q . terminationPseudo 1 cc Q"
  shows "vUniform w i" 
proof -
  have 1:"v = w" if "qReachable i (Proc - {p}) c'" and "vDecided v c'" for p c' v
    using that by (metis QReachImplReach Validity init inM validity_def)
  moreover 
  have "\<exists> c' . qReachable i (Proc - {p}) c' \<and> vDecided w c'" for p 
  proof -
    have "val[p,i] \<noteq> {}"
      using DecisionValuesExist Termination asynchronousSystem.InitialIsInitReachable local.init by blast
    then obtain c' u where 2:"qReachable i (Proc - {p}) c' \<and> vDecided u c'"
      using pSilDecVal_def by auto
    hence "u = w" using 1 by blast 
    thus ?thesis using 2 by blast 
  qed
  ultimately show "vUniform w i" unfolding vUniform_def pSilDecVal_def pSilentDecisionValues_def by auto
qed

lemma frozen_state_invisible: 
  assumes
    "withoutQReachable c Q d"
    and "\<And> p . states c' p = states c p"
    and "\<And> p m . \<lbrakk>p \<notin> Q; isReceiverOf p m\<rbrakk> \<Longrightarrow> (count (msgs c') m) = (count (msgs c) m)"
    and "\<And> v . count (msgs c') <\<bottom>,outM v> = (count (msgs c) <\<bottom>,outM v>)"
  shows "\<exists> d' . withoutQReachable c' Q d' \<and> (\<forall> p . states d' p = states d p)
    \<and> (\<forall> p m . p \<notin> Q \<and> isReceiverOf p m \<longrightarrow> (count (msgs d') m) = (count (msgs d) m))
    \<and> (\<forall> v . count (msgs d') <\<bottom>,outM v> = (count (msgs d) <\<bottom>,outM v>))"
  using assms
proof (induct c "Proc-Q" d rule:qReachable.induct)
  case (InitQ c1)
  then show ?case using qReachable.InitQ by blast 
next
  case (StepQ c1 d1 m d2)
  obtain d1' where 1:"qReachable c' (Proc - Q) d1'" and 2:"\<And> p . states d1' p = states d1 p"
    and 3:"\<And> p m . \<lbrakk>p \<notin> Q; isReceiverOf p m\<rbrakk> \<Longrightarrow> (count (msgs d1') m) = (count (msgs d1) m)"
      and 4:"\<And> v . count (msgs d1') <\<bottom>,outM v> = (count (msgs d1) <\<bottom>,outM v>)"
    using StepQ.hyps(2) StepQ.prems by auto 
  obtain p where 5:"p \<notin> Q" and 6:"isReceiverOf p m" using StepQ.hyps(4) by blast
  
  define d2' where "d2' \<equiv> \<lparr>states = (states d1')(p := states d2 p),
    msgs = (msgs d2 - (msgs d1 - {#m#})) + (msgs d1' - {#m#})\<rparr>"
    
  have f1:"\<And> p . states d2' p = states d2 p" 
    unfolding d2'_def using 2 6 \<open>d1 \<turnstile> m \<mapsto> d2\<close>
    by (metis UniqueReceiverOf asynchronousSystem.NoReceivingNoChange fun_upd_apply select_convs(1))
    
  define delta where "delta \<equiv> msgs d2 - (msgs d1 - {#m#})"
  have msgs':"msgs d2' = delta + (msgs d1' - {#m#})"
    using 2 \<open>d1 \<turnstile> m \<mapsto> d2\<close> by (simp add:d2'_def delta_def; cases m; simp)
  have msgs:"msgs d2 = delta + (msgs d1 - {#m#})" using \<open>d1 \<turnstile> m \<mapsto> d2\<close> 
    by ((simp add:delta_def)) (metis NoMessageLossStep subset_eq_diff_conv subset_mset.diff_add)
  have f2:"(count (msgs d2') m2) = (count (msgs d2) m2)" if "p2 \<notin> Q" and "isReceiverOf p2 m2" for p2 m2
  proof -
    have "(count (msgs d1') m2) = (count (msgs d1) m2)" using "3" that by blast
    with msgs msgs' show ?thesis by simp
  qed
  have f3:"count (msgs d2') <\<bottom>,outM v> = (count (msgs d2) <\<bottom>,outM v>)" for v
    unfolding d2'_def using 4 msgs by auto
    
  have f4:"qReachable c' (Proc - Q) d2'"
  proof -
    have "d1' \<turnstile> m \<mapsto> d2'" using \<open>d1 \<turnstile> m \<mapsto> d2\<close> 2 3 6
       by (cases m; simp_all add:d2'_def enabled_def) (metis 5 6 count_eq_zero_iff)+
    thus ?thesis using \<open>qReachable c' (Proc - Q) d1'\<close> 6 qReachable.StepQ 5 by blast
  qed
  
  from f1 f2 f3 f4 show ?case by blast
qed

text{*
  There is an \isb{initial} configuration that is \isb{nonUniform} under
  the assumption of \isb{validity}, \isb{agreement} and \isb{terminationPseudo}.

  The lemma is used in the proof of the main theorem to construct the
  \isb{non\-Uni\-form} and \isb{initial} configuration that leads to the
  final contradiction.

  \voelzer{Lemma 1}
*}
lemma InitialNonUniformCfg:
assumes
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Validity: "\<forall> i c . validity i c" and
  Agreement: "\<forall> i c . agreementInit i c"
shows 
  "\<exists> cfg . initial cfg \<and> nonUniform cfg" 
proof-
  define n where "n \<equiv> card Proc"
  text {* We order the processes using a bijection to @{term "{0..<n}"}. *}
  obtain f where f_bij:"bij_betw f Proc {0..<n}"
    using ex_bij_betw_finite_nat n_def finite_UNIV by blast
  
  text {* We define a family of configurations as in \voelzer{Lemma 1}. *}
  define initMsgs :: "nat \<Rightarrow> (('p, 'v) message) multiset"
    where "initMsgs \<equiv>  (\<lambda> i . mset_set {m . \<exists> p . m = <p, inM (f p < i)>})"
  define initCfg :: "nat \<Rightarrow> ('p, 'v, 's) configuration" where
    "initCfg \<equiv> \<lambda> i . \<lparr> states = start, msgs = initMsgs i \<rparr>"
  have count_initMsgs[simp]:"count (initMsgs i) m = (if (\<exists> p . m = <p, inM f p < i>) then 1 else 0)" for i m
  proof -
    have finite_initMsgs_set:
      "finite {m . \<exists> p . m = <p, inM (f p < i)>}" (is "finite ?S") for i 
    proof -
      have "?S = (\<lambda> p . <p, inM (f p < i)>) ` UNIV" by (simp add: full_SetCompr_eq)
      thus ?thesis by simp
    qed
    thus ?thesis
      using count_mset_set(1)[OF finite_initMsgs_set] count_mset_set(3) initMsgs_def by auto
  qed
  hence in_initMsgs[iff]:"m \<in># initMsgs i \<longleftrightarrow> (\<exists> p . m = <p, inM f p < i>)" for m i
    by (metis count_eq_zero_iff zero_neq_one)
    
  text {* All the configurations in the family are initial. *}
  have InitInitial: "initial c" if 1:"c \<in> initCfg ` {0..m}" for c m 
    using that unfolding initial_def initCfg_def
    by (cases c, auto simp add: split:if_splits message.splits)
  
  text {* Now we obtain an index j where the configuration j is uniform, 
    but not the configuration @{term "j+1"} *}
  define P::"nat \<Rightarrow> bool" where "P \<equiv> \<lambda> i . vUniform False (initCfg i)"
  obtain j where "j\<in>{0..<(n+1)}" and "P j" and "\<not> (P (j+1))"
  proof -
    have "P 0" 
    proof -
      have "\<And> v . (\<exists>p. (<p, inM v> \<in># msgs (initCfg 0))) \<Longrightarrow> v = False"
        unfolding initCfg_def by (auto split!:message.splits if_splits)
      moreover from InitInitial have "initial (initCfg 0)"
        by (simp add: finite_UNIV finite_UNIV_card_ge_0 n_def)
      ultimately show ?thesis using inM_all_eq_imp_uniform Validity Termination P_def
        by blast 
    qed
    have "\<not> P (n+1)" 
    proof - 
      have "\<And> v . (\<exists>p. (<p, inM v> \<in># msgs (initCfg (n+1)))) \<Longrightarrow> v = True"
        unfolding initCfg_def n_def by (auto split!:message.splits if_splits) 
          (metis atLeastLessThan_iff bij_betw_imp_surj_on f_bij less_SucI n_def rangeI)
      moreover from InitInitial have "initial (initCfg (n+1))"
        by (meson atLeastAtMost_iff image_iff le0 order_refl) 
      ultimately have "vUniform True (initCfg (n+1))" using inM_all_eq_imp_uniform Validity Termination
        by blast 
      thus ?thesis unfolding P_def vUniform_def by auto
    qed
    from \<open>P 0\<close> and \<open>\<not> (P (n+1))\<close> show ?thesis using that NatPredicateTippingPoint by moura
  qed
  
  text {* Now we show that the configuration @{term "j+1"} is non-uniform. *}
  consider (a) "vUniform True (initCfg (j+1))" | (b) "nonUniform (initCfg (j+1))" 
    using \<open>\<not> (P (j+1))\<close> P_def by blast
  thus ?thesis
  proof (cases)
    case a
    text {* We obtain an execution where False is decided, leading to a contradiction. *}
    define pj where "pj \<equiv> (inv f) j"
    obtain c where "qReachable (initCfg (j+1)) (Proc-{pj}) c" and "vDecided False c"
    proof -
      obtain cj where 1:"withoutQReachable (initCfg j) {pj} cj" and "vDecided False cj"
        using \<open>P j\<close> that unfolding P_def vUniform_def pSilDecVal_def pSilentDecisionValues_def by auto 
      have 2:"\<And> p . states (initCfg j) p = states (initCfg (j+1)) p"
        unfolding initCfg_def by auto
      have 3:"count (msgs (initCfg j)) m = (count (msgs (initCfg (j+1))) m)" 
        if "p \<notin> {pj}" and "isReceiverOf p m" for p m using that f_bij unfolding initCfg_def pj_def 
        by auto (metis UNIV_I bij_betw_def inv_into_f_f less_antisym)+
      have 4:"count (msgs (initCfg (j+1))) <\<bottom>,outM v> = (count (msgs (initCfg j)) <\<bottom>,outM v>)" for v
        using initCfg_def by auto
      obtain cSucJ where "withoutQReachable (initCfg (j+1)) {pj} cSucJ" 
        and "\<And> v . count (msgs cSucJ) <\<bottom>,outM v> = (count (msgs cj) <\<bottom>,outM v>)"
        using frozen_state_invisible[OF 1] 2 3 4 by simp blast
      have "vDecided False cSucJ" using \<open>vDecided False cj\<close> 
          \<open>\<And> v . count (msgs cSucJ) <\<bottom>,outM v> = (count (msgs cj) <\<bottom>,outM v>)\<close>
        by (metis count_eq_zero_iff)
      show ?thesis using that \<open>vDecided False cSucJ\<close> \<open>withoutQReachable (initCfg (j+1)) {pj} cSucJ\<close>
        by blast
    qed
    with a have False unfolding vUniform_def pSilDecVal_def pSilentDecisionValues_def
      by blast
    thus ?thesis by auto
  next
    case b
    then show ?thesis using InitInitial atLeastAtMost_iff by blast 
  qed 
qed

lemma bool_set_cases:
  obtains "bs = {}" | "bs = {True}" | "bs = {False}" | "bs = {True,False}"
  by (cases "bs = {}"; cases "bs = {True}"; cases "bs = {False}"; cases "bs = {True,False}")
    (auto, (metis (full_types))+)

text{*  
  Völzer's Lemma 2 proves that for every process $p$ in the consensus setting 
  \isb{nonUniform} configurations can reach a configuration where the silent
  decision values of $p$ are True and False. This is key to the construction of
  non-deciding executions.

  \voelzer{Lemma 2}
*}
lemma NonUniformCanReachSilentBivalence:
assumes 
  Init: "initReachable c" and
  NonUni: "nonUniform c" and
  PseudoTermination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Agree: "\<And> cfg . reachable c cfg \<longrightarrow> agreement cfg"
shows 
   "\<exists> c' . reachable c c' \<and> val[p,c'] = {True, False}"
proof(cases "val[p,c] = {True, False}")
  case True 
  have "reachable c c" using reachable.simps by metis
  thus ?thesis using True by blast
next 
  case False
  
  text {* Since the configuration is non-uniform, we obtain p with @{term "val[p,c] = {b}"}
    and q with @{term "(\<not>b) \<in> val[q,c]"}*}
  have 2:"val[q,c] \<noteq> {}" for q
    using DecisionValuesExist Init PseudoTermination by blast
  obtain b where  "val[p,c] = {b}" using 2 False
    by (cases "val[p,c]" rule:bool_set_cases; auto)
  obtain q where "(\<not> b) \<in> val[q,c]"
  proof -
    obtain p2 where 4:"val[p2,c] \<noteq> {b}" using False that \<open>nonUniform c\<close>  
      by (simp add:pSilDecVal_def vUniform_def) (metis (mono_tags, lifting))
    moreover 
    have "val[p2,c] \<noteq> {}" using 2 by auto
    ultimately show ?thesis 
      using that by (cases "val[p2,c]" rule:bool_set_cases; auto)
  qed
  
  text {* Then we reach a configuration @{term cNotB} in which @{term "val[p,cNotB]={\<not>b}"} by letting
    the system run without q and reach a @{term "\<not>b"} decision. *}
  obtain cNotB where "vDecided (\<not> b) cNotB" and "withoutQReachable c {q} cNotB"
    using \<open>(\<not> b) \<in> val[q,c]\<close> pSilDecVal_def by auto
  hence "val[p,cNotB] = {\<not> b}"
    by (meson Agree DecidedImpliesUniform Init PseudoTermination ReachableTrans asynchronousSystem.QReachImplReach initReachable_def vUniform_def)
  
  text {* We obtain two configuration @{term "cB"} and @{term cNotB'}, on the way to @{term "cNotB"} 
    where the set of silent decision values of p changes to include @{term "\<not>b"} or is @{term "{True,False}"} already. *}
  obtain cB cNotB' m q' where "val[p,cB] = {b} \<or> val[p,cB] = {True,False}" and "(\<not>b) \<in> val[p,cNotB']" and
    "cB \<turnstile> m \<mapsto> cNotB'" and "isReceiverOf q' m" and "withoutQReachable c {q} cB"
    using \<open>withoutQReachable c {q} cNotB\<close> \<open>val[p,cNotB] = {\<not> b}\<close> \<open>val[p,c] = {b}\<close> \<open>initReachable c\<close>
  proof (induct c "Proc - {q}" cNotB rule:qReachable.induct)
    case (InitQ c1)
    then show ?case by simp
  next
    case (StepQ c1 c2 msg c3)
    then show ?case
    proof (cases "val[p,c2] = {\<not> b}")
      case True
      text {* Immediate by induction hypothesis. *}
      then show ?thesis
        using StepQ.hyps(2) StepQ.prems(1) StepQ.prems(3) StepQ.prems(4) by blast
    next
      case False
      have "val[p,c2] \<noteq> {}"
        by (meson DecisionValuesExist PseudoTermination ReachableTrans StepQ.hyps(1) StepQ.prems(4) asynchronousSystem.QReachImplReach initReachable_def)
      with False have "val[p,c2] = {b} \<or> val[p,c2] = {True,False}"
        by (cases "val[p,c2]" rule:bool_set_cases) auto
      then show ?thesis
        by (metis StepQ.hyps(1) StepQ.hyps(3) StepQ.hyps(4) StepQ.prems(1) StepQ.prems(2) singletonI)        
    qed
  qed
  
  text {* Trivial facts *}
  have "initReachable cB" 
    using \<open>withoutQReachable c {q} cB\<close> \<open>initReachable c\<close>  QReachImplReach ReachableTrans initReachable_def
    by blast
  have "reachable c cNotB'" using \<open>cB \<turnstile> m \<mapsto> cNotB'\<close> \<open>withoutQReachable c {q} cB\<close>
    using QReachImplReach reachable.step by blast
  
  text {* Now either  @{term "val[p,cB] = {True,False}"} or, using @{thm SilentDecisionValueNotInverting}, 
    @{term "val[p,cNotB'] = {True,False}"}*}
  consider "val[p,cB] = {True,False}" | "val[p,cNotB'] = {True,False}"
  proof -
    have "val[p,cNotB'] = {True,False}" if "val[p,cB] \<noteq> {True,False}"
    proof -
      from that and \<open>val[p,cB] = {b} \<or> val[p,cB] = {True,False}\<close>
      have "val[p,cB] = {b}"
        by linarith 
      have "val[p,cNotB'] \<noteq> {\<not>b}" 
        using  SilentDecisionValueNotInverting[OF \<open>val[p,cB] = {b}\<close> \<open>cB \<turnstile> m \<mapsto> cNotB'\<close> \<open>isReceiverOf q' m\<close>
            \<open>initReachable cB\<close>] by simp
      with \<open>(\<not>b) \<in> val[p,cNotB']\<close> and 2 
      show "val[p,cNotB'] = {True,False}" by fastforce
    qed
    thus ?thesis using that by blast 
  qed
  
  text {* And in both cases we have found our @{term c'} *}
  hence "\<exists> c' . reachable c c' \<and> val[p,c'] = {True, False}"
    using \<open>reachable c cNotB'\<close> \<open>withoutQReachable c {q} cB\<close> by (meson QReachImplReach) 
  with False 2 show ?thesis by auto
qed

end

end
