section \<open>AsynchronousSystem\<close>

text \<open>
  \file{AsynchronousSystem} defines a message datatype and a transition system locale to
  model asynchronous distributed computation. It establishes a diamond property for a
  special reachability relation within such transition systems.
\<close>

theory AsynchronousSystem
imports "~~/src/HOL/Library/Multiset"
begin

text\<open>
  The formalization is type-parameterized over
  \begin{description}
    \item[\var{'p} process identifiers.] Corresponds to the set $P$ in Völzer.
      Finiteness is not yet demanded, but will be in \file{FLPSystem}.
    \item[\var{'s} process states.] Corresponds to $S$, countability is not
      imposed.
    \item[\var{'v} message payloads.] Corresponds to the interprocess
      communication part of $M$ from Völzer. The whole of $M$ is captured by
      \isb{messageValue}.
  \end{description}
\<close>

subsection\<open>Messages\<close>

text \<open>
  A \isb{message} is either an initial input message telling a process
  which value it should introduce to the consensus negotiation, a message
  to the environment communicating the consensus outcome, or a message
  passed from one process to some other.
\<close>

datatype ('p, 'v) message =
  InMsg 'p bool  ("<_, inM _>")
| OutMsg bool    ("<\<bottom>, outM _>")
| Msg 'p 'v      ("<_, _>")

text \<open>
  A message value is the content of a message, which a process may receive. 
\<close>

datatype 'v messageValue = 
  Bool bool
| Value 'v

fun unpackMessage :: "('p, 'v) message \<Rightarrow> 'v messageValue"
where
  "unpackMessage <p, inM b>  = Bool b"
| "unpackMessage <p, v>      = Value v"
| "unpackMessage <\<bottom>, outM v> = Bool False"

fun isReceiverOf :: 
  "'p \<Rightarrow> ('p, 'v) message \<Rightarrow> bool"
where 
   "isReceiverOf p1 (<p2, inM v>) = (p1 = p2)"
 | "isReceiverOf p1 (<p2, v>) =     (p1 = p2)"
 | "isReceiverOf p1 (<\<bottom>,outM v>) =  False"

lemma UniqueReceiverOf:
fixes 
  msg  :: "('p, 'v) message" and
  p q :: 'p
assumes
  "isReceiverOf q msg"
  "p \<noteq> q"
shows 
  "\<not> isReceiverOf p msg"
using assms by (cases msg, auto)

subsection\<open>Configurations\<close>

text \<open>
  Here we formalize a configuration as detailed in section 2 of Völzer's paper.

  Note that Völzer imposes the finiteness of the message multiset by
  definition while we do not do so. In \isb{FiniteMessages}
  We prove the finiteness to follow from the assumption that only
  finitely many messages can be sent at once.
\<close>

record ('p, 'v, 's) configuration =
  states :: "'p \<Rightarrow> 's"
  msgs :: "(('p, 'v) message) multiset"

text \<open>
  C.f. Völzer: \textquote{A step is identified with a message $(p, m)$. A step $(p, m)$ is enabled
  in a configuration c if $\var{msgs}_c$ contains the message $(p, m)$.}
\<close>

definition enabled ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v) message \<Rightarrow> bool"
where 
  "enabled cfg msg \<equiv> (msg \<in># msgs cfg)"

subsection \<open>The system locale\<close>

text \<open>
  The locale describing a system is derived by slight refactoring from the
  following passage of Völzer:
  \begin{displayquote}
    A process $p$ consists of an initial state $s_p \in S$ and a step transition
    function, which assigns to each pair $(m, s)$ of a message value $m$ and
    a process state $s$ a follower state and a finite set of messages (the
    messages to be sent by $p$ in a step).
  \end{displayquote}
\<close>

locale asynchronousSystem =
fixes 
  trans :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> 's" and
  sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset" and
  start :: "'p \<Rightarrow> 's"
begin

abbreviation Proc :: "'p set"
where "Proc \<equiv> (UNIV :: 'p set)"

subsection \<open>The step relation\<close>

text \<open>
  The step relation is defined analogously to Völzer:
  \begin{displayquote}
    {[}If enabled, a step may{]} occur, resulting in a follower
    configuration $c^\prime$, where $c^\prime$ is obtained from $c$ by removing
    $(p, m)$ from $\var{msgs}_c$, changing $p$'s state and adding the set of
    messages to $\var{msgs}_c$ according to the step transition function
    associated with $p$. We denote this by $c \xrightarrow{p,m} c^\prime$.
  \end{displayquote}
  There are no steps consuming output messages.
\<close>

fun steps :: 
  "('p, 'v, 's) configuration
   \<Rightarrow> ('p, 'v) message
   \<Rightarrow> ('p, 'v, 's) configuration
   \<Rightarrow> bool"
   ("_ \<turnstile> _ \<mapsto> _" [70,70,70])
where 
  StepInMsg: "cfg1 \<turnstile> <p, inM v> \<mapsto> cfg2 = (
  (\<forall> s. ((s = p) \<longrightarrow> states cfg2 p = trans p (states cfg1 p) (Bool v))
      \<and> ((s \<noteq> p) \<longrightarrow> states cfg2 s = states cfg1 s))
   \<and> enabled cfg1 <p, inM v>
   \<and> msgs cfg2 = (sends p (states cfg1 p) (Bool v)
                  + (msgs cfg1 - {#(<p, inM v>)#} )))"
| StepMsg: "cfg1 \<turnstile> <p, v> \<mapsto> cfg2 = (
  (\<forall> s. ((s = p) \<longrightarrow> states cfg2 p = trans p (states cfg1 p) (Value v))
      \<and> ((s \<noteq> p) \<longrightarrow> states cfg2 s = states cfg1 s))
   \<and> enabled cfg1 <p, v>
   \<and> msgs cfg2 = (sends p (states cfg1 p) (Value v)
                  + (msgs cfg1 - {#(<p, v>)#})))"
| StepOutMsg: "cfg1 \<turnstile> <\<bottom>,outM v> \<mapsto> cfg2 = 
    False"

text \<open>
  The system is distributed and asynchronous in the sense that the processing
  of messages only affects the process the message is directed to while the
  rest stays unchanged.
\<close>
lemma NoReceivingNoChange:
  assumes
    Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and Rec: "\<not> isReceiverOf p m"
  shows
    "states cfg1 p = states cfg2 p " 
  using assms by (cases m, auto)

lemma ExistsMsg:
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2"
shows
  "m \<in># (msgs cfg1)"
using assms enabled_def by (cases m, auto)

lemma NoMessageLossStep:
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2"
shows 
  "msgs cfg1 \<subseteq># msgs cfg2 + {#m#}"
  using subset_eq_diff_conv assms 
  by (induct cfg1 m cfg2 rule:steps.induct)  fastforce+

lemma OutOnlyGrowing:
assumes
  "cfg1 \<turnstile> m \<mapsto> cfg2" "isReceiverOf p m"
shows 
  "count (msgs cfg2) <\<bottom>, outM b>  = (count (msgs cfg1) <\<bottom>, outM b>) + 
    count (sends p (states cfg1 p) (unpackMessage m)) <\<bottom>, outM b>" 
  using assms by (cases m, auto)

lemma OtherMessagesOnlyGrowing:
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and "m \<noteq> m'"
shows "count (msgs cfg1) m' \<le> count (msgs cfg2) m'"
using assms by (cases m, auto)

text \<open>
  Völzer: \textquote{Note that steps are enabled persistently, i.e., an
  enabled step remains enabled as long as it does not occur.}
\<close>
lemma OnlyOccurenceDisables:
  assumes
    Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and En: "enabled cfg1 m'" and NotEn: "\<not> (enabled cfg2 m')"
  shows "m = m'"
  using assms OtherMessagesOnlyGrowing 
  apply (induct cfg1 m cfg2 rule:steps.induct; simp add:enabled_def)
   apply (metis (no_types, lifting) insert_DiffM insert_noteq_member union_iff)
  apply (metis (no_types, lifting)  insert_DiffM insert_noteq_member union_iff)
  done

subsection \<open>Reachability\<close>

inductive reachable :: 
  "  ('p, 'v, 's) configuration 
  \<Rightarrow> ('p, 'v, 's) configuration
  \<Rightarrow> bool"
where 
  init: "reachable cfg1 cfg1"
| step: "\<lbrakk> reachable cfg1 cfg2; (cfg2 \<turnstile> msg \<mapsto> cfg3) \<rbrakk> 
          \<Longrightarrow> reachable cfg1 cfg3"

lemma ReachableStepFirst: 
assumes
  "reachable cfg cfg'"
obtains 
  "cfg = cfg'" 
|  cfg1 msg p where "(cfg \<turnstile> msg \<mapsto> cfg1) \<and> enabled cfg msg 
  \<and> isReceiverOf p msg \<and> reachable cfg1 cfg'" 
using assms 
  by (induct rule: reachable.induct, auto)
  (metis asynchronousSystem.ExistsMsg asynchronousSystem.init asynchronousSystem.step enabled_def isReceiverOf.simps(1) isReceiverOf.simps(2) local.StepOutMsg message.exhaust)

lemma ReachableTrans: 
assumes  "reachable cfg1 cfg2" and "reachable cfg2 cfg3"
shows "reachable cfg1 cfg3"
  using assms(2) assms(1) asynchronousSystem.step  by (induct rule: reachable.induct, auto, blast)

definition stepReachable ::
    "('p, 'v, 's) configuration
  \<Rightarrow> ('p ,'v) message
  \<Rightarrow> ('p, 'v, 's) configuration
  \<Rightarrow> bool" 
where
  "stepReachable c1 msg c2 \<equiv> 
    \<exists> c' c''. reachable c1 c' \<and> (c' \<turnstile> msg \<mapsto> c'') \<and> reachable c'' c2 "

lemma StepReachable:
assumes
  "reachable cfg cfg'" and "enabled cfg msg" and "\<not> (enabled cfg' msg)"
shows "stepReachable cfg msg cfg'"
  using assms by (induct rule: reachable.induct, auto simp add:stepReachable_def)
  (metis asynchronousSystem.OnlyOccurenceDisables reachable.simps)

subsection \<open>Reachability with special process activity\<close>

text \<open>
  We say that \isb{qReachable cfg1 Q cfg2} iff cfg2 is reachable from cfg1
  only by activity of processes from Q.
\<close>
inductive qReachable ::
  "('p,'v,'s) configuration 
  \<Rightarrow> 'p set 
  \<Rightarrow> ('p,'v,'s) configuration 
  \<Rightarrow> bool"
where  
  InitQ: "qReachable cfg1 Q cfg1"
| StepQ: "\<lbrakk> qReachable cfg1 Q cfg2; (cfg2 \<turnstile> msg \<mapsto> cfg3) ;
            \<exists> p \<in> Q . isReceiverOf p msg \<rbrakk> 
          \<Longrightarrow> qReachable cfg1 Q cfg3"

text \<open>
  We say that \isb{withoutQReachable cfg1 Q cfg2} iff cfg2 is reachable from cfg1
  with no activity of processes from Q.
\<close>
abbreviation withoutQReachable ::
   "('p,'v,'s) configuration 
  \<Rightarrow> 'p set 
  \<Rightarrow> ('p,'v,'s) configuration 
  \<Rightarrow> bool"
where
  "withoutQReachable cfg1 Q cfg2 \<equiv> 
    qReachable cfg1 ((UNIV :: 'p set ) - Q) cfg2"

text\<open>
  Obviously q-reachability (and thus also without-q-reachability) implies 
  reachability.
\<close>
lemma QReachImplReach:
assumes
  "qReachable cfg1 Q cfg2"
shows 
  "reachable cfg1 cfg2"
  using assms  apply (induct rule: qReachable.induct, auto)
  using init apply blast
  using asynchronousSystem.step apply blast 
  done

lemma QReachableTrans:
assumes "qReachable cfg2 Q cfg3" and "qReachable cfg1 Q cfg2"
shows "qReachable cfg1 Q cfg3"
using assms
proof (induct rule: qReachable.induct, simp)
  case (StepQ)
  thus ?case using qReachable.simps by metis
qed

lemma NotInQFrozenQReachability: 
assumes
  "qReachable cfg1 Q cfg2" and "p \<notin> Q"
shows
  "states cfg1 p = states cfg2 p"
  using assms apply (induct rule: qReachable.induct, auto)
  by (metis (no_types) UniqueReceiverOf asynchronousSystem.NoReceivingNoChange)

corollary WithoutQReachablFrozenQ:
assumes
  Steps: "withoutQReachable cfg1 Q cfg2" and P: "p \<in> Q"
shows
  "states cfg1 p = states cfg2 p"
using assms NotInQFrozenQReachability by simp

lemma NoActivityNoMessageLoss :
assumes
  "qReachable cfg1 Q cfg2" and "p \<notin> Q" and "isReceiverOf p m'"
shows
  "count (msgs cfg1) m' \<le> count (msgs cfg2) m'"
  using assms apply (induct rule: qReachable.induct, simp)
  by (metis (no_types, lifting) OtherMessagesOnlyGrowing UniqueReceiverOf order_trans)

lemma NoMessageLoss:
assumes
  "withoutQReachable cfg1 Q cfg2" and "p \<in> Q" and "isReceiverOf p m'"
shows
  "count (msgs cfg1) m' \<le> count (msgs cfg2) m'"
using assms NoActivityNoMessageLoss by simp

lemma NoOutMessageLoss:
  assumes
    "reachable cfg1 cfg2"
  shows
    "count (msgs cfg1) <\<bottom>, outM v> \<le> count (msgs cfg2) <\<bottom>, outM v>"
  using assms
  apply (induct rule: reachable.induct, auto)
  by (metis (no_types, lifting) OtherMessagesOnlyGrowing local.StepOutMsg order_trans) 

lemma StillEnabled:
assumes 
  "withoutQReachable cfg1 Q cfg2" and "p \<in> Q" and "isReceiverOf p msg" and
  "enabled cfg1 msg"
shows
  "enabled cfg2 msg"
  using assms
  by (meson NoMessageLoss count_greater_eq_one_iff dual_order.trans enabled_def)

subsection\<open>Initial reachability\<close>

definition initial :: 
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "initial cfg \<equiv>
        (\<forall> p::'p . (\<exists> v::bool . (count (msgs cfg) <p, inM v> = 1)))
      \<and> (\<forall> p m1 m2 . ((m1 \<in># (msgs cfg)) \<and> (m2 \<in># (msgs cfg)) 
         \<and> isReceiverOf p m1 \<and> isReceiverOf p m2) \<longrightarrow> (m1 = m2))
      \<and> (\<forall> v::bool . count (msgs cfg) <\<bottom>, outM v> = 0)
      \<and> (\<forall> p v. count (msgs cfg) <p, v> = 0)
      \<and> states cfg = start"

definition initReachable ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "initReachable cfg \<equiv> \<exists>cfg0 . initial cfg0 \<and> reachable cfg0 cfg"

lemma InitialIsInitReachable :
assumes "initial c"
shows "initReachable c"
  using assms reachable.init
  unfolding initReachable_def by blast

subsection \<open>Diamond property of reachability\<close>
  
lemma DiamondOne:
assumes
  StepP: "c \<turnstile> m  \<mapsto> c1" and
  PNotQ: "p \<noteq> q" and
  Rec: "isReceiverOf p m" and
  Rec': "isReceiverOf q m'" and
  StepQ: "c \<turnstile> m' \<mapsto> c2"
shows
  "\<exists> c'  . (c1 \<turnstile> m' \<mapsto> c') \<and> (c2 \<turnstile> m \<mapsto> c')" 
proof -
  text \<open>First a few auxiliary facts.\<close>
  have "enabled c m'" and "enabled c m" 
    using asynchronousSystem.ExistsMsg enabled_def local.StepQ StepP by blast+
  have "m \<noteq> m'" using PNotQ Rec Rec' UniqueReceiverOf by fastforce 
  { fix p q c c1 and m m'::"('p, 'v) message"
    assume "p \<noteq> q" and "isReceiverOf p m" and "c \<turnstile> m \<mapsto> c1" and "isReceiverOf q m'"
      and "enabled c m'"
    have "states c1 q = states c q" and "enabled c1 m'"
    proof -
      have "withoutQReachable c {q} c1"
        by (meson DiffI UNIV_I \<open>c \<turnstile> m \<mapsto> c1\<close> \<open>isReceiverOf p m\<close> \<open>p \<noteq> q\<close> qReachable.simps singleton_iff) 
      thus "states c1 q = states c q" using WithoutQReachablFrozenQ  by auto 
    next
      show "enabled c1 m'"
        using UniqueReceiverOf \<open>c \<turnstile> m \<mapsto> c1\<close> \<open>enabled c m'\<close> \<open>isReceiverOf p m\<close> \<open>isReceiverOf q m'\<close> \<open>p \<noteq> q\<close> asynchronousSystem.OnlyOccurenceDisables by fastforce 
    qed }
  note 1 = this[of p q m c c1, OF \<open>p \<noteq> q\<close> \<open>isReceiverOf p m\<close> \<open>c \<turnstile> m  \<mapsto> c1\<close> \<open>isReceiverOf q m'\<close> \<open>enabled c m'\<close>]
    and 2 = this[of q p m' c c2, OF \<open>p \<noteq> q\<close>[symmetric] \<open>isReceiverOf q m'\<close> \<open>c \<turnstile> m'  \<mapsto> c2\<close>  \<open>isReceiverOf p m\<close> \<open>enabled c m\<close>]

  define c1' where "c1' \<equiv> \<lparr>states = (states c1)(q := states c2 q),
    msgs = (msgs c2 - (msgs c - {#m'#})) + (msgs c1 - {#m'#})\<rparr>"
  define c2' where "c2' \<equiv> \<lparr>states = (states c2)(p := states c1 p),
    msgs = (msgs c1 - (msgs c - {#m#})) + (msgs c2 - {#m#})\<rparr>"
    
  have "c1 \<turnstile> m' \<mapsto> c1'" using \<open>c \<turnstile> m' \<mapsto> c2\<close> 1 \<open>isReceiverOf q m'\<close>
    by (simp add:c1'_def; induct c m' c2 rule:steps.induct)
      (auto simp add: enabled_def union_single_eq_diff add.commute)
  moreover
  have "c2 \<turnstile> m \<mapsto> c2'" using \<open>c \<turnstile> m \<mapsto> c1\<close> 2 \<open>isReceiverOf p m\<close>
    by (simp add:c2'_def; induct c m c1 rule:steps.induct)
      (auto simp add: enabled_def union_single_eq_diff add.commute)
  moreover 
  have "c1' = c2'" using 1 2 \<open>p\<noteq>q\<close> \<open>enabled c m\<close> \<open>enabled c m'\<close> \<open>m \<noteq> m'\<close> StepQ StepP 
      NoMessageLossStep[OF StepP] NoMessageLossStep[OF StepQ] Rec Rec'
    by (auto simp add:c1'_def c2'_def enabled_def fun_eq_iff add.commute subset_eq_diff_conv)
     (metis UniqueReceiverOf NoReceivingNoChange)
  ultimately show ?thesis by blast
qed

lemma DiamondTwo:
assumes
  QReach: "qReachable c Q c1" and
  Step: "c  \<turnstile> m \<mapsto> c2" "\<exists>p\<in>Proc - Q. isReceiverOf p m"
shows
  "\<exists> c' . (c1  \<turnstile> m \<mapsto> c') \<and> qReachable c2 Q c'"
using assms 
proof (induct c Q c1 rule: qReachable.induct)
  case (InitQ c Q)
  then show ?case using asynchronousSystem.InitQ by blast
next
  case (StepQ c1' Q c2' m2 c3)
  obtain c' where "c2' \<turnstile> m \<mapsto> c'" and "qReachable c2 Q c'" 
    using StepQ.hyps(2)[OF StepQ.prems] by auto
  obtain c'' where "c'  \<turnstile> m2 \<mapsto> c''" and "c3  \<turnstile> m \<mapsto> c''" 
    using DiamondOne \<open>c2' \<turnstile> m \<mapsto> c'\<close> \<open>c2' \<turnstile> m2 \<mapsto> c3\<close>
      \<open>\<exists>p\<in>Q. isReceiverOf p m2\<close> \<open>\<exists>p\<in>Proc - Q. isReceiverOf p m\<close>  by (metis DiffD2)
  moreover
  have "qReachable c2 Q c''" 
    using \<open>qReachable c2 Q c'\<close> \<open>c2' \<turnstile> m2 \<mapsto> c3\<close> \<open>c'  \<turnstile> m2 \<mapsto> c''\<close>
      \<open>\<exists>p\<in>Q. isReceiverOf p m2\<close> \<open>\<exists>p\<in>Proc - Q. isReceiverOf p m\<close> qReachable.StepQ by blast 
  ultimately show ?case by blast 
qed

text \<open>Proposition 1 of Völzer.\<close>
lemma Diamond:
assumes
  QReach: "qReachable c Q c1" and
  WithoutQReach: "withoutQReachable c Q c2"
shows 
  "\<exists> c'. withoutQReachable c1 Q c' \<and> qReachable c2 Q c'" using assms
proof (induct c Q c1 rule: qReachable.induct)
  case (InitQ c1 Q)
  then show ?case
    using asynchronousSystem.InitQ by blast
next
  case (StepQ c1 Q c2' m c3)
  obtain c' where "qReachable c2' (Proc - Q) c'" and "qReachable c2 Q c'"
    using StepQ.hyps(2) StepQ.prems by blast
  obtain c'' where "qReachable c3 (Proc - Q) c''" and "c' \<turnstile> m \<mapsto> c''"
    using \<open>qReachable c2' (Proc - Q) c'\<close> \<open>c2' \<turnstile> m \<mapsto> c3\<close> \<open>\<exists>p\<in>Q. isReceiverOf p m\<close>
    by (metis DiamondTwo DiffD2 DiffI UNIV_I)
  have "qReachable c2 Q c''" using \<open>qReachable c2 Q c'\<close> \<open>c' \<turnstile> m \<mapsto> c''\<close> \<open>\<exists>p\<in>Q. isReceiverOf p m\<close>
    qReachable.StepQ by blast 
  show ?case using \<open>qReachable c3 (Proc - Q) c''\<close> \<open>qReachable c2 Q c''\<close> by blast
qed

end

end