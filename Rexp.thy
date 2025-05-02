theory Rexp
  imports Main
begin



section \<open>Definitions: Language Operations and Regular Expressions\<close>


text \<open>Sequential composition\<close>

definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ \<otimes> _" [100,100] 100)
where 
  "A \<otimes> B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"


text \<open>Language power\<close>

fun 
  Lang_pow :: "string set \<Rightarrow> nat \<Rightarrow> string set" ("_ \<up> _" [100, 100] 100)
where
  "A \<up> 0 = {[]}" 
| "A \<up> (Suc n) = A \<otimes> (A \<up> n)"


thm Lang_pow.simps
thm Lang_pow.induct


text \<open>Kleene Star\<close>

definition 
  Star :: "string set \<Rightarrow> string set"
where
  "Star A = (\<Union>n. A \<up> n)"

thm Star_def



inductive_set
  Star2 :: "string set \<Rightarrow> string set" ("_\<star>" [101] 102)
  for A :: "string set"
where
  start: "[] \<in> A\<star>"
| step:  "\<lbrakk>s1 \<in> A; s2 \<in> A\<star>\<rbrakk> \<Longrightarrow> s1 @ s2 \<in> A\<star>"

thm Star2.induct
thm Star2.intros
thm start step



datatype rexp =
  ZERO
| ONE
| CH char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp

thm rexp.induct

section \<open>Types and Terms\<close>

(*
  nat
  int
  char
  bool
  'a set
  char set
  'a list
  char list set  (aka set of strings)
  'a \<Rightarrow> 'b
  ..

  A \<and> B
  C \<or> D
  E \<longrightarrow> F
  \<forall>x. P x
  {x . P x}
  0
  (Suc 0)
  1, 2, 3
  ...
  
  \<lambda>x. x

*)


section \<open>Lemmas, Automated Tools and Apply Scripts\<close>

lemma Sequ_empty [simp]:
  shows "A \<otimes> {} = {}"
  and   "{} \<otimes> A = {}"
  apply(auto simp add: Sequ_def)
  done

lemma Sequ_empty_string [simp]:
  shows "A \<otimes> {[]} = A"
  and   "{[]} \<otimes> A = A"
  apply(simp_all add: Sequ_def)
  done

thm Sequ_empty_string



(* general pattern:

lemma name[modifiers]:
  fixes var::type
  assumes nme: "..."
  and nme: "..."
  shows "..."
  and   "..."
  <<<...proof...>>>
  done   
*)

lemma silly_example:
  fixes x :: nat
  assumes "x < 5"
  shows "2 * x + 3 < 2 * 5 + 3"
  using assms   
  apply(auto)
  done

(* automated provers

  simp
  simp_all

  simp add: ...
  simp only: ...
  simp del: ...

  auto
  auto simp: 
  ...

  sledgehammer
*)



(* aside: oops, sorry *)

text \<open>Some Simple Properties about Sequential Composition\<close>



lemma Sequ_assoc: 
  shows "(A \<otimes> B) \<otimes> C = A \<otimes> (B \<otimes> C)"
  apply(simp add: Sequ_def)
  apply(metis (no_types, lifting) append.assoc)
  done

lemma Lang_pow_comm:
  shows "A \<otimes> (A \<up> n) = (A \<up> n) \<otimes> A"
  apply(induct n)
  apply(simp)
  apply(simp)
  apply(simp add: Sequ_assoc[symmetric])
  done

lemma Lang_pow_add: 
  shows "A \<up> (n + m) = (A \<up> n) \<otimes> (A \<up> m)"
  apply(induct n)
  apply(simp)
  apply(simp)
  apply(subst Sequ_assoc[symmetric])
  apply(simp)
  done

lemma Star_pow1:
  assumes "s \<in> A\<star>"
  shows "\<exists>n. s \<in> A \<up> n"
  using assms
  apply(induct)
  apply(rule_tac x="0" in exI)
  apply(simp)
  apply(erule exE)
  apply(rule_tac x="Suc n" in exI)
  apply(simp)
  apply(auto simp add: Sequ_def)
  done

lemma Star_pow2:
  assumes "s \<in> A \<up> n"
  shows "s \<in> A\<star>"
  using assms
  apply(induct n arbitrary: s)
  apply(simp add: Star2.start)
  apply(simp add: Sequ_def)
  apply(erule exE)
  apply(erule exE)
  apply(simp)
  apply(rule step)
  apply(simp)
  apply(drule_tac x="s2" in meta_spec)
  apply(simp)
  done

lemma Star_Star2:
  shows "Star A = A\<star>"
  apply(auto)
  apply(simp add: Star_def)
  apply(erule exE)
  apply(simp add: Star_pow2)
  apply(simp add: Star_def)
  apply(simp add: Star_pow1)
  done

lemma silly_test_all:
  assumes "\<forall>x. P x"
  shows "P 5"
  using assms 
  apply(drule_tac x="5" in spec)
  apply(simp)
  done

lemma silly_test_ex:
  assumes "P 5"
  shows "\<exists>x. P x \<or> Q x"
  using assms 
  apply(rule_tac x="5" in exI)
  apply(simp)
  done

lemma silly_test_ex2:
  assumes "\<exists>x. P (Suc x)"
  shows "\<exists>x. P x \<or> Q x"
  using assms 
  apply(erule_tac exE)
  apply(rule_tac x="Suc x" in exI)
  apply(simp)
  done

section \<open>Language for Regular Expressions\<close>
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (ZERO) = {}"
| "L (ONE) = {[]}"
| "L (CH c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) \<otimes> (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"
| "L (STAR r) = (L r)\<star>"


section \<open>Semantic Derivative (Left Quotient) of Languages\<close>

definition
  Der :: "char \<Rightarrow> string set \<Rightarrow> string set"
where
  "Der c A \<equiv> {s. c # s \<in> A}"


lemma Der_null [simp]:
  shows "Der c {} = {}"
unfolding Der_def
by auto

lemma Der_empty [simp]:
  shows "Der c {[]} = {}"
unfolding Der_def
by auto

lemma Der_char [simp]:
  shows "Der c {[d]} = (if c = d then {[]} else {})"
unfolding Der_def
by auto

lemma Der_union [simp]:
  shows "Der c (A \<union> B) = Der c A \<union> Der c B"
unfolding Der_def
by auto

lemma Der_Sequ [simp]:
  shows "Der c (A \<otimes> B) = 
        (Der c A) \<otimes> B \<union> (if [] \<in> A then Der c B else {})"
unfolding Der_def Sequ_def
by (auto simp add: Cons_eq_append_conv)

lemma 
shows Der_inter[simp]:   "Der a (A \<inter> B) = Der a A \<inter> Der a B"
  and Der_compl[simp]:   "Der a (-A) = - Der a A"
  and Der_Union[simp]:   "Der a (Union M) = Union(Der a ` M)"
  and Der_UN[simp]:      "Der a (UN x:I. S x) = (UN x:I. Der a (S x))"
by (auto simp: Der_def)


lemma Star_cons_decomp: 
  assumes "c # x \<in> A\<star>" 
  shows "\<exists>s1 s2. x = s1 @ s2 \<and> c # s1 \<in> A \<and> s2 \<in> A\<star>"
using assms
apply(induct x\<equiv>"c # x" rule: Star2.induct) 
apply(auto simp add: append_eq_Cons_conv)
done

lemma Star_Der_Sequ: 
  shows "Der c (A\<star>) \<subseteq> (Der c A) \<otimes> A\<star>"
unfolding Der_def Sequ_def
apply(auto simp add: Star_cons_decomp)
done


lemma Star_cases1:
  shows "Star A \<subseteq> {[]} \<union> A \<otimes> Star A"
  sorry

lemma Star_cases2:
  shows "{[]} \<union> A \<otimes> Star A \<subseteq> Star A "
  sorry

lemma Star_cases:
  shows "Star A = {[]} \<union> A \<otimes> Star A"
  using Star_cases1 Star_cases2
  by auto

lemma Der_star[simp]:
  shows "Der c (A\<star>) = (Der c A) \<otimes> A\<star>"
proof -    
  have "Der c (A\<star>) = Der c ({[]} \<union> A \<otimes> A\<star>)"
    using Star_Star2 Star_cases by auto    
  also have "... = Der c (A \<otimes> A\<star>)"
    by (simp only: Der_union Der_empty) (simp)
  also have "... = (Der c A) \<otimes> A\<star> \<union> (if [] \<in> A then Der c (A\<star>) else {})"
    by simp
  also have "... =  (Der c A) \<otimes> A\<star>"
    using Star_Der_Sequ by auto
  finally show "Der c (A\<star>) = (Der c A) \<otimes> A\<star>" .
qed




section \<open>Nullable, Derivatives\<close>

fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (ZERO) = False"
| "nullable (ONE) = True"
| "nullable (CH c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (STAR r) = True"

fun
 der :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "der c (ZERO) = ZERO"
| "der c (ONE) = ZERO"
| "der c (CH d) = (if c = d then ONE else ZERO)"
| "der c (ALT r1 r2) = ALT (der c r1) (der c r2)"
| "der c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2)"
| "der c (STAR r) = SEQ (der c r) (STAR r)"


lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
  apply(induct r) 
  apply(auto simp add: Sequ_def start)
  done


lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
sorry (*proof(induct r) *)



definition
  Ders :: "string \<Rightarrow> string set \<Rightarrow> string set"
where
  "Ders s A \<equiv> {s'. s @ s' \<in> A}"

fun
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"

lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
  by (induct s arbitrary: r)
     (simp_all add: Ders_def der_correctness Der_def)

lemma matcher_correctness:
  shows "nullable (ders s r) \<longleftrightarrow> s \<in> L r"
  sorry




end