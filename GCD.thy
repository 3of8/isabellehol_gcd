(*  Authors:    Christophe Tabacznyj, Lawrence C. Paulson, Amine Chaieb,
                Thomas M. Rasmussen, Jeremy Avigad, Tobias Nipkow


This file deals with the functions gcd and lcm.  Definitions and
lemmas are proved uniformly for the natural numbers and integers.

This file combines and revises a number of prior developments.

The original theories "GCD" and "Primes" were by Christophe Tabacznyj
and Lawrence C. Paulson, based on \cite{davenport92}. They introduced
gcd, lcm, and prime for the natural numbers.                           

The original theory "IntPrimes" was by Thomas M. Rasmussen, and
extended gcd, lcm, primes to the integers. Amine Chaieb provided
another extension of the notions to the integers, and added a number
of results to "Primes" and "GCD". IntPrimes also defined and developed
the congruence relations on the integers. The notion was extended to
the natural numbers by Chaieb.

Jeremy Avigad combined all of these, made everything uniform for the
natural numbers and the integers, and added a number of new theorems.

Tobias Nipkow cleaned up a lot.

Manuel Eberl introduced the typeclasses euclidean_semiring and 
euclidean_ring to derive a common gcd/lcm for all Euclidean (semi)rings,
such as nat, int and polynomials.
*)
theory GCD
imports Fact Parity
begin

declare One_nat_def [simp del]

context semiring_div
begin 
  definition ring_inv :: "'a \<Rightarrow> 'a" where "ring_inv x = 1 div x"
  definition is_unit :: "'a \<Rightarrow> bool" where "is_unit x \<longleftrightarrow> x dvd 1"
  definition associated :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
      where "associated x y \<longleftrightarrow> x dvd y \<and> y dvd x"

lemma unit_prod [intro]: "\<lbrakk>is_unit x; is_unit y\<rbrakk> \<Longrightarrow> is_unit (x*y)"
  unfolding is_unit_def by (subst mult_1_left[of 1, symmetric], rule mult_dvd_mono) 

lemma unit_ring_inv: "is_unit y \<Longrightarrow> x div y = x * ring_inv y"
  by (simp add: div_mult_swap ring_inv_def is_unit_def)

lemma unit_ring_inv_ring_inv [simp]: "is_unit x \<Longrightarrow> ring_inv (ring_inv x) = x"
  unfolding is_unit_def ring_inv_def
  by (metis div_mult_mult1_if div_mult_self1_is_id dvd_mult_div_cancel mult_1_right)

lemma inv_imp_eq_ring_inv: "a * b = 1 \<Longrightarrow> ring_inv a = b"
  by (metis dvd_mult_div_cancel dvd_mult_right mult_1_right mult_left_commute one_dvd ring_inv_def)

lemma ring_inv_is_inv1 [simp]: "is_unit a \<Longrightarrow> a * ring_inv a = 1"
  unfolding is_unit_def ring_inv_def by (simp add: dvd_mult_div_cancel)

lemma ring_inv_is_inv2 [simp]: "is_unit a \<Longrightarrow> ring_inv a * a = 1"
  by (simp add: mult_commute)

     
lemma unit_ring_inv_unit [simp,intro]: "is_unit x \<Longrightarrow> is_unit (ring_inv x)"
proof-
  fix x assume "is_unit x"
  hence "1 = ring_inv x * x" by simp
  thus "is_unit (ring_inv x)" unfolding is_unit_def by (rule dvdI)
qed

lemma mult_unit_dvd_iff: "is_unit y \<Longrightarrow> x * y dvd z \<longleftrightarrow> x dvd z"
proof
  assume "is_unit y" "x * y dvd z"
  thus "x dvd z" by (simp add: dvd_mult_left)
next
  assume "is_unit y" "x dvd z"
  then obtain k where "z = x * k" unfolding dvd_def by blast
  with `is_unit y` have "z = (x * y) * (ring_inv y * k)" 
      by (simp add: mult_ac)
  thus "x * y dvd z" by (rule dvdI)
qed

lemma div_unit_dvd_iff: "is_unit y \<Longrightarrow> x div y dvd z \<longleftrightarrow> x dvd z"
    by (subst unit_ring_inv, assumption, simp add: mult_unit_dvd_iff)

lemma dvd_mult_unit_iff: "is_unit y \<Longrightarrow> x dvd z * y \<longleftrightarrow> x dvd z"
proof
  assume "is_unit y" and "x dvd z * y"
  have "z * y dvd z * (y * ring_inv y)" by (subst mult_assoc[symmetric], simp)
  also from `is_unit y` have "y * ring_inv y = 1" by simp
  finally have "z * y dvd z" by simp
  with `x dvd z * y` show "x dvd z" by (rule dvd_trans)
next
  assume "x dvd z"
  thus "x dvd z * y" by simp
qed

lemma dvd_div_unit_iff: "is_unit y \<Longrightarrow> x dvd z div y \<longleftrightarrow> x dvd z"
  by (subst unit_ring_inv, assumption, simp add: dvd_mult_unit_iff)

lemmas unit_dvd_iff = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff dvd_div_unit_iff

lemma unit_div [intro]: "\<lbrakk>is_unit x; is_unit y\<rbrakk> \<Longrightarrow> is_unit (x div y)"
  by (subst unit_ring_inv, assumption, rule unit_prod, simp_all)

lemma unit_div_mult_swap: "is_unit z \<Longrightarrow> x * (y div z) = x * y div z"
  by (simp only: unit_ring_inv[of _ y] unit_ring_inv[of _ "x*y"] mult_assoc)

lemma unit_div_commute: "is_unit y \<Longrightarrow> x div y * z = x * z div y"
  by (simp only: unit_ring_inv[of _ x] unit_ring_inv[of _ "x*z"] mult_ac)

lemma unit_imp_dvd [dest]: "is_unit y \<Longrightarrow> y dvd x"
  by (rule dvd_trans[of _ 1], simp_all add: is_unit_def)

lemma dvd_unit_imp_unit: "is_unit y \<Longrightarrow> x dvd y \<Longrightarrow> is_unit x"
  by (unfold is_unit_def, rule dvd_trans)

lemma ring_inv_0 [simp]: "ring_inv 0 = 0" unfolding ring_inv_def by simp

lemma unit_ring_inv'1: "is_unit y \<Longrightarrow> x div (y * z) = x * ring_inv y div z" 
proof-
  assume "is_unit y"
  hence "x div (y * z) = x * (ring_inv y * y) div (y * z)" by simp
  also have "... = y * (x * ring_inv y) div (y * z)"
      by (simp only: mult_ac)
  also have "... = x * ring_inv y div z"
      by (cases "y = 0", simp, rule div_mult_mult1)
  finally show ?thesis .
qed

lemma associated_comm: "associated x y \<Longrightarrow> associated y x"
  by (simp add: associated_def)

lemma associated_0 [simp]: "associated 0 b \<longleftrightarrow> b = 0"
                          "associated a 0 \<longleftrightarrow> a = 0"
  unfolding associated_def by simp_all

lemma associated_unit: "is_unit x \<Longrightarrow> associated x y \<Longrightarrow> is_unit y"
  unfolding associated_def by (fast dest: dvd_unit_imp_unit)

lemma is_unit_1 [simp]: "is_unit 1"
  unfolding is_unit_def by simp

lemma not_is_unit_0 [simp]: "\<not>is_unit 0"
  unfolding is_unit_def by auto

lemma unit_mult_left_cancel: "is_unit x \<Longrightarrow> (x * y) = (x * z) \<longleftrightarrow> y = z"
  proof-
  assume "is_unit x"
  hence "x \<noteq> 0" by auto
  thus ?thesis by (metis div_mult_self1_is_id)
qed

lemma unit_mult_right_cancel: "is_unit x \<Longrightarrow> (y * x) = (z * x) \<longleftrightarrow> y = z"
  by (simp add: mult_commute unit_mult_left_cancel)

lemma unit_div_cancel: "is_unit x \<Longrightarrow> (y div x) = (z div x) \<longleftrightarrow> y = z"
  apply (subst unit_ring_inv[of _ y], assumption)
  apply (subst unit_ring_inv[of _ z], assumption)
  apply (rule unit_mult_right_cancel, erule unit_ring_inv_unit)
  done

lemma unit_eq_div1: "is_unit y \<Longrightarrow> x div y = z \<longleftrightarrow> x = z * y"
  apply (subst unit_ring_inv, assumption)
  apply (subst unit_mult_right_cancel[symmetric], assumption)
  apply (subst mult_assoc, subst ring_inv_is_inv2, assumption, simp)
  done

lemma unit_eq_div2: "is_unit y \<Longrightarrow> x = z div y \<longleftrightarrow> x * y = z"
    by (subst (1 2) eq_commute, simp add: unit_eq_div1, subst eq_commute, rule refl)


lemma associated_iff_div_unit: "associated x y \<longleftrightarrow> (\<exists>z. is_unit z \<and> x = z * y)"
proof
  assume "associated x y"
  show "\<exists>z. is_unit z \<and> x = z * y"
  proof (cases "x = 0")
    assume "x = 0"
    thus "\<exists>z. is_unit z \<and> x = z * y" using `associated x y`
        by (intro exI[of _ 1], simp add: associated_def)
  next
    assume [simp]: "x \<noteq> 0"
    hence [simp]: "x dvd y" "y dvd x" using `associated x y`
        unfolding associated_def by simp_all
    hence "1 = x div y * (y div x)"
      by (simp add: div_mult_swap dvd_div_mult_self)
    hence "is_unit (x div y)" unfolding is_unit_def by (rule dvdI)
    moreover have "x = (x div y) * y" by (simp add: dvd_div_mult_self)
    ultimately show ?thesis by blast
  qed
next
  assume "\<exists>z. is_unit z \<and> x = z * y"
  then obtain z where "is_unit z" and "x = z * y" by blast
  hence "y = x * ring_inv z" by (simp add: algebra_simps)
  hence "x dvd y" by simp
  moreover from `x = z * y` have "y dvd x" by simp
  ultimately show "associated x y" unfolding associated_def by simp
qed

lemmas unit_simps = mult_unit_dvd_iff div_unit_dvd_iff dvd_mult_unit_iff 
                    dvd_div_unit_iff unit_div_mult_swap unit_div_commute
                    unit_mult_left_cancel unit_mult_right_cancel unit_div_cancel 
                    unit_eq_div1 unit_eq_div2

end

context ring_div
begin
lemma is_unit_neg [simp]: "is_unit (-x) \<Longrightarrow> is_unit x"
  unfolding is_unit_def by simp
lemma is_unit_neg_1 [simp]: "is_unit (-1)"
  unfolding is_unit_def by simp
end

lemma is_unit_nat [simp]: "is_unit (x::nat) \<longleftrightarrow> x = 1"
  unfolding is_unit_def by simp
lemma is_unit_int: "is_unit (x::int) \<longleftrightarrow> x = 1 \<or> x = -1"
  unfolding is_unit_def by auto



class gcd = 
  fixes gcd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and lcm :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin
  abbreviation "coprime a b \<equiv> gcd a b = 1"
end

class Gcd = gcd +
  fixes Gcd :: "'a set \<Rightarrow> 'a"
  fixes Lcm :: "'a set \<Rightarrow> 'a"
begin
end


text {*
  A Euclidean semiring is a semiring upon which the Euclidean algorithm can be
  implemented. It must provide:
  \begin{itemize}
  \item division with remainder
  \item a size function such that @{term "size (a mod b) < size b"} 
        for any @{term "b \<noteq> 0"}
  \item a normalisation factor such that two associated numbers are equal iff 
        they are the same when divided by their normalisation factors.
  \end{itemize}
  The existence of these functions makes it possible to derive gcd and lcm functions 
  for any Euclidean semiring.
*} 
class euclidean_semiring = semiring_div + 
  fixes euclidean_size :: "'a \<Rightarrow> nat"
  fixes normalisation_factor :: "'a \<Rightarrow> 'a"
  assumes mod_size_less [simp]: 
      "b \<noteq> 0 \<Longrightarrow> euclidean_size (a mod b) < euclidean_size b"
  assumes size_mult_mono:
      "b \<noteq> 0 \<Longrightarrow> euclidean_size (a * b) \<ge> euclidean_size a"
  assumes normalisation_factor_is_unit [intro,simp]: 
      "a \<noteq> 0 \<Longrightarrow> is_unit (normalisation_factor a)"
  assumes normalisation_factor_mult: "normalisation_factor (a * b) = 
      normalisation_factor a * normalisation_factor b"
  assumes normalisation_factor_unit: "is_unit x \<Longrightarrow> normalisation_factor x = x"
  assumes normalisation_factor_0 [simp]: "normalisation_factor 0 = 0"
begin

  lemma normalisation_factor_dvd [simp]:
    "a \<noteq> 0 \<Longrightarrow> normalisation_factor a dvd b" by (rule unit_imp_dvd, simp)
    
  lemma normalisation_factor_1 [simp]:
    "normalisation_factor 1 = 1" by (simp add: normalisation_factor_unit)

  lemma normalisation_factor_0_iff [simp]:
    "normalisation_factor x = 0 \<longleftrightarrow> x = 0"
  proof
    assume "normalisation_factor x = 0"
    hence "\<not>is_unit (normalisation_factor x)" by (metis not_is_unit_0)
    thus "x = 0" by force
  next
    assume "x = 0"
    thus "normalisation_factor x = 0" by simp
  qed

  lemma normalisation_factor_pow:
    "normalisation_factor (x ^ n) = normalisation_factor x ^ n"
    by (induction n) (simp_all add: normalisation_factor_mult power_Suc2)


  lemma normalisation_correct [simp]:
      "normalisation_factor (x div normalisation_factor x) = 
           (if x = 0 then 0 else 1)"
  proof (cases "x = 0", simp)
    assume "x \<noteq> 0"
    let ?nf = "normalisation_factor"
    from normalisation_factor_is_unit[OF `x \<noteq> 0`] have "?nf x \<noteq> 0"
        by (metis not_is_unit_0) 
    have "?nf (x div ?nf x) * ?nf (?nf x) = ?nf (x div ?nf x * ?nf x)" 
        by (simp add: normalisation_factor_mult)
    also have "x div ?nf x * ?nf x = x" using `x \<noteq> 0`
        by (simp add: dvd_div_mult_self)
    also have "?nf (?nf x) = ?nf x" using `x \<noteq> 0` 
        normalisation_factor_is_unit normalisation_factor_unit by simp
    finally show ?thesis using `x \<noteq> 0` and `?nf x \<noteq> 0` 
        by (metis div_mult_self2_is_id div_self)
  qed

  lemma normalisation_0_iff [simp]:
    "x div normalisation_factor x = 0 \<longleftrightarrow> x = 0"
      by (cases "x = 0", simp, subst unit_eq_div1, blast, simp)

  lemma associated_iff_normed_eq:
    "associated a b \<longleftrightarrow> a div normalisation_factor a = b div normalisation_factor b"
  proof (cases "b = 0", simp, cases "a = 0", 
             metis associated_0(1) normalisation_0_iff, rule iffI)
    let ?nf = normalisation_factor
    assume "a \<noteq> 0" "b \<noteq> 0" "a div ?nf a = b div ?nf b"
    hence "a = b * (?nf a div ?nf b)"
      apply (subst (asm) unit_eq_div1, blast, subst (asm) unit_div_commute, blast)
      apply (subst div_mult_swap, simp, simp)
      done
    with `a \<noteq> 0` `b \<noteq> 0` have "\<exists>z. is_unit z \<and> a = z * b"
        by (intro exI[of _ "?nf a div ?nf b"], force simp: mult_ac)
    with associated_iff_div_unit show "associated a b" by simp
  next
    let ?nf = normalisation_factor
    assume "a \<noteq> 0" "b \<noteq> 0" "associated a b"
    with associated_iff_div_unit obtain z where "is_unit z" and "a = z * b" by blast
    thus "a div ?nf a = b div ?nf b"
        apply (simp only: `a = z * b` normalisation_factor_mult
                    normalisation_factor_unit)
        apply (rule div_mult_mult1, force)
        done
  qed

  lemma normed_associated_imp_eq:
    "\<lbrakk>associated a b; normalisation_factor a \<in> {0,1};
      normalisation_factor b \<in> {0,1}\<rbrakk> \<Longrightarrow> a = b"
    by (simp add: associated_iff_normed_eq, elim disjE, simp_all)
    
  lemmas normalisation_factor_dvd_iff [simp] = unit_dvd_iff[OF normalisation_factor_is_unit]


  lemma euclidean_division:
    fixes a :: 'a and b :: 'a
    assumes "b \<noteq> 0"
    obtains s and t where "a = s * b + t" 
        and "euclidean_size t < euclidean_size b"
    proof-
      from div_mod_equality[of a b 0] 
          have "a = a div b * b + a mod b" by simp
      with that and assms show ?thesis by force
    qed

  lemma dvd_euclidean_size_eq_imp_dvd:
    assumes "a \<noteq> 0" and b_dvd_a: "b dvd a" and size_eq: "euclidean_size a = euclidean_size b"
    shows "a dvd b"
  proof (subst dvd_eq_mod_eq_0, rule ccontr)
    assume "b mod a \<noteq> 0"
    from b_dvd_a have b_dvd_mod: "b dvd b mod a" by (simp add: dvd_mod_iff)
    from b_dvd_mod obtain c where "b mod a = b * c" unfolding dvd_def by blast
    with `b mod a \<noteq> 0` have "c \<noteq> 0" by auto
    with `b mod a = b * c` have "euclidean_size (b mod a) \<ge> euclidean_size b"
        using size_mult_mono by force
    moreover from `a \<noteq> 0` have "euclidean_size (b mod a) < euclidean_size a"
        using mod_size_less by blast
    ultimately show False using size_eq by simp
  qed


  (* Definition of Euclidean gcd and lcm *)

  function gcd_eucl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
    "gcd_eucl a b = (if b = 0 then a div normalisation_factor a else gcd_eucl b (a mod b))"
    by (pat_completeness, simp)
    termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

  declare gcd_eucl.simps [simp del]

  lemma gcd_induct: "\<lbrakk>\<And>b. P b 0; \<And>a b. 0 \<noteq> b \<Longrightarrow> P b (a mod b) \<Longrightarrow> P a b\<rbrakk> \<Longrightarrow> P a b"
  proof (induction a b rule: gcd_eucl.induct)
    case (goal1 m n)
      thus ?case by (cases "n = 0") auto
  qed

  definition lcm_eucl where "lcm_eucl a b = 
      a * b div (gcd_eucl a b * normalisation_factor (a*b))"


  (* Somewhat complicated definition of Lcm that has the advantage of working
     for infinite sets as well *)

  definition Lcm_eucl :: "'a set \<Rightarrow> 'a" where
    "Lcm_eucl A = (if \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) then
                     let l = SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l =
                               (LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n)
                     in l div normalisation_factor l
                   else 0)"
  definition Gcd_eucl :: "'a set \<Rightarrow> 'a" where
    "Gcd_eucl A = Lcm_eucl {d. \<forall>a\<in>A. d dvd a}"

end


class euclidean_semiring_gcd = euclidean_semiring + gcd + Gcd +
  assumes gcd_gcd_eucl: "gcd = gcd_eucl" and lcm_lcm_eucl: "lcm = lcm_eucl"
  assumes Gcd_Gcd_eucl: "Gcd = Gcd_eucl" and Lcm_Lcm_eucl: "Lcm = Lcm_eucl"
begin

  (* Properties of gcd *)

  lemma gcd_red: "gcd x y = gcd y (x mod y)"
      by (metis gcd_eucl.simps mod_0 mod_by_0 gcd_gcd_eucl)

  lemma gcd_non_0: "y \<noteq> 0 \<Longrightarrow> gcd x y = gcd y (x mod y)"
      by (rule gcd_red)

  lemma gcd_0_left: "gcd 0 x = x div normalisation_factor x"
    by (simp only: gcd_gcd_eucl, subst gcd_eucl.simps, 
                   subst gcd_eucl.simps, simp add: Let_def)

  lemma gcd_0: "gcd x 0 = x div normalisation_factor x"
    by (simp only: gcd_gcd_eucl, subst gcd_eucl.simps, simp add: Let_def)

  lemma gcd_dvd1 [iff]: "gcd x y dvd x"
    and gcd_dvd2 [iff]: "gcd x y dvd y"
  proof (induction x y rule: gcd_eucl.induct)
    fix x y :: 'a
    assume IH1: "y \<noteq> 0 \<Longrightarrow> gcd y (x mod y) dvd y"
    assume IH2: "y \<noteq> 0 \<Longrightarrow> gcd y (x mod y) dvd (x mod y)"
    
    have "gcd x y dvd x \<and> gcd x y dvd y"
    proof (cases "y = 0")
      case True
        thus ?thesis by (cases "x = 0", simp_all add: gcd_0)
    next
      case False
        with IH1 and IH2 show ?thesis by (simp add: gcd_non_0 dvd_mod_iff)
    qed
    thus "gcd x y dvd x" "gcd x y dvd y" by simp_all
  qed

  lemma dvd_gcd_D1: "k dvd gcd m n \<Longrightarrow> k dvd m"
    by (rule dvd_trans, assumption, rule gcd_dvd1)

  lemma dvd_gcd_D2: "k dvd gcd m n \<Longrightarrow> k dvd n"
    by (rule dvd_trans, assumption, rule gcd_dvd2)

  lemma gcd_greatest:
    fixes k x y :: 'a
    shows "k dvd x \<Longrightarrow> k dvd y \<Longrightarrow> k dvd gcd x y"
  proof (induction x y rule: gcd_eucl.induct)
    case (goal1 x y)
      show ?case
      proof (cases "y = 0")
        assume "y = 0"
        with goal1 show ?thesis by (cases "x = 0", simp_all add: gcd_0)
      next
        assume "y \<noteq> 0"
        with goal1 show ?thesis by (simp add: gcd_non_0 dvd_mod_iff) 
      qed
  qed

  lemma dvd_gcd_iff:
    "k dvd gcd x y \<longleftrightarrow> k dvd x \<and> k dvd y"
    by (blast intro!: gcd_greatest intro: dvd_trans)

  lemmas gcd_greatest_iff = dvd_gcd_iff

  lemma gcd_zero: "gcd x y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
      by (metis dvd_0_left dvd_refl gcd_dvd1 gcd_dvd2 gcd_greatest)+

  lemma normalisation_factor_gcd [simp]:
    "normalisation_factor (gcd x y) = (if x = 0 \<and> y = 0 then 0 else 1)"
       (is "?f x y = ?g x y")
  proof (induction x y rule: gcd_eucl.induct)
    fix x y :: 'a
    assume IH: "y \<noteq> 0 \<Longrightarrow> ?f y (x mod y) = ?g y (x mod y)"
    thus "?f x y = ?g x y" by (cases "y = 0", auto simp: gcd_non_0 gcd_0)
  qed

  lemma gcdI:
    "\<lbrakk>k dvd x; k dvd y; \<And>l. l dvd x \<Longrightarrow> l dvd y \<Longrightarrow> l dvd k;
      normalisation_factor k = (if k = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> k = gcd x y"
    by (intro normed_associated_imp_eq) (auto simp: associated_def intro: gcd_greatest)

  lemma gcd_unique: "d dvd a \<and> d dvd b \<and> 
      normalisation_factor d = (if d = 0 then 0 else 1) \<and>
      (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
    by (rule, auto intro: gcdI simp: gcd_greatest gcd_zero)

  (* FIXME remove iff *)
  lemma gcd_dvd_prod [iff]: "gcd a b dvd k * b"
    using mult_dvd_mono [of 1] by auto

  lemma gcd_1_left [simp]: "gcd 1 x = 1"
    by (rule sym, rule gcdI, simp_all)

  lemma gcd_1 [simp]: "gcd x 1 = 1"
    by (rule sym, rule gcdI, simp_all)

  lemma gcd_commute: "gcd x y = gcd y x"
    by (rule gcdI, simp_all add: gcd_greatest gcd_zero)

  lemma gcd_proj2_if_dvd: 
      "y dvd x \<Longrightarrow> gcd x y = y div normalisation_factor y"
      by (cases "y = 0", simp_all add: dvd_eq_mod_eq_0 gcd_non_0 gcd_0)

  lemma gcd_proj1_if_dvd: 
      "x dvd y \<Longrightarrow> gcd x y = x div normalisation_factor x"
     by (subst gcd_commute, simp add: gcd_proj2_if_dvd)

  lemma gcd_proj1_iff: "gcd m n = m div normalisation_factor m \<longleftrightarrow> m dvd n"
  proof
    assume A: "gcd m n = m div normalisation_factor m"
    show "m dvd n"
    proof (cases "m = 0")
      assume [simp]: "m \<noteq> 0"
      from A have B: "m = gcd m n * normalisation_factor m"
        by (simp add: unit_eq_div2)
      show ?thesis by (subst B, simp add: mult_unit_dvd_iff)
    qed (insert A, simp add: gcd_zero)
  next
    assume "m dvd n"
    thus "gcd m n = m div normalisation_factor m" by (rule gcd_proj1_if_dvd)
  qed
  
  lemma gcd_proj2_iff: "gcd m n = n div normalisation_factor n \<longleftrightarrow> n dvd m"
    by (subst gcd_commute, simp add: gcd_proj1_iff)

  lemma gcd_mod1 [simp]:
     "gcd (x mod y) y = gcd x y"
     by (rule gcdI, metis dvd_mod_iff gcd_dvd1 gcd_dvd2,
         simp_all add: gcd_greatest dvd_mod_iff gcd_zero)

  lemma gcd_mod2 [simp]:
     "gcd x (y mod x) = gcd x y"
     by (rule gcdI, simp, metis dvd_mod_iff gcd_dvd1 gcd_dvd2,
         simp_all add: gcd_greatest dvd_mod_iff gcd_zero)
         
  lemma normalisation_factor_dvd' [simp]:
     "normalisation_factor x dvd x"
     by (cases "x = 0", simp_all)

  lemma gcd_mult_distrib': 
    "k div normalisation_factor k * gcd x y = gcd (k*x) (k*y)"
  proof (induction x y rule: gcd_eucl.induct)
    case (goal1 x y)
      show ?case
      proof (cases "y = 0")
        case True
          thus ?thesis by (simp add: normalisation_factor_mult gcd_0
                             algebra_simps div_mult_div_if_dvd)
      next
        case False
          hence "k div normalisation_factor k * gcd x y = 
              gcd (k * y) (k * (x mod y))" 
              using goal1 by (subst gcd_red, simp)
          also have "... = gcd (k * x) (k * y)"
              by (simp add: mult_mod_right gcd_commute)
          finally show ?thesis .
      qed
    qed

  lemma gcd_mult_distrib:
    "k * gcd x y = gcd (k*x) (k*y) * normalisation_factor k"
  proof-
    let ?nf = "normalisation_factor"
    from gcd_mult_distrib' 
        have "gcd (k*x) (k*y) = k div ?nf k * gcd x y" ..
    also have "... = k * gcd x y div ?nf k"
        by (metis dvd_div_mult dvd_eq_mod_eq_0 mod_0 normalisation_factor_dvd)
    finally show ?thesis
        by (metis dvd_0_right dvd_mult2 dvd_mult_div_cancel 
                  mult_commute normalisation_factor_dvd)
  qed

  lemma euclidean_size_gcd_le1 [simp]: "a \<noteq> 0 \<Longrightarrow> euclidean_size (gcd a b) \<le> euclidean_size a"
  proof-
    assume "a \<noteq> 0"
    have "gcd a b dvd a" by (rule gcd_dvd1)
    then obtain c where A: "a = gcd a b * c" unfolding dvd_def by blast
    with `a \<noteq> 0` show ?thesis by (subst (2) A, intro size_mult_mono) auto
  qed

  lemma euclidean_size_gcd_le2 [simp]: "b \<noteq> 0 \<Longrightarrow> euclidean_size (gcd a b) \<le> euclidean_size b"
    by (subst gcd_commute, rule euclidean_size_gcd_le1)

  lemma euclidean_size_gcd_less1:
    assumes "a \<noteq> 0" and "\<not>a dvd b"
    shows "euclidean_size (gcd a b) < euclidean_size a"
  proof (rule ccontr)
    assume "\<not>euclidean_size (gcd a b) < euclidean_size a"
    with `a \<noteq> 0` have "euclidean_size (gcd a b) = euclidean_size a"
        by (intro le_antisym, simp_all)
    with assms have "a dvd gcd a b" by (auto intro: dvd_euclidean_size_eq_imp_dvd)
    hence "a dvd b" using dvd_gcd_D2 by blast
    with `\<not>a dvd b` show False by contradiction
  qed

  lemma euclidean_size_gcd_less2:
    assumes "b \<noteq> 0" and "\<not>b dvd a"
    shows "euclidean_size (gcd a b) < euclidean_size b"
    using assms by (subst gcd_commute, rule euclidean_size_gcd_less1)


  lemma gcd_assoc [simp]: "gcd (gcd x y) z = gcd x (gcd y z)"
  proof (rule gcdI)
    have "gcd (gcd x y) z dvd gcd x y" "gcd x y dvd x" by simp_all
    thus "gcd (gcd x y) z dvd x" by (rule dvd_trans)
    
    have "gcd (gcd x y) z dvd gcd x y" "gcd x y dvd y" by simp_all
    hence "gcd (gcd x y) z dvd y" by (rule dvd_trans)
    moreover have "gcd (gcd x y) z dvd z" by simp
    ultimately show "gcd (gcd x y) z dvd gcd y z"
        by (rule gcd_greatest)
    
    show "normalisation_factor (gcd (gcd x y) z) = 
              (if gcd (gcd x y) z = 0 then 0 else 1)"
        by (auto simp: gcd_zero)

    fix l assume "l dvd x" and "l dvd gcd y z"
    with dvd_trans[OF _ gcd_dvd1] and dvd_trans[OF _ gcd_dvd2]
        have "l dvd y" and "l dvd z" by blast+
    with `l dvd x` show "l dvd gcd (gcd x y) z"
        by (intro gcd_greatest)
  qed

  lemma gcd_commute_left: "gcd x (gcd y z) = gcd y (gcd x z)"
      by (subst gcd_assoc[symmetric], subst gcd_commute, simp only: gcd_assoc)
  lemmas gcd_ac = gcd_assoc gcd_commute gcd_commute_left

  lemma gcd_mult_unit1: "is_unit a \<Longrightarrow> gcd (x*a) y = gcd x y"
    apply (rule gcdI)
    apply (rule dvd_trans, rule gcd_dvd1, simp add: unit_simps)
    apply (rule gcd_dvd2)
    apply (rule gcd_greatest, simp add: unit_simps, assumption)
    apply (subst normalisation_factor_gcd, simp add: gcd_0 gcd_zero)
    done

  lemma gcd_mult_unit2: "is_unit a \<Longrightarrow> gcd x (y*a) = gcd x y"
    by (subst gcd_commute, subst gcd_mult_unit1, assumption, rule gcd_commute)

  lemma gcd_div_unit1: "is_unit a \<Longrightarrow> gcd (x div a) y = gcd x y"
    by (simp add: unit_ring_inv gcd_mult_unit1)

  lemma gcd_div_unit2: "is_unit a \<Longrightarrow> gcd x (y div a) = gcd x y"
    by (simp add: unit_ring_inv gcd_mult_unit2)

  lemma gcd_idem: "gcd x x = x div normalisation_factor x"
    by (cases "x = 0") (simp add: gcd_0_left, rule sym, rule gcdI, simp_all)

  lemma gcd_right_idem: "gcd (gcd p q) q = gcd p q"
    apply (rule gcdI)
    apply simp
    apply (rule gcd_dvd2)
    apply (rule gcd_greatest, erule (1) gcd_greatest, assumption)
    apply (simp add: gcd_zero)
    done

  lemma gcd_left_idem: "gcd p (gcd p q) = gcd p q"
    apply (rule gcdI)
    apply simp
    apply (rule dvd_trans, rule gcd_dvd2, rule gcd_dvd2)
    apply (rule gcd_greatest, assumption, erule gcd_greatest, assumption)
    apply (simp add: gcd_zero)
    done

  interpretation gcd: abel_semigroup gcd
  proof qed (auto intro: gcd_commute)

  lemma comp_fun_idem_gcd: "comp_fun_idem gcd"
  proof
    fix a b show "gcd a \<circ> gcd b = gcd b \<circ> gcd a" unfolding o_def 
      by (intro ext) (simp only: gcd_assoc[symmetric], subst gcd_commute, rule refl)
  next
    fix a show "gcd a \<circ> gcd a = gcd a" unfolding o_def
      by (intro ext, simp add: gcd_left_idem)
  qed


  (* Coprimality *)

  lemma coprime_dvd_mult: "gcd k n = 1 \<Longrightarrow> k dvd m * n \<Longrightarrow> k dvd m"
  proof-
    let ?nf = "normalisation_factor"
    assume "gcd k n = 1" and "k dvd m * n"
    with gcd_mult_distrib[of m k n] 
        have A: "m = gcd (m * k) (m * n) * ?nf m" by simp
    from `k dvd m * n` show ?thesis by (subst A, simp_all add: gcd_greatest)
  qed


  lemma coprime_dvd_mult_iff: "gcd k n = 1 \<Longrightarrow> (k dvd m * n) = (k dvd m)"
      by (rule, rule coprime_dvd_mult, simp_all)

  lemma gcd_dvd_antisym:
       "\<lbrakk>gcd a b dvd gcd c d; gcd c d dvd gcd a b\<rbrakk> \<Longrightarrow> gcd a b = gcd c d"
  proof (rule gcdI)
    assume A: "gcd a b dvd gcd c d" and B: "gcd c d dvd gcd a b"
    have "gcd c d dvd c" by simp
    with A show "gcd a b dvd c" by (rule dvd_trans)
    have "gcd c d dvd d" by simp
    with A show "gcd a b dvd d" by (rule dvd_trans)
    show "normalisation_factor (gcd a b) = (if gcd a b = 0 then 0 else 1)"
        by (simp add: gcd_zero)
    fix l assume "l dvd c" and "l dvd d"
    hence "l dvd gcd c d" by (rule gcd_greatest)
    from this and B show "l dvd gcd a b" by (rule dvd_trans)
  qed

  lemma gcd_mult_cancel: "gcd k n = 1 \<Longrightarrow> gcd (k * m) n = gcd m n"
  proof (rule gcd_dvd_antisym)
    assume "gcd k n = 1"
    have "gcd (gcd (k * m) n) k = gcd (gcd k n) (k * m)" by (simp add: gcd_commute)
    also note `gcd k n = 1`
    finally have "gcd (gcd (k * m) n) k = 1" by simp
    hence "gcd (k * m) n dvd m" by (rule coprime_dvd_mult, simp add: mult_commute)
    moreover have "gcd (k * m) n dvd n" by simp
    ultimately show "gcd (k * m) n dvd gcd m n" by (rule gcd_greatest)
    
    have "gcd m n dvd (k * m)" and "gcd m n dvd n" by simp_all
    thus "gcd m n dvd gcd (k * m) n" by (rule gcd_greatest)
  qed

  lemma coprime_crossproduct:
  assumes [simp]: "gcd a d = 1" "gcd b c = 1"
  shows "associated (a * c) (b * d) \<longleftrightarrow> associated a b \<and> associated c d" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?rhs then show ?lhs unfolding associated_def by (fast intro: mult_dvd_mono)
  next
    assume ?lhs
    from `?lhs` have "a dvd b * d" unfolding associated_def by (metis dvd_mult_left) 
    hence "a dvd b" by (simp add: coprime_dvd_mult_iff)
    moreover from `?lhs` have "b dvd a * c" unfolding associated_def by (metis dvd_mult_left) 
    hence "b dvd a" by (simp add: coprime_dvd_mult_iff)
    moreover from `?lhs` have "c dvd d * b" 
        unfolding associated_def by (metis dvd_mult_right mult_commute) 
    hence "c dvd d" by (simp add: coprime_dvd_mult_iff gcd_commute)
    moreover from `?lhs` have "d dvd c * a"
        unfolding associated_def by (metis dvd_mult_right mult_commute) 
    hence "d dvd c" by (simp add: coprime_dvd_mult_iff gcd_commute)
    ultimately show ?rhs unfolding associated_def by simp
  qed

  lemma gcd_add1 [simp]: "gcd (m + n) n = gcd m n"
      by (cases "n = 0", simp_all add: gcd_non_0)

  lemma gcd_add2 [simp]: "gcd m (m + n) = gcd m n"
      by (subst gcd_commute, subst add_commute, subst gcd_add1, simp only: gcd_commute)

  lemma gcd_add_mult: "gcd m (k * m + n) = gcd m n"
      by (subst gcd_commute, subst gcd_red, simp)

  lemma coprimeI: "(\<And>l. \<lbrakk>l dvd x; l dvd y\<rbrakk> \<Longrightarrow> l dvd 1) \<Longrightarrow> gcd x y = 1"
      by (rule sym, rule gcdI, simp_all)

  lemma coprime: "gcd a b = 1 \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> is_unit d)"
    by (auto simp: is_unit_def intro: coprimeI gcd_greatest dvd_gcd_D1 dvd_gcd_D2)


  lemma div_gcd_coprime:
    assumes nz: "a \<noteq> 0 \<or> b \<noteq> 0"
    defines [simp]: "d \<equiv> gcd a b"
    defines [simp]: "a' \<equiv> a div d" and [simp]: "b' \<equiv> b div d"
    shows "gcd a' b' = 1"
  proof (rule coprimeI)
    fix l assume "l dvd a'" "l dvd b'"
    then obtain s t where "a' = l * s" "b' = l * t" unfolding dvd_def by blast
    moreover have "a = a' * d" "b = b' * d" by (simp_all add: dvd_div_mult_self)
    ultimately have "a = (l * d) * s" "b = (l * d) * t"
        by (metis mult_commute mult_left_commute)+
    hence "l*d dvd a" and "l*d dvd b" by force+
    hence "l*d dvd d" by (simp add: gcd_greatest)
    then obtain u where "u * l * d = d" unfolding dvd_def
        by (metis mult_commute mult_assoc)
    moreover from nz have "d \<noteq> 0" by (simp add: gcd_zero)
    ultimately have "u * l = 1" 
        by (metis div_mult_self1_is_id div_self mult_commute)
    thus "l dvd 1" by force
  qed

  lemma coprime_mult: 
    assumes da: "gcd d a = 1" and db: "gcd d b = 1"
    shows "gcd d (a * b) = 1"
    apply (subst gcd_commute)
    using da apply (subst gcd_mult_cancel)
    apply (subst gcd_commute, assumption)
    apply (subst gcd_commute, rule db)
    done

  lemma coprime_lmult:
    assumes dab: "gcd d (a * b) = 1" 
    shows "gcd d a = 1"
  proof (rule coprimeI)
    fix l assume "l dvd d" and "l dvd a"
    hence "l dvd a * b" by simp
    with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_greatest)
  qed

 lemma coprime_rmult:
   assumes dab: "gcd d (a * b) = 1"
   shows "gcd d b = 1"
  proof (rule coprimeI)
    fix l assume "l dvd d" and "l dvd b"
    hence "l dvd a * b" by simp
    with `l dvd d` and dab show "l dvd 1" by (auto intro: gcd_greatest)
  qed

  lemma coprime_mul_eq: "gcd d (a * b) = 1 \<longleftrightarrow> gcd d a = 1 \<and> gcd d b = 1"
    using coprime_rmult[of d a b] coprime_lmult[of d a b]
          coprime_mult[of d a b] by blast

  lemma gcd_coprime:
    assumes z: "gcd a b \<noteq> 0" and a: "a = a' * gcd a b" and b: "b = b' * gcd a b"
    shows "gcd a' b' = 1"
  proof-
    from z have "a \<noteq> 0 \<or> b \<noteq> 0" by (simp add: gcd_zero)
    with div_gcd_coprime have "gcd (a div gcd a b) (b div gcd a b) = 1" .
    also from assms have "a div gcd a b = a'" by (metis div_mult_self2_is_id)+
    also from assms have "b div gcd a b = b'" by (metis div_mult_self2_is_id)+
    finally show ?thesis .
  qed

  lemma coprime_power:
    assumes "0 < n"
    shows "gcd a (b ^ n) = 1 \<longleftrightarrow> gcd a b = 1"
    using assms
    proof (induct n)
     case (Suc n) then show ?case
       by (cases n) (simp_all add: coprime_mul_eq)
    qed simp

  lemma gcd_coprime_exists:
    assumes nz: "gcd a b \<noteq> 0"
    shows "\<exists>a' b'. a = a' * gcd a b \<and> b = b' * gcd a b \<and> gcd a' b' = 1"
    apply (rule_tac x = "a div gcd a b" in exI)
    apply (rule_tac x = "b div gcd a b" in exI)
    apply (insert nz, auto simp add: dvd_div_mult gcd_0_left 
               gcd_zero intro: div_gcd_coprime)
  done

  lemma coprime_exp: "gcd d a = 1 \<Longrightarrow> gcd d (a^n) = 1"
      by (induct n, simp_all add: coprime_mult)

  lemma coprime_exp2 [intro]: "gcd a b = 1 \<Longrightarrow> gcd (a^n) (b^m) = 1"
    apply (rule coprime_exp)
    apply (subst gcd_commute)
    apply (rule coprime_exp)
    apply (subst gcd_commute)
    apply assumption
    done

  lemma gcd_exp: "gcd (a^n) (b^n) = (gcd a b) ^ n"
  proof (cases "a = 0 \<and> b = 0")
    assume "a = 0 \<and> b = 0"
    thus ?thesis by (cases n, simp_all add: gcd_0_left)
  next
    assume A: "\<not>(a = 0 \<and> b = 0)"
    hence "1 = gcd ((a div gcd a b)^n) ((b div gcd a b)^n)"
      using div_gcd_coprime by (subst sym, auto simp: div_gcd_coprime)
    hence "(gcd a b) ^ n = (gcd a b) ^ n * ..." by simp
    also note gcd_mult_distrib
    also have "normalisation_factor ((gcd a b)^n) = 1"
        by (simp add: normalisation_factor_pow A)
    also have "(gcd a b)^n * (a div gcd a b)^n = a^n"
        by (subst mult_commute, subst div_power, simp,
            rule dvd_div_mult_self, rule dvd_power_same, simp)
    also have "(gcd a b)^n * (b div gcd a b)^n = b^n"
        by (subst mult_commute, subst div_power, simp,
            rule dvd_div_mult_self, rule dvd_power_same, simp)
    finally show ?thesis by simp
  qed

  lemma coprime_common_divisor: 
    "gcd a b = 1 \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> is_unit x"
     apply (subgoal_tac "x dvd gcd a b")
     apply (simp add: is_unit_def)
     apply (erule (1) gcd_greatest)
     done


  (* TODO Move *)
  lemma dvd_mult_cancel_left:
    assumes "a \<noteq> 0" and "a * b dvd a * c"
    shows "b dvd c"
  proof-
    from assms(2) obtain k where "a * c = a * b * k" unfolding dvd_def by blast
    hence "c * a = b * k * a" by (simp add: mult_ac)
    hence "c * (a div a) = b * k * (a div a)" by (simp add: div_mult_swap)
    also from `a \<noteq> 0` have "a div a = 1" by simp
    finally show ?thesis by simp
  qed

  lemma dvd_mult_cancel_right: "\<lbrakk>a \<noteq> 0; b * a dvd c * a\<rbrakk> \<Longrightarrow> b dvd c"
    by (subst (asm) (1 2) mult_commute, rule dvd_mult_cancel_left)

  lemma division_decomp: 
    assumes dc: "a dvd b * c"
    shows "\<exists>b' c'. a = b' * c' \<and> b' dvd b \<and> c' dvd c"
  proof (cases "gcd a b = 0")
    assume "gcd a b = 0"
    hence "a = 0 \<and> b = 0" by (simp add: gcd_zero)
    hence "a = 0 * c \<and> 0 dvd b \<and> c dvd c" by simp
    thus ?thesis by blast
  next
    let ?d = "gcd a b"
    assume "?d \<noteq> 0"
    from gcd_coprime_exists[OF this]
      obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd a' b' = 1"
          by blast
    from ab'(1) have "a' dvd a" unfolding dvd_def by blast
    with dc have "a' dvd b*c" using dvd_trans[of a' a "b*c"] by simp
    from dc ab'(1,2) have "a'*?d dvd (b'*?d) * c" by simp
    hence "?d * a' dvd ?d * (b' * c)" by (simp add: mult_ac)
    with `?d \<noteq> 0` have "a' dvd b' * c" by (rule dvd_mult_cancel_left)
    with coprime_dvd_mult[OF ab'(3)] 
        have "a' dvd c" by (subst (asm) mult_commute, blast)
    with ab'(1) have "a = ?d * a' \<and> ?d dvd b \<and> a' dvd c" by (simp add: mult_ac)
    thus ?thesis by blast
  qed


  (* TODO: Move *)
  lemma nonzero_pow_nonzero: "a \<noteq> 0 \<Longrightarrow> a ^ n \<noteq> 0"
    by (induction n) (simp_all add: no_zero_divisors)
  lemma zero_pow_zero: "n \<noteq> 0 \<Longrightarrow> 0 ^ n = 0"
    by (cases n, simp_all)
  lemma pow_zero_iff: "n \<noteq> 0 \<Longrightarrow> a^n = 0 \<longleftrightarrow> a = 0"
    using nonzero_pow_nonzero zero_pow_zero by auto
  (* End TODO *)

  lemma pow_divides_pow:
    assumes ab: "a ^ n dvd b ^ n" and n: "n \<noteq> 0"
    shows "a dvd b"
  proof (cases "gcd a b = 0")
    assume "gcd a b = 0"
    thus ?thesis by (simp add: gcd_zero)
  next
    let ?d = "gcd a b"
    assume "?d \<noteq> 0"
    from n obtain m where m: "n = Suc m" by (cases n, simp_all)
    from `?d \<noteq> 0` have zn: "?d ^ n \<noteq> 0" by (rule nonzero_pow_nonzero)
    from gcd_coprime_exists[OF `?d \<noteq> 0`]
      obtain a' b' where ab': "a = a' * ?d" "b = b' * ?d" "gcd a' b' = 1"
          by blast
    from ab have "(a' * ?d) ^ n dvd (b' * ?d) ^ n"
        by (simp add: ab'(1,2)[symmetric])
    hence "?d^n * a'^n dvd ?d^n * b'^n"
        by (simp only: power_mult_distrib mult_commute)
    with zn have "a'^n dvd b'^n" by (rule dvd_mult_cancel_left)
    hence "a' dvd b'^n" using dvd_trans[of a' "a'^n" "b'^n"] by (simp add: m)
    hence "a' dvd b'^m * b'" by (simp add: m mult_commute)
    with coprime_dvd_mult[OF coprime_exp[OF ab'(3), of m]]
      have "a' dvd b'" by (subst (asm) mult_commute, blast)
    hence "a'*?d dvd b'*?d" by (rule mult_dvd_mono, simp)
    with ab'(1,2) show ?thesis by simp
  qed

  lemma pow_divides_eq [simp]: "n \<noteq> 0 \<Longrightarrow> (a^n dvd b^n) = (a dvd b)"
    by (auto intro: pow_divides_pow dvd_power_same)

  lemma divides_mult:
    assumes mr: "m dvd r" and nr: "n dvd r" and mn: "gcd m n = 1"
    shows "m * n dvd r"
  proof-
    from mr nr obtain m' n' where m': "r = m*m'" and n': "r = n*n'"
      unfolding dvd_def by blast
    from mr n' have "m dvd n'*n" by (simp add: mult_commute)
    hence "m dvd n'" using coprime_dvd_mult_iff[OF mn] by simp
    then obtain k where k: "n' = m*k" unfolding dvd_def by blast
    with n' have "r = m * n * k" by (simp add: mult_ac)
    thus ?thesis unfolding dvd_def by blast
  qed

  lemma coprime_plus_one [simp]: "gcd (n + 1) n = 1"
      by (subst add_commute, simp)

  lemma setprod_coprime [rule_format]:
      "(\<forall>i\<in>A. gcd (f i) x = 1) \<longrightarrow> gcd (\<Prod>i\<in>A. f i) x = 1"
    apply (cases "finite A")
    apply (induct set: finite)
    apply (auto simp add: gcd_mult_cancel)
    done

  lemma coprime_divisors: 
    assumes "d dvd a" "e dvd b" "gcd a b = 1"
    shows "gcd d e = 1" 
  proof-
    from assms obtain k l where "a = d * k" "b = e * l"
        unfolding dvd_def by blast
    with assms have "gcd (d * k) (e * l) = 1" by simp
    hence "gcd (d * k) e = 1" by (rule coprime_lmult)
    also have "gcd (d * k) e = gcd e (d * k)" by (rule gcd_commute)
    finally have "gcd e d = 1" by (rule coprime_lmult)
    thus ?thesis by (subst gcd_commute)
  qed

  lemma invertible_coprime: "x * y mod m = 1 \<Longrightarrow> gcd x m = 1"
      by (metis coprime_lmult gcd_1 gcd_commute gcd_red)


  subsection {* Proerties of lcm *}

  lemma lcm_gcd: "lcm a b = a * b div (gcd a b * normalisation_factor (a*b))"
      by (simp only: lcm_lcm_eucl gcd_gcd_eucl lcm_eucl_def)

  lemma lcm_commute: "lcm x y = lcm y x"
      by (simp add: lcm_gcd gcd_commute mult_commute)

  lemma lcm_gcd_prod: "lcm a b * gcd a b = a * b div normalisation_factor (a*b)"
  proof (cases "a * b = 0")
    let ?nf = normalisation_factor
    assume "a * b \<noteq> 0"
    hence "gcd a b \<noteq> 0" by (auto simp add: gcd_zero)
    from lcm_gcd have "lcm a b * gcd a b = gcd a b * (a * b div (?nf (a*b) * gcd a b))" 
        by (simp add: mult_ac)
    also from `a * b \<noteq> 0` have "... = a * b div ?nf (a*b)" 
        by (simp_all add: unit_ring_inv'1 dvd_mult_div_cancel unit_ring_inv)
    finally show ?thesis .
  qed (simp add: lcm_gcd)

  lemma lcm_dvd1 [iff]: "x dvd lcm x y"
  proof (cases "x*y = 0")
    assume "x * y \<noteq> 0"
    hence "gcd x y \<noteq> 0" by (auto simp: gcd_zero)
    let ?c = "ring_inv (normalisation_factor (x*y))"
    from `x * y \<noteq> 0` have [simp]: "is_unit (normalisation_factor (x*y))" by simp
    from lcm_gcd_prod[of x y] have "lcm x y * gcd x y = x * ?c * y"
        by (simp add: mult_ac unit_ring_inv)
    hence "lcm x y * gcd x y div gcd x y = x * ?c * y div gcd x y" by simp
    with `gcd x y \<noteq> 0` have "lcm x y = x * ?c * y div gcd x y"
        by (subst (asm) div_mult_self2_is_id, simp_all)
    also have "... = x * (?c * y div gcd x y)"
        by (metis div_mult_swap gcd_dvd2 mult_assoc)
    finally show ?thesis by (rule dvdI)
  qed (simp add: lcm_gcd)

  lemma lcm_dvd2 [iff]: "y dvd lcm x y"
      by (subst lcm_commute, simp)

  lemma dvd_lcm_D1: "lcm m n dvd k \<Longrightarrow> m dvd k"
    by (rule dvd_trans, rule lcm_dvd1, assumption)

  lemma dvd_lcm_D2: "lcm m n dvd k \<Longrightarrow> n dvd k"
    by (rule dvd_trans, rule lcm_dvd2, assumption)

  lemma lcm_least: "\<lbrakk>a dvd k; b dvd k\<rbrakk> \<Longrightarrow> lcm a b dvd k"
  proof (cases "k = 0")
    let ?nf = normalisation_factor
    assume "k \<noteq> 0"
    hence "is_unit (?nf k)" by simp
    hence "?nf k \<noteq> 0" by (metis not_is_unit_0)

    assume A: "a dvd k" "b dvd k"
    hence "gcd a b \<noteq> 0" using `k \<noteq> 0` by (auto simp add: gcd_zero)
    from A obtain r s where ar: "k = a * r" and bs: "k = b * s" 
        unfolding dvd_def by blast
    with `k \<noteq> 0` have "r * s \<noteq> 0" 
        by (intro notI) (drule divisors_zero, elim disjE, simp_all)
    hence "is_unit (?nf (r * s))" by simp
    let ?c = "?nf k div ?nf (r*s)"
    from `is_unit (?nf k)` and `is_unit (?nf (r * s))` have "is_unit ?c" by (rule unit_div)
    hence "?c \<noteq> 0" using not_is_unit_0 by fast 
    from ar bs have "k * k * gcd s r = ?nf k * k * gcd (k * s) (k * r)"
        by (subst mult_assoc, subst gcd_mult_distrib[of k s r],
            simp only: mult_commute mult_assoc)
    also have "... = ?nf k * k * gcd ((r*s) * a) ((r*s) * b)"
        by (subst (3) `k = a * r`, subst (3) `k = b * s`, simp add: algebra_simps)
    also have "... = ?c * r*s * k * gcd a b" using `r * s \<noteq> 0`
        by (subst gcd_mult_distrib'[symmetric], simp add: algebra_simps unit_simps)
    finally have "(a*r) * (b*s) * gcd s r = ?c * k * r * s * gcd a b"
        by (subst ar[symmetric], subst bs[symmetric], simp add: mult_ac)
    hence "a * b * gcd s r * (r * s) = ?c * k * gcd a b * (r * s)"
        by (simp add: algebra_simps)
    hence "?c * k * gcd a b = a * b * gcd s r" using `r * s \<noteq> 0`
        by (metis div_mult_self2_is_id)
    also have "... = lcm a b * gcd a b * gcd s r * ?nf (a*b)"
        by (subst lcm_gcd_prod[of a b], metis gcd_mult_distrib gcd_mult_distrib') 
    also have "... = lcm a b * gcd s r * ?nf (a*b) * gcd a b"
        by (simp add: algebra_simps)
    finally have "k * ?c = lcm a b * gcd s r * ?nf (a*b)" using `gcd a b \<noteq> 0`
        by (metis mult_commute div_mult_self2_is_id)
    hence "k = lcm a b * (gcd s r * ?nf (a*b)) div ?c" using `?c \<noteq> 0`
        by (metis div_mult_self2_is_id mult_assoc) 
    also have "... = lcm a b * (gcd s r * ?nf (a*b) div ?c)" using `is_unit ?c`
        by (simp add: unit_simps)
    finally show ?thesis by (rule dvdI)
  qed simp

  lemma gcd_dvd_lcm [simp]: "gcd a b dvd lcm a b"
      by (metis dvd_trans gcd_dvd2 lcm_dvd2)
  
  lemma lcm_zero: "lcm a b = 0 \<longleftrightarrow> a = 0 \<or> b = 0"
  proof-
    let ?nf = normalisation_factor
    {
      assume "a \<noteq> 0" "b \<noteq> 0"
      hence "a * b div ?nf (a * b) \<noteq> 0" by (simp add: no_zero_divisors)
      moreover from `a \<noteq> 0` and `b \<noteq> 0` have "gcd a b \<noteq> 0" by (simp add: gcd_zero)
      ultimately have "lcm a b \<noteq> 0" using lcm_gcd_prod[of a b] by (intro notI, simp)
    } moreover {
      assume "a = 0 \<or> b = 0"
      hence "lcm a b = 0" by (elim disjE, simp_all add: lcm_gcd)
    }
    ultimately show ?thesis by blast
  qed

  lemmas lcm_0_iff = lcm_zero

  lemma gcd_lcm: 
      "lcm a b \<noteq> 0 \<Longrightarrow> gcd a b = a * b div (lcm a b * normalisation_factor (a*b))"
  proof-
    assume "lcm a b \<noteq> 0"
    hence "gcd a b \<noteq> 0" by (simp add: gcd_zero lcm_zero)
    let ?c = "normalisation_factor (a*b)"
    from `lcm a b \<noteq> 0` have "?c \<noteq> 0" by (intro notI, simp add: lcm_zero no_zero_divisors)
    hence "is_unit ?c" by simp
    from lcm_gcd_prod[of a b] have "gcd a b = a * b div ?c div lcm a b"
        by (subst (2) div_mult_self2_is_id[OF `lcm a b \<noteq> 0`, symmetric], simp add: mult_ac)
    also from `is_unit ?c` have "... = a * b div (?c * lcm a b)"
        by (simp only: unit_ring_inv'1 unit_ring_inv)
    finally show ?thesis by (simp only: mult_commute)
  qed

  lemma normalisation_factor_lcm [simp]:
      "normalisation_factor (lcm a b) = (if a = 0 \<or> b = 0 then 0 else 1)"
  proof (cases "a = 0 \<or> b = 0")
    case True
      thus ?thesis by (simp add: lcm_gcd, metis div_0 mult_commute 
                           mult_zero_left normalisation_factor_0)
  next
    case False
    let ?nf = normalisation_factor
    from lcm_gcd_prod[of a b] 
        have "?nf (lcm a b) * ?nf (gcd a b) = ?nf (a*b) div ?nf (a*b)"
        by (metis div_by_0 div_self normalisation_correct 
                  normalisation_factor_0 normalisation_factor_mult)
    also have "... = (if a*b = 0 then 0 else 1)"
        by (cases "a*b = 0", simp, subst div_self,
            metis dvd_0_left normalisation_factor_dvd, simp)
    finally show ?thesis using False by (simp add: no_zero_divisors)
  qed

  lemma lcm_1_iff: "lcm a b = 1 \<longleftrightarrow> is_unit a \<and> is_unit b"
  proof
    assume "lcm a b = 1"
    thus "is_unit a \<and> is_unit b" unfolding is_unit_def by auto
  next
    assume "is_unit a \<and> is_unit b"
    hence "a dvd 1" and "b dvd 1" unfolding is_unit_def by simp_all
    hence "is_unit (lcm a b)" unfolding is_unit_def by (rule lcm_least)
    hence "lcm a b = normalisation_factor (lcm a b)"
        by (subst normalisation_factor_unit, simp_all)
    also have "\<dots> = 1" using `is_unit a \<and> is_unit b` by (auto simp add: is_unit_def)
    finally show "lcm a b = 1" .
  qed

  lemma lcmI:
    "\<lbrakk>x dvd k; y dvd k; \<And>l. x dvd l \<Longrightarrow> y dvd l \<Longrightarrow> k dvd l;
      normalisation_factor k = (if k = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> k = lcm x y"
    by (intro normed_associated_imp_eq) (auto simp: associated_def intro: lcm_least)

  lemma lcm_0_left [simp]: "lcm 0 x = 0"
    by (rule sym, rule lcmI, simp_all)

  lemma lcm_0 [simp]: "lcm x 0 = 0"
    by (rule sym, rule lcmI, simp_all)

  lemma lcm_unique: "a dvd d \<and> b dvd d \<and> 
      normalisation_factor d = (if d = 0 then 0 else 1) \<and>
      (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
    by (rule, auto intro: lcmI simp: lcm_least lcm_zero)

  lemma dvd_lcm_I1 [simp]: "k dvd m \<Longrightarrow> k dvd lcm m n"
    by (metis lcm_dvd1 dvd_trans)
  lemma dvd_lcm_I2 [simp]: "k dvd n \<Longrightarrow> k dvd lcm m n"
    by (metis lcm_dvd2 dvd_trans)

  lemma lcm_1_left [simp]: "lcm 1 x = x div normalisation_factor x"
      by (cases "x = 0") (simp, rule sym, rule lcmI, simp_all)

  lemma lcm_1_right [simp]: "lcm x 1 = x div normalisation_factor x"
     by (subst lcm_commute, simp)

  lemma lcm_coprime: "gcd a b = 1 \<Longrightarrow> lcm a b = a * b div normalisation_factor (a*b)"
     by (subst lcm_gcd) simp

  lemma lcm_proj1_if_dvd: 
      "y dvd x \<Longrightarrow> lcm x y = x div normalisation_factor x"
    by (cases "x = 0") (simp, rule sym, rule lcmI, simp_all)

  lemma lcm_proj2_if_dvd: 
      "x dvd y \<Longrightarrow> lcm x y = y div normalisation_factor y"
      by (subst lcm_commute, simp add: lcm_proj1_if_dvd)

  lemma lcm_proj1_iff: "lcm m n = m div normalisation_factor m \<longleftrightarrow> n dvd m"
  proof
    assume A: "lcm m n = m div normalisation_factor m"
    show "n dvd m"
    proof (cases "m = 0")
      assume [simp]: "m \<noteq> 0"
      from A have B: "m = lcm m n * normalisation_factor m"
        by (simp add: unit_eq_div2)
      show ?thesis by (subst B, simp)
    qed simp
  next
    assume "n dvd m"
    thus "lcm m n = m div normalisation_factor m" by (rule lcm_proj1_if_dvd)
  qed
  
  lemma lcm_proj2_iff: "lcm m n = n div normalisation_factor n \<longleftrightarrow> m dvd n"
    by (subst lcm_commute, simp add: lcm_proj1_iff)

  lemma lcm_assoc [simp]: "lcm (lcm x y) z = lcm x (lcm y z)"
  proof (rule lcmI)
    have "x dvd lcm x y" and "lcm x y dvd lcm (lcm x y) z" by simp_all
    thus "x dvd lcm (lcm x y) z" by (rule dvd_trans)
    
    have "y dvd lcm x y" and "lcm x y dvd lcm (lcm x y) z" by simp_all
    hence "y dvd lcm (lcm x y) z" by (rule dvd_trans)
    moreover have "z dvd lcm (lcm x y) z" by simp
    ultimately show "lcm y z dvd lcm (lcm x y) z" by (rule lcm_least)

    fix l assume "x dvd l" and "lcm y z dvd l"
    have "y dvd lcm y z" by simp
    from this and `lcm y z dvd l` have "y dvd l" by (rule dvd_trans)
    have "z dvd lcm y z" by simp
    from this and `lcm y z dvd l` have "z dvd l" by (rule dvd_trans)
    from `x dvd l` and `y dvd l` have "lcm x y dvd l" by (rule lcm_least)
    from this and `z dvd l` show "lcm (lcm x y) z dvd l" by (rule lcm_least)
  qed (simp add: lcm_zero)

  lemma lcm_commute_left: "lcm x (lcm y z) = lcm y (lcm x z)"
      by (subst lcm_assoc[symmetric], subst lcm_commute, simp only: lcm_assoc)
  lemmas lcm_ac = lcm_assoc lcm_commute lcm_commute_left


  lemma euclidean_size_lcm_le1: 
    "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> euclidean_size a \<le> euclidean_size (lcm a b)"
  proof-
    assume "a \<noteq> 0" "b \<noteq> 0"
    have "a dvd lcm a b" by (rule lcm_dvd1)
    then obtain c where A: "lcm a b = a * c" unfolding dvd_def by blast
    with `a \<noteq> 0` and `b \<noteq> 0` have "c \<noteq> 0" by (auto simp: lcm_zero)
    thus ?thesis by (subst A, intro size_mult_mono)
  qed

  lemma euclidean_size_lcm_le2:
    "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> euclidean_size b \<le> euclidean_size (lcm a b)"
    by (subst lcm_commute, rule euclidean_size_lcm_le1)

  lemma euclidean_size_lcm_less1:
    assumes "b \<noteq> 0" and "\<not>b dvd a"
    shows "euclidean_size a < euclidean_size (lcm a b)"
  proof (rule ccontr)
    from assms have "a \<noteq> 0" by auto
    assume "\<not>euclidean_size a < euclidean_size (lcm a b)"
    with `a \<noteq> 0` and `b \<noteq> 0` have "euclidean_size (lcm a b) = euclidean_size a"
        by (intro le_antisym, simp, intro euclidean_size_lcm_le1)
    with assms have "lcm a b dvd a" 
        by (rule_tac dvd_euclidean_size_eq_imp_dvd) (auto simp: lcm_zero)
    hence "b dvd a" by (rule dvd_lcm_D2)
    with `\<not>b dvd a` show False by contradiction
  qed

  lemma euclidean_size_lcm_less2:
    assumes "a \<noteq> 0" and "\<not>a dvd b"
    shows "euclidean_size b < euclidean_size (lcm a b)"
    using assms by (subst lcm_commute, rule euclidean_size_lcm_less1)


  lemma lcm_mult_unit1: "is_unit a \<Longrightarrow> lcm (x*a) y = lcm x y"
    apply (rule lcmI)
    apply (rule dvd_trans[of _ "x*a"], simp, rule lcm_dvd1)
    apply (rule lcm_dvd2)
    apply (rule lcm_least, simp add: unit_simps, assumption)
    apply (subst normalisation_factor_lcm, simp add: lcm_zero)
    done

  lemma lcm_mult_unit2: "is_unit a \<Longrightarrow> lcm x (y*a) = lcm x y"
    by (subst lcm_commute, subst lcm_mult_unit1, assumption, rule lcm_commute)

  lemma lcm_div_unit1: "is_unit a \<Longrightarrow> lcm (x div a) y = lcm x y"
    by (simp add: unit_ring_inv lcm_mult_unit1)

  lemma lcm_div_unit2: "is_unit a \<Longrightarrow> lcm x (y div a) = lcm x y"
    by (simp add: unit_ring_inv lcm_mult_unit2)

  lemma lcm_left_idem: "lcm p (lcm p q) = lcm p q"
    apply (rule lcmI)
    apply simp
    apply (subst lcm_assoc[symmetric], rule lcm_dvd2)
    apply (rule lcm_least, assumption)
    apply (erule (1) lcm_least)
    apply (auto simp: lcm_zero)
    done

  lemma lcm_right_idem: "lcm (lcm p q) q = lcm p q"
    apply (rule lcmI)
    apply (subst lcm_assoc, rule lcm_dvd1)
    apply (rule lcm_dvd2)
    apply (rule lcm_least, erule (1) lcm_least, assumption)
    apply (auto simp: lcm_zero)
    done


  interpretation lcm: abel_semigroup lcm
  proof qed (auto intro: lcm_commute)

  lemma comp_fun_idem_lcm: "comp_fun_idem lcm"
  proof
    fix a b show "lcm a \<circ> lcm b = lcm b \<circ> lcm a" unfolding o_def 
      by (intro ext) (simp only: lcm_assoc[symmetric], subst lcm_commute, rule refl)
  next
    fix a show "lcm a \<circ> lcm a = lcm a" unfolding o_def
      by (intro ext, simp add: lcm_left_idem)
  qed


  subsection {* Properties of Lcm *}

  lemma dvd_Lcm [simp]: "x \<in> A \<Longrightarrow> x dvd Lcm A"
    and Lcm_dvd [simp]: "(\<forall>x\<in>A. x dvd l') \<Longrightarrow> Lcm A dvd l'"
    and normalisation_factor_Lcm [simp]: 
          "normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)"
  proof-
    have "(\<forall>x\<in>A. x dvd Lcm A) \<and> (\<forall>l'. (\<forall>x\<in>A. x dvd l') \<longrightarrow> Lcm A dvd l') \<and>
          normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" (is ?thesis)
    proof (cases "\<exists>l. l \<noteq>  0 \<and> (\<forall>x\<in>A. x dvd l)")
      case False
      hence "Lcm A = 0" by (auto simp: Lcm_Lcm_eucl Lcm_eucl_def)
      with False show ?thesis by auto

    next

      case True
      then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l\<^sub>0)" by blast
      def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
        apply (subst n_def)
        apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
        apply (rule exI[of _ l\<^sub>0])
        apply (simp add: l\<^sub>0_props)
        done
      from someI_ex[OF this] have "l \<noteq> 0" and "\<forall>x\<in>A. x dvd l" and "euclidean_size l = n" 
          unfolding l_def by simp_all
      {
        fix l' assume "\<forall>x\<in>A. x dvd l'"
        with `\<forall>x\<in>A. x dvd l` have "\<forall>x\<in>A. x dvd gcd l l'" by (auto intro: gcd_greatest)
        moreover from `l \<noteq> 0` have "gcd l l' \<noteq> 0" by (simp add: gcd_zero)
        ultimately have "\<exists>b. b \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd b) \<and> euclidean_size b = euclidean_size (gcd l l')"
            by (intro exI[of _ "gcd l l'"], auto)
        hence "euclidean_size (gcd l l') \<ge> n" by (subst n_def) (rule Least_le)
        moreover have "euclidean_size (gcd l l') \<le> n"
        proof-
          have "gcd l l' dvd l" by simp
          then obtain a where "l = gcd l l' * a" unfolding dvd_def by blast
          with `l \<noteq> 0` have "a \<noteq> 0" by auto
          hence "euclidean_size (gcd l l') \<le> euclidean_size (gcd l l' * a)"
              by (rule size_mult_mono)
          also have "gcd l l' * a = l" using `l = gcd l l' * a` ..
          also note `euclidean_size l = n`
          finally show "euclidean_size (gcd l l') \<le> n" .
        qed
        ultimately have "euclidean_size l = euclidean_size (gcd l l')" 
            by (intro le_antisym, simp_all add: `euclidean_size l = n`)
        with `l \<noteq> 0` have "l dvd gcd l l'" by (blast intro: dvd_euclidean_size_eq_imp_dvd)
        hence "l dvd l'" by (blast dest: dvd_gcd_D2)
      }

      with `(\<forall>x\<in>A. x dvd l)` and normalisation_factor_is_unit[OF `l \<noteq> 0`] and `l \<noteq> 0`
          have "(\<forall>x\<in>A. x dvd l div normalisation_factor l) \<and> 
                (\<forall>l'. (\<forall>x\<in>A. x dvd l') \<longrightarrow> l div normalisation_factor l dvd l') \<and>
                normalisation_factor (l div normalisation_factor l) = 
                    (if l div normalisation_factor l = 0 then 0 else 1)"
          by (auto simp: unit_simps)
      also from True have "l div normalisation_factor l = Lcm A"
          by (simp add: Lcm_Lcm_eucl Lcm_eucl_def Let_def n_def l_def)
      finally show ?thesis .
    qed
    note A = this

    {fix x assume "x \<in> A" thus "x dvd Lcm A" using A by blast}
    {fix l' assume "\<forall>x\<in>A. x dvd l'" thus "Lcm A dvd l'" using A by blast}
    from A show "normalisation_factor (Lcm A) = (if Lcm A = 0 then 0 else 1)" by blast
  qed
    
  lemma LcmI:
    "\<lbrakk>\<And>x. x\<in>A \<Longrightarrow> x dvd l; \<And>l'. (\<forall>x\<in>A. x dvd l') \<Longrightarrow> l dvd l';
      normalisation_factor l = (if l = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> l = Lcm A"
    by (intro normed_associated_imp_eq)
       (auto intro: Lcm_dvd dvd_Lcm simp: associated_def)

  lemma Lcm_subset: "A \<subseteq> B \<Longrightarrow> Lcm A dvd Lcm B"
    by (blast intro: Lcm_dvd dvd_Lcm)

  lemma Lcm_Un: "Lcm (A \<union> B) = lcm (Lcm A) (Lcm B)"
    apply (rule lcmI)
    apply (blast intro: Lcm_subset)
    apply (blast intro: Lcm_subset)
    apply (intro Lcm_dvd ballI, elim UnE)
    apply (rule dvd_trans, erule dvd_Lcm, assumption)
    apply (rule dvd_trans, erule dvd_Lcm, assumption)
    apply simp
    done

  lemma Lcm_1_iff: "Lcm A = 1 \<longleftrightarrow> (\<forall>x\<in>A. is_unit x)"
  proof
    assume "Lcm A = 1"
    thus "\<forall>x\<in>A. is_unit x" unfolding is_unit_def by auto
  qed (rule LcmI[symmetric], auto)

  lemma Lcm_no_units: "Lcm A = Lcm (A - {x. is_unit x})"
  proof-
    have "(A - {x. is_unit x}) \<union> {x\<in>A. is_unit x} = A" by blast
    hence "Lcm A = lcm (Lcm (A - {x. is_unit x})) (Lcm {x\<in>A. is_unit x})"
        by (simp add: Lcm_Un[symmetric])
    also have "Lcm {x\<in>A. is_unit x} = 1" by (simp add: Lcm_1_iff)
    finally show ?thesis by simp
  qed

  lemma Lcm_empty [simp]: "Lcm {} = 1"
    by (simp add: Lcm_1_iff)

  lemma Lcm_eq_0 [simp]: "0 \<in> A \<Longrightarrow> Lcm A = 0"
    by (drule dvd_Lcm) simp

  lemma Lcm0_iff': "Lcm A = 0 \<longleftrightarrow> \<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))"
  proof
    assume "Lcm A = 0"
    show "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))"
    proof
      assume ex: "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l)"
      then obtain l\<^sub>0 where l\<^sub>0_props: "l\<^sub>0 \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l\<^sub>0)" by blast
      def n \<equiv> "LEAST n. \<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      def l \<equiv> "SOME l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
      have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l) \<and> euclidean_size l = n"
        apply (subst n_def)
        apply (rule LeastI[of _ "euclidean_size l\<^sub>0"])
        apply (rule exI[of _ l\<^sub>0])
        apply (simp add: l\<^sub>0_props)
        done
      from someI_ex[OF this] have "l \<noteq> 0" unfolding l_def by simp_all
      hence "l div normalisation_factor l \<noteq> 0" by simp
      also from ex have "l div normalisation_factor l = Lcm A"
          by (simp only: Lcm_Lcm_eucl Lcm_eucl_def n_def l_def if_True Let_def)
      finally show False using `Lcm A = 0` by contradiction
    qed
  qed (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)


  (* TODO: Move *)
  lemma dvd_setprod [intro]:
    assumes "finite A" and "x \<in> A"
    shows "f x dvd setprod f A"
  proof
    from `finite A` have "setprod f (insert x (A - {x})) = f x * setprod f (A - {x})"
        by (intro setprod.insert) auto
    also from `x \<in> A` have "insert x (A - {x}) = A" by blast
    finally show "setprod f A = f x * setprod f (A - {x})" .
  qed

  lemma Lcm0_iff [simp]: "finite A \<Longrightarrow> Lcm A = 0 \<longleftrightarrow> 0 \<in> A"
  proof-
    assume "finite A"
    have "0 \<in> A \<Longrightarrow> Lcm A = 0"  by (intro dvd_0_left dvd_Lcm)
    moreover {
      assume "0 \<notin> A"
      hence "\<Prod>A \<noteq> 0" 
        apply (induction rule: finite_induct[OF `finite A`]) 
        apply simp
        apply (subst setprod.insert, assumption, assumption)
        apply (rule no_zero_divisors)
        apply blast+
        done
      moreover from `finite A` have "\<forall>x\<in>A. x dvd \<Prod>A" by (intro ballI dvd_setprod)
      ultimately have "\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l)" by blast
      with Lcm0_iff' have "Lcm A \<noteq> 0" by simp
    }
    ultimately show "Lcm A = 0 \<longleftrightarrow> 0 \<in> A" by blast
  qed

  lemma Lcm_no_multiple: "(\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>x\<in>A. \<not>x dvd m)) \<Longrightarrow> Lcm A = 0"
  proof-
    assume "\<forall>m. m \<noteq> 0 \<longrightarrow> (\<exists>x\<in>A. \<not>x dvd m)"
    hence "\<not>(\<exists>l. l \<noteq> 0 \<and> (\<forall>x\<in>A. x dvd l))" by blast
    thus "Lcm A = 0" by (simp only: Lcm_Lcm_eucl Lcm_eucl_def if_False)
  qed

  lemma Lcm_insert [simp]: "Lcm (insert a A) = lcm a (Lcm A)"
  proof (rule lcmI)
    fix l assume "a dvd l" and "Lcm A dvd l"
    hence "\<forall>x\<in>A. x dvd l" by (blast intro: dvd_trans dvd_Lcm)
    with `a dvd l` show "Lcm (insert a A) dvd l" by (force intro: Lcm_dvd)
  qed (auto intro: Lcm_dvd dvd_Lcm simp: normalisation_factor_Lcm)
 
  lemma Lcm_finite:
    assumes "finite A"
    shows "Lcm A = Finite_Set.fold lcm 1 A"
    by (induction rule: finite.induct[OF `finite A`])
       (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_lcm])

  lemma Lcm_set [code, code_unfold]:
    "Lcm (set xs) = fold lcm xs 1"
    using comp_fun_idem.fold_set_fold[OF comp_fun_idem_lcm] Lcm_finite 
        by (simp add: lcm_commute)

  lemma Lcm_singleton [simp]: "Lcm {a} = a div normalisation_factor a"
      by simp

  lemma Lcm_2 [simp]: "Lcm {a,b} = lcm a b"
      by (simp only: Lcm_insert Lcm_empty lcm_1_right)
         (cases "b = 0", simp, rule lcm_div_unit2, simp)

 lemma Lcm_coprime:
    assumes finite: "finite A" and ne: "A \<noteq> {}" 
    assumes coprime: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1"
    shows "Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)"
  proof (insert coprime, induction rule: finite_ne_induct[OF finite ne])
    case (goal2 a A)
      have "Lcm (insert a A) = lcm a (Lcm A)" by simp
      also from goal2 have "Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)" by blast
      also have "lcm a \<dots> = lcm a (\<Prod>A)" by (cases "\<Prod>A = 0") (simp_all add: lcm_div_unit2)
      also from goal2 have "gcd a (\<Prod>A) = 1" by (subst gcd_commute, intro setprod_coprime) auto
      with goal2 have "lcm a (\<Prod>A) = \<Prod>(insert a A) div normalisation_factor (\<Prod>(insert a A))"
          by (simp add: lcm_coprime)
      finally show ?case .
  qed simp
      
  lemma Lcm_coprime':
    "\<lbrakk>card A \<noteq> 0; \<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a \<noteq> b \<Longrightarrow> gcd a b = 1\<rbrakk>
      \<Longrightarrow> Lcm A = \<Prod>A div normalisation_factor (\<Prod>A)"
    by (rule Lcm_coprime) (simp_all add: card_eq_0_iff)



 (* Properties of Gcd *)

  lemma Gcd_Lcm: "Gcd A = Lcm {d. \<forall>x\<in>A. d dvd x}"
    by (simp add: Gcd_Gcd_eucl Lcm_Lcm_eucl Gcd_eucl_def)

  lemma Gcd_dvd [simp]: "x \<in> A \<Longrightarrow> Gcd A dvd x"
    and dvd_Gcd [simp]: "(\<forall>x\<in>A. g' dvd x) \<Longrightarrow> g' dvd Gcd A"
    and normalisation_factor_Gcd [simp]: 
          "normalisation_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
  proof-
    fix x assume "x \<in> A"
    hence "Lcm {d. \<forall>x\<in>A. d dvd x} dvd x" by (intro Lcm_dvd) blast
    thus "Gcd A dvd x" by (simp add: Gcd_Lcm)
  next
    fix g' assume "\<forall>x\<in>A. g' dvd x"
    hence "g' dvd Lcm {d. \<forall>x\<in>A. d dvd x}" by (intro dvd_Lcm) blast
    thus "g' dvd Gcd A" by (simp add: Gcd_Lcm)
  next
    show "normalisation_factor (Gcd A) = (if Gcd A = 0 then 0 else 1)"
      by (simp add: Gcd_Lcm normalisation_factor_Lcm)
  qed

  lemma GcdI:
    "\<lbrakk>\<And>x. x\<in>A \<Longrightarrow> l dvd x; \<And>l'. (\<forall>x\<in>A. l' dvd x) \<Longrightarrow> l' dvd l;
      normalisation_factor l = (if l = 0 then 0 else 1)\<rbrakk> \<Longrightarrow> l = Gcd A"
    by (intro normed_associated_imp_eq)
       (auto intro: Gcd_dvd dvd_Gcd simp: associated_def)

  lemma Lcm_Gcd: "Lcm A = Gcd {m. \<forall>x\<in>A. x dvd m}"
    by (rule LcmI[symmetric]) (auto intro: dvd_Gcd Gcd_dvd)

  lemma Gcd_0_iff: "Gcd A = 0 \<longleftrightarrow> A \<subseteq> {0}"
    apply (rule iffI)
    apply (rule subsetI, drule Gcd_dvd, simp)
    apply (auto intro: GcdI[symmetric])
    done

  lemma Gcd_empty [simp]: "Gcd {} = 0"
    by (simp add: Gcd_0_iff)

  lemma Gcd_1: "1 \<in> A \<Longrightarrow> Gcd A = 1"
    by (intro GcdI[symmetric]) (auto intro: Gcd_dvd dvd_Gcd)

  lemma Gcd_insert [simp]: "Gcd (insert a A) = gcd a (Gcd A)"
  proof (rule gcdI)
    fix l assume "l dvd a" and "l dvd Gcd A"
    hence "\<forall>x\<in>A. l dvd x" by (blast intro: dvd_trans Gcd_dvd)
    with `l dvd a` show "l dvd Gcd (insert a A)" by (force intro: Gcd_dvd)
  qed (auto intro: Gcd_dvd dvd_Gcd simp: normalisation_factor_Gcd)

  lemma Gcd_finite:
    assumes "finite A"
    shows "Gcd A = Finite_Set.fold gcd 0 A"
    by (induction rule: finite.induct[OF `finite A`])
       (simp_all add: comp_fun_idem.fold_insert_idem[OF comp_fun_idem_gcd])

  lemma Gcd_set [code, code_unfold]:
    "Gcd (set xs) = fold gcd xs 0"
    using comp_fun_idem.fold_set_fold[OF comp_fun_idem_gcd] Gcd_finite
        by (simp add: gcd_commute)

  lemma Gcd_singleton [simp]: "Gcd {a} = a div normalisation_factor a"
      by (simp add: gcd_0)

  lemma Gcd_2 [simp]: "Gcd {a,b} = gcd a b"
      by (simp only: Gcd_insert Gcd_empty gcd_0)
         (cases "b = 0", simp, rule gcd_div_unit2, simp)

end


instantiation nat :: euclidean_semiring
begin
  definition [simp]: "euclidean_size_nat = (id :: nat \<Rightarrow> nat)"
  definition [simp]: "normalisation_factor_nat (n::nat) = (if n = 0 then 0 else 1 :: nat)"

  instance proof qed (simp_all add: is_unit_def)
end

instantiation nat :: euclidean_semiring_gcd
begin
  fun gcd_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "gcd_nat a b = (if b = 0 then a else gcd b (a mod b))"
  declare gcd_nat.simps [simp del]

  definition lcm_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "lcm_nat a b = a * b div gcd a b"

  definition "Lcm_nat = (Lcm_eucl :: nat set \<Rightarrow> nat)"
  definition "Gcd_nat = (Gcd_eucl :: nat set \<Rightarrow> nat)"

  instance proof
    show "(gcd :: nat \<Rightarrow> nat \<Rightarrow> nat) = gcd_eucl"
    proof (intro ext)
      fix a b :: nat show "gcd a b = gcd_eucl a b"
      by (induction a b rule: gcd_eucl.induct)
         (subst gcd_nat.simps, subst gcd_eucl.simps, simp_all)
    qed
    thus "(lcm :: nat \<Rightarrow> nat \<Rightarrow> nat) = lcm_eucl"
      by (intro ext) (simp add: lcm_nat_def lcm_eucl_def)

  qed (simp_all add: Lcm_nat_def Gcd_nat_def)

end


lemma Lcm_nat_altdef: "Lcm (A::nat set) = (if finite A then Finite_Set.fold lcm (1::nat) A else 0)"
proof (cases "finite A")
  assume "\<not>finite A"
  hence "Lcm A = 0"
  proof (intro Lcm_no_multiple impI allI)
    fix m :: nat assume "m \<noteq> 0"
    from `\<not>finite A` have "\<forall>m. \<exists>n\<in>A. n > m" using finite_nat_set_iff_bounded_le 
        by (auto simp: not_le)
    then obtain x where "x \<in> A" and "x > m" by blast
    moreover with `m \<noteq> 0` have "\<not>x dvd m" by (auto dest: dvd_imp_le)
    ultimately show "\<exists>x\<in>A. \<not>x dvd m" by blast
  qed
  thus "Lcm A = (if finite A then Finite_Set.fold lcm (1::nat) A else 0)"
     using `\<not>finite A` by simp
qed (simp add: Lcm_finite)

lemma Lcm_nat_infinite: "\<not>finite A \<Longrightarrow> Lcm (A::nat set) = 0"
  by (simp add: Lcm_nat_altdef)

lemma nat_normalisation_transfer: "(n::nat) div normalisation_factor n = n" by simp




lemma gcd_Suc_0: "gcd m (Suc 0) = Suc 0" by (simp only: One_nat_def[symmetric] gcd_1)
lemma gcd_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> gcd x y = x" 
    by (simp add: gcd_proj1_if_dvd)
lemma gcd_proj2_if_dvd_nat [simp]: "(y::nat) dvd x \<Longrightarrow> gcd x y = y"
    by (simp add: gcd_proj2_if_dvd)
lemma gcd_proj1_iff_nat [simp]: "gcd m n = (m::nat) \<longleftrightarrow> m dvd n"
  using gcd_proj1_iff[of m n] by (simp split: split_if_asm)
lemma gcd_proj2_iff_nat [simp]: "gcd m n = (n::nat) \<longleftrightarrow> n dvd m"
  using gcd_proj2_iff[of m n] by (simp split: split_if_asm)
lemma gcd_0_left_nat [simp]: "gcd 0 (x::nat) = x" by simp
lemma gcd_0_nat [simp]: "gcd x (0::nat) = x" by simp
lemma gcd_idem_nat: "gcd (x::nat) x = x" by simp

lemma gcd_nat_induct:
  "\<lbrakk>\<And>m::nat. P m 0; \<And>m n. 0 < n \<Longrightarrow> P n (m mod n) \<Longrightarrow> P m n\<rbrakk> \<Longrightarrow> P m n"
  by (induction m n rule: gcd_induct) simp_all

lemma gcd_le1_nat [simp]: "a \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> a"
  by (rule dvd_imp_le, auto)
lemma gcd_le2_nat [simp]: "b \<noteq> 0 \<Longrightarrow> gcd (a::nat) b \<le> b"
  by (rule dvd_imp_le, auto)

lemma gcd_pos_nat [simp]: "(gcd (m::nat) n > 0) = (m \<noteq> 0 \<or> n \<noteq> 0)"
  by (insert gcd_zero[of m n], arith)

lemma gcd_mult_distrib_nat: "(k::nat) * gcd x y = gcd (k*x) (k*y)"
  by (simp add: gcd_mult_distrib)

lemma gcd_greatest_iff_nat [simp]: "(k::nat) dvd x \<Longrightarrow> k dvd y \<Longrightarrow> k dvd gcd x y"
  by (fact gcd_greatest)

lemma gcd_diff1_nat: "(m::nat) \<ge> n \<Longrightarrow> gcd (m - n) n = gcd m n"
  by (subst gcd_add1[symmetric], auto)

lemma gcd_diff2_nat: "(n::nat) \<ge> m \<Longrightarrow> gcd (n - m) n = gcd m n"
proof-
  assume "n \<ge> m"
  have "gcd (n - m) n = gcd (n - (n - m)) (n - m)"
      by (subst gcd_commute, simp only: gcd_diff1_nat)
  also have "n - (n - m) = m" using `n \<ge> m` by simp
  also have "gcd m (n - m) = gcd (n - m) m" by (rule gcd_commute)
  also have "... = gcd m n" using `n \<ge> m` by (subst gcd_commute, rule gcd_diff1_nat)
  finally show ?thesis .
qed

lemma coprime_nat: "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using coprime by (auto simp: is_unit_def)

lemma coprime_Suc_0_nat: "coprime (a::nat) b \<longleftrightarrow> (\<forall>d. d dvd a \<and> d dvd b \<longleftrightarrow> d = Suc 0)"
  using coprime_nat by (simp add: One_nat_def)

lemma coprime_Suc_nat [simp]: "coprime (Suc n) n"
  by (subst Suc_eq_plus1, rule coprime_plus_one)
  
lemma coprime_minus_one_nat: "(n::nat) \<noteq> 0 \<Longrightarrow> coprime (n - 1) n"
proof-
  assume "n \<noteq> 0"
  have "gcd (n - 1) n = gcd n (n - 1)" by (rule gcd_commute)
  also from `n \<noteq> 0` have "\<dots> = gcd ((n - 1) + 1) (n - 1)" by simp
  also have "\<dots> = 1" by (rule coprime_plus_one)
  finally show ?thesis .
qed

lemma gcd_unique_nat: "d \<ge> 0 \<and> (d::nat) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
    by (auto intro: gcdI gcd_greatest)

lemma coprime_crossproduct_nat:
  fixes a b c d :: nat
  assumes "coprime a d" and "coprime b c"
  shows "a * c = b * d \<longleftrightarrow> a = b \<and> c = d" (is "?lhs \<longleftrightarrow> ?rhs")
  using coprime_crossproduct[OF assms] unfolding associated_def
  by (force intro!: dvd_antisym)

lemma coprime_common_divisor_nat:
  "coprime (a::nat) b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> x = 1"
  by (drule (2) coprime_common_divisor, simp add: is_unit_def)

lemma finite_divisors_nat [simp]:
  assumes "(m::nat) \<noteq> 0" shows "finite {d. d dvd m}"
proof-
  have "{d. d dvd m} \<subseteq> {d. d \<le> m}" using dvd_imp_le assms by force
  moreover have "finite {d. d \<le> m}" by (blast intro: bounded_nat_set_is_finite)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma Max_divisors_self_nat [simp]: "n \<noteq> 0 \<Longrightarrow> Max {d::nat. d dvd n} = n"
apply(rule antisym)
apply (fastforce intro: Max_le_iff [THEN iffD2] simp: dvd_imp_le)
apply simp
done

lemma gcd_is_Max_divisors_nat:
  "m \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> gcd (m::nat) n = (Max {d. d dvd m \<and> d dvd n})"
apply(rule Max_eqI [THEN sym])
apply (metis finite_Collect_conjI finite_divisors_nat)
apply simp
apply(metis Suc_diff_1 Suc_neq_Zero dvd_imp_le gcd_greatest_iff gcd_pos_nat)
apply simp
done


text {*
  A Euclidean ring is a Euclidean semiring with additive inverses. It provides a 
  few more lemmas; in particular, Bezout's lemma holds for any Euclidean ring.
*}
class euclidean_ring = euclidean_semiring + idom

class euclidean_ring_gcd = euclidean_semiring_gcd + idom
begin

  subclass euclidean_ring ..

  lemma gcd_neg1 [simp]: "gcd (-x) y = gcd x y"
      by (rule sym, rule gcdI, simp_all add: gcd_greatest gcd_zero)
  lemma gcd_neg2 [simp]: "gcd x (-y) = gcd x y"
      by (rule sym, rule gcdI, simp_all add: gcd_greatest gcd_zero)
  lemma gcd_neg_numeral_1 [simp]: "gcd (- numeral n) x = gcd (numeral n) x"
      by (fact gcd_neg1)
  lemma gcd_neg_numeral_2 [simp]: "gcd x (- numeral n) = gcd x (numeral n)"
      by (fact gcd_neg2)

  lemma gcd_diff1: "gcd (m - n) n = gcd m n"
    by (subst diff_conv_add_uminus, subst gcd_neg2[symmetric], 
        subst gcd_add1, simp)
  lemma gcd_diff2: "gcd (n - m) n = gcd m n"
    by (subst gcd_neg1[symmetric], simp only: minus_diff_eq gcd_diff1)

  lemma coprime_minus_one [simp]: "gcd (n - 1) n = 1"
  proof-
    have "gcd (n - 1) n = gcd n (n - 1)" by (rule gcd_commute)
    also have "\<dots> = gcd ((n - 1) + 1) (n - 1)" by simp
    also have "\<dots> = 1" by (rule coprime_plus_one)
    finally show ?thesis .
  qed

  lemma lcm_neg1 [simp]: "lcm (-x) y = lcm x y"
      by (rule sym, rule lcmI, simp_all add: lcm_least lcm_zero)
  lemma lcm_neg2 [simp]: "lcm x (-y) = lcm x y"
      by (rule sym, rule lcmI, simp_all add: lcm_least lcm_zero)
  lemma lcm_neg_numeral_1 [simp]: "lcm (- numeral n) x = lcm (numeral n) x"
      by (fact lcm_neg1)
  lemma lcm_neg_numeral_2 [simp]: "lcm x (- numeral n) = lcm x (numeral n)"
      by (fact lcm_neg2)

  function euclid_ext :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where
    "euclid_ext a b = 
       (if b = 0 then 
          let x = ring_inv (normalisation_factor a) in (x, 0, a * x)
        else 
          case euclid_ext b (a mod b) of
              (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
    by (pat_completeness, simp)
    termination by (relation "measure (euclidean_size \<circ> snd)", simp_all)

  declare euclid_ext.simps [simp del]

  lemma euclid_ext_0: 
    "euclid_ext a 0 = (ring_inv (normalisation_factor a), 0, a * ring_inv (normalisation_factor a))"
    by (subst euclid_ext.simps, simp add: Let_def)

  lemma euclid_ext_non_0:
    "b \<noteq> 0 \<Longrightarrow> euclid_ext a b = (case euclid_ext b (a mod b) of 
                                    (s,t,c) \<Rightarrow> (t, s - t * (a div b), c))"
    by (subst euclid_ext.simps, simp)

  definition "euclid_ext' a b = (case euclid_ext a b of (s,t,_) \<Rightarrow> (s,t))"
  definition "bezw = euclid_ext'"

  lemma euclid_ext_gcd [simp]:
    "(case euclid_ext a b of (_,_,t) \<Rightarrow> t) = gcd a b"
  proof (induction a b rule: euclid_ext.induct)
    case (goal1 a b)
      thus ?case
      proof (cases "b = 0")
        case True
          thus ?thesis by (cases "a = 0") 
              (simp_all add: euclid_ext_0 unit_div mult_ac unit_simps gcd_0)
      next
        case False with goal1 show ?thesis
            by (simp add: euclid_ext_non_0 gcd_commute split: prod.split prod.split_asm)
      qed
  qed

  lemma euclid_ext_gcd' [simp]:
    "euclid_ext a b = (r,s,t) \<Longrightarrow> t = gcd a b"
    by (insert euclid_ext_gcd[of a b], drule (1) subst, simp)

  lemma euclid_ext_correct:
    "case euclid_ext x y of (s,t,c) \<Rightarrow> s*x + t*y = c"
  proof (induction x y rule: euclid_ext.induct)
    case (goal1 x y)
      show ?case
      proof (cases "y = 0")
        case True
          thus ?thesis by (simp add: euclid_ext_0 mult_ac)
      next
        case False
          obtain s t c where stc: "euclid_ext y (x mod y) = (s,t,c)"
              by (cases "euclid_ext y (x mod y)", blast)
          from goal1 have "c = s * y + t * (x mod y)" by (simp add: stc False)
          also have "... = t*((x div y)*y + x mod y) + (s - t * (x div y))*y"
              by (simp add: algebra_simps) 
          also have "(x div y)*y + x mod y = x" using mod_div_equality .
          finally show ?thesis
              by (subst euclid_ext.simps, simp add: False stc)
      qed
  qed

  lemma euclid_ext'_correct:
      "fst (euclid_ext' a b) * a + snd (euclid_ext' a b) * b = gcd a b"
  proof-
    obtain s t c where "euclid_ext a b = (s,t,c)"
        by (cases "euclid_ext a b", blast)
    with euclid_ext_correct[of a b] euclid_ext_gcd[of a b]
        show ?thesis unfolding euclid_ext'_def by simp
  qed

  lemma bezw_aux [rule_format]:
    "fst (bezw x y) * x + snd (bezw x y) * y = gcd x y"
    by (simp add: bezw_def euclid_ext'_correct)

  lemma bezout: "\<exists>s t. s * x + t * y = gcd x y"
      using euclid_ext'_correct by blast

  declare gcd_zero [simp]

  lemma bezw_0 [simp]: "bezw x 0 = (ring_inv (normalisation_factor x), 0)" 
      by (simp add: bezw_def euclid_ext'_def euclid_ext_0)

  lemma bezw_non_0: "y \<noteq> 0 \<Longrightarrow> bezw x y = (snd (bezw y (x mod y)),
       fst (bezw y (x mod y)) - snd (bezw y (x mod y)) * (x div y))"
      by (cases "euclid_ext y (x mod y)") 
         (simp add: bezw_def euclid_ext'_def euclid_ext_non_0)

  

end


instantiation int :: euclidean_ring
begin
  definition [simp]: "euclidean_size_int = (nat \<circ> abs :: int \<Rightarrow> nat)"
  definition [simp]: "normalisation_factor_int = (sgn :: int \<Rightarrow> int)"

  instance proof
    case goal2 thus ?case by (auto simp add: abs_mult nat_mult_distrib)
  next
    case goal3 thus ?case by (simp add: zsgn_def is_unit_def)
  next
    case goal5 thus ?case by (auto simp: zsgn_def is_unit_def)
  next
    case goal6 thus ?case by (auto split: abs_split simp: zsgn_def is_unit_def)
  qed (auto simp: sgn_times split: abs_split)
end

instantiation int :: euclidean_ring_gcd
begin
  function gcd_int :: "int \<Rightarrow> int \<Rightarrow> int" where
    "gcd_int a b = (if b = 0 then abs a else gcd_int b (a mod b))"
  by (pat_completeness, simp)
  termination proof (relation "measure (nat \<circ> abs \<circ> snd)")
  fix a b ::int assume "b \<noteq> 0" 
  thus "((b, a mod b), (a, b)) \<in> measure (nat \<circ> abs \<circ> snd)"
      by (cases "a < 0", (cases "b < 0", simp, simp)+)
  qed simp

  declare gcd_int.simps [simp del]

  definition "lcm_int a b = (abs (a * b) div gcd a b :: int)"

  definition "Lcm_int = (Lcm_eucl :: int set \<Rightarrow> int)"
  definition "Gcd_int = (Gcd_eucl :: int set \<Rightarrow> int)"

  instance proof
    show A: "gcd = (gcd_eucl :: int \<Rightarrow> int \<Rightarrow> int)"
    proof (intro ext)
      fix a b :: int show "gcd a b = gcd_eucl a b"
      by (induction a b rule: gcd_eucl.induct)
         (subst gcd_int.simps, subst gcd_eucl.simps, 
          simp_all add: zabs_def zsgn_def)
    qed

    show "lcm = (lcm_eucl :: int \<Rightarrow> int \<Rightarrow> int)"
      unfolding lcm_int_def [abs_def] lcm_eucl_def [abs_def]
      by (intro ext, simp add: A zsgn_def zabs_def div_minus_right)
    qed (simp_all add: Lcm_int_def Gcd_int_def)
end


(* TODO: Move *)
lemma dvd_int_iff: "x dvd y \<longleftrightarrow> nat (abs x) dvd nat (abs y)"
  by (simp add: zdvd_int)

lemma finite_int_set_iff_bounded_le: "finite (N::int set) = (\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m)"
proof
  assume "finite (N::int set)"
  hence "finite (nat ` abs ` N)" by (intro finite_imageI)
  hence "\<exists>m. \<forall>n\<in>nat`abs`N. n \<le> m" by (simp add: finite_nat_set_iff_bounded_le)
  then obtain m :: nat where "\<forall>n\<in>N. nat (abs n) \<le> nat (int m)" by auto
  thus "\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m" by (intro exI[of _ "int m"]) (auto simp: nat_le_eq_zle)
next
  assume "\<exists>m\<ge>0. \<forall>n\<in>N. abs n \<le> m"
  then obtain m where "m \<ge> 0" and "\<forall>n\<in>N. abs n \<le> m" by blast
  hence "\<forall>n\<in>N. nat (abs n) \<le> nat m" by (auto simp: nat_le_eq_zle)
  hence "\<forall>n\<in>nat`abs`N. n \<le> nat m" by (auto simp: nat_le_eq_zle)
  hence A: "finite ((nat \<circ> abs)`N)" unfolding o_def 
      by (subst finite_nat_set_iff_bounded_le) blast
  {
    assume "\<not>finite N"
    from pigeonhole_infinite[OF this A] obtain x 
       where "x \<in> N" and B: "~finite {a\<in>N. nat (abs a) = nat (abs x)}" 
       unfolding o_def by blast
    have "{a\<in>N. nat (abs a) = nat (abs x)} \<subseteq> {x, -x}" by auto
    hence "finite {a\<in>N. nat (abs a) = nat (abs x)}" by (rule finite_subset) simp
    with B have False by contradiction
  }
  thus "finite N" by blast
qed

lemma Lcm_int_altdef: "Lcm (A::int set) = (if finite A then Finite_Set.fold lcm (1::int) A else 0)"
proof (cases "finite A")
  assume "\<not>finite A"
  hence "Lcm A = 0"
  proof (intro Lcm_no_multiple impI allI)
    fix m :: int assume "m \<noteq> 0"
    from `\<not>finite A` have "\<not>(\<exists>m\<ge>0. \<forall>n\<in>A. \<bar>n\<bar> \<le> m)" 
        using finite_int_set_iff_bounded_le by simp
    hence "\<And>m. m \<ge> 0 \<Longrightarrow> \<exists>n\<in>A. \<bar>n\<bar> > m" by (case_tac "m < 0") (auto simp: not_le)
    from this[of "\<bar>m\<bar>"] obtain x where "x \<in> A" and "\<bar>x\<bar> > \<bar>m\<bar>" by auto
    hence "nat \<bar>x\<bar> > nat \<bar>m\<bar>" by (simp add: nat_less_eq_zless)
    moreover from `m \<noteq> 0` have "nat \<bar>m\<bar> \<noteq> 0" by simp
    ultimately have "\<not>nat \<bar>x\<bar> dvd nat \<bar>m\<bar>" by (auto dest: dvd_imp_le)
    hence "\<not>x dvd m" by (simp add: transfer_nat_int_relations)
    with `x \<in> A` show "\<exists>x\<in>A. \<not>x dvd m" by blast
  qed
  thus "Lcm A = (if finite A then Finite_Set.fold lcm (1::int) A else 0)"
     using `\<not>finite A` by simp
qed (simp add: Lcm_finite)

lemma Lcm_int_infinite: "\<not>finite A \<Longrightarrow> Lcm (A::int set) = 0"
  by (simp add: Lcm_int_altdef)

lemma gcd_int_nat [simp]: "gcd (int a) (int b) = int (gcd a b)"
proof (induction a b rule: gcd_eucl.induct)
  case (goal1 a b)
  thus ?case 
    apply (cases "b = 0") 
    apply (simp add: gcd_0 zsgn_def)
    apply (subst (1 2) gcd_red, subst zmod_int[symmetric], assumption)
    done
qed

lemma gcd_proj1_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> gcd x y = abs x"
    by (simp add: zsgn_def gcd_proj1_if_dvd)
lemma gcd_proj2_if_dvd_int [simp]: "(y::int) dvd x \<Longrightarrow> gcd x y = abs y"
    by (simp add: zsgn_def gcd_proj2_if_dvd)
lemma gcd_0_int [simp]: "gcd (x::int) 0 = abs x" by (simp add: zsgn_def)
lemma gcd_0_left_int [simp]: "gcd (0::int) x = abs x" by (simp add: zsgn_def)

lemma gcd_ge_0_int [simp]: "gcd (a::int) b \<ge> 0"
  by (induction a b rule: gcd_int.induct, simp_all add: gcd_int.simps)

lemma gcd_le_0_imp_int [dest]: "gcd (x::int) y \<le> 0 \<Longrightarrow> x = 0 \<and> y = 0"
  by (induction x y rule:gcd_int.induct, simp_all add: gcd_int.simps split: split_if_asm)

lemma gcd_le_0_iff_int [simp]: "gcd (x::int) y \<le> 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (rule iffI, blast, simp add: gcd_int.simps)

lemma coprime_common_divisor_int:
  "coprime (a::int) b \<Longrightarrow> x dvd a \<Longrightarrow> x dvd b \<Longrightarrow> abs x = 1"
  by (drule (2) coprime_common_divisor, simp add: is_unit_def)
find_theorems name:crossproduct
lemma coprime_crossproduct_int:
  fixes a b c d :: int
  assumes "coprime a d" and "coprime b c"
  shows "\<bar>a\<bar> * \<bar>c\<bar> = \<bar>b\<bar> * \<bar>d\<bar> \<longleftrightarrow> \<bar>a\<bar> = \<bar>b\<bar> \<and> \<bar>c\<bar> = \<bar>d\<bar>"
proof
  assume "\<bar>a\<bar> * \<bar>c\<bar> = \<bar>b\<bar> * \<bar>d\<bar>"
      hence "associated (a * c) (b * d)" unfolding associated_def 
      by (auto intro: dvd_if_abs_eq simp: abs_mult)
  with coprime_crossproduct[OF assms] show "\<bar>a\<bar> = \<bar>b\<bar> \<and> \<bar>c\<bar> = \<bar>d\<bar>"
      by (auto intro: zdvd_antisym_abs simp: associated_def)
next
  assume "\<bar>a\<bar> = \<bar>b\<bar> \<and> \<bar>c\<bar> = \<bar>d\<bar>"
  hence "associated a b" and "associated c d"
      unfolding associated_def by (auto intro: dvd_if_abs_eq)
  with coprime_crossproduct[OF assms] have "associated (a * c) (b * d)" by simp
  thus "\<bar>a\<bar> * \<bar>c\<bar> = \<bar>b\<bar> * \<bar>d\<bar>" unfolding associated_def 
      by (subst (1 2) abs_mult[symmetric], auto intro: zdvd_antisym_abs)
qed


lemma sgn_gcd_int [simp]: "sgn (gcd (a::int) b) = (if a = 0 \<and> b = 0 then 0 else 1)"
  by (subst normalisation_factor_int_def[symmetric], simp only: normalisation_factor_gcd)

lemma abs_gcd_int [simp]: "abs (gcd (x::int) y) = gcd x y"
  by (rule gcdI) (simp_all add: gcd_greatest gcd_zero)

lemma gcd_abs_int: "gcd (x::int) y = gcd (abs x) (abs y)"
  by (rule gcdI) (simp_all add: gcd_greatest zsgn_def not_less gcd_zero)

lemma gcd_abs1_int [simp]: "gcd (abs x) (y::int) = gcd x y"
  by (rule gcdI) (simp_all add: gcd_greatest zsgn_def 
                                zabs_def not_less gcd_zero)

lemma gcd_abs2_int [simp]: "gcd x (abs y::int) = gcd x y"
  by (rule gcdI) (simp_all add: gcd_greatest zsgn_def 
                                zabs_def not_less gcd_zero)

lemma gcd_cases_int:
  fixes x :: int and y
  assumes "x \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd x y)"
      and "x \<ge> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd x (-y))"
      and "x \<le> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> P (gcd (-x) y)"
      and "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> P (gcd (-x) (-y))"
  shows "P (gcd x y)"
by (insert assms, auto, arith)

lemma gcd_unique_int: "d \<ge> 0 \<and> (d::int) dvd a \<and> d dvd b \<and>
    (\<forall>e. e dvd a \<and> e dvd b \<longrightarrow> e dvd d) \<longleftrightarrow> d = gcd a b"
  by (force intro!: gcdI gcd_greatest)

lemma coprime_int: "coprime (a::int) b \<longleftrightarrow>
    (\<forall>d. d >= 0 \<and> d dvd a \<and> d dvd b \<longleftrightarrow> d = 1)"
  using gcd_unique_int [of 1 a b]
  apply clarsimp
  apply (erule subst)
  apply (rule iffI)
  apply force
  apply (drule_tac x = "abs ?e" in exI)
  apply (case_tac "(?e::int) >= 0")
  apply force
  apply force
done

lemma gcd_idem_int: "gcd (x::int) x = abs x"
  by (subst gcd_proj1_if_dvd_int, simp_all)

lemma gcd_le1_int [simp]: "a > 0 \<Longrightarrow> gcd (a::int) b \<le> a"
  by (rule zdvd_imp_le, auto)
lemma gcd_le2_int [simp]: "b > 0 \<Longrightarrow> gcd (a::int) b \<le> b"
  by (rule zdvd_imp_le, auto)

lemma gcd_pos_int [simp]: "(gcd (m::int) n > 0) = (m \<noteq> 0 \<or> n \<noteq> 0)"
  by (subst not_le[symmetric], simp)


lemma gcd_mult_distrib_int: "abs (k::int) * gcd x y = gcd (k*x) (k*y)"
  by (simp add: gcd_mult_distrib zsgn_def zabs_def)

lemma finite_divisors_int [simp]:
  assumes "(i::int) \<noteq> 0" shows "finite {d. d dvd i}"
proof-
  have "{d. abs d \<le> abs i} = {-abs i..abs i}" by(auto simp: abs_if)
  hence "finite{d. abs d \<le> abs i}" by simp
  from finite_subset[OF _ this] show ?thesis using assms
    by (bestsimp intro!:dvd_imp_le_int)
qed

lemma Max_divisors_self_int [simp]: "n \<noteq> 0 \<Longrightarrow> Max {d::int. d dvd n} = abs n"
apply(rule antisym)
apply(rule Max_le_iff [THEN iffD2])
apply (auto intro: abs_le_D1 dvd_imp_le_int)
done

lemma gcd_is_Max_divisors_int:
  "m \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> gcd (m::int) n = (Max {d. d dvd m \<and> d dvd n})"
apply(rule Max_eqI [THEN sym])
apply (metis finite_Collect_conjI finite_divisors_int)
apply simp
apply (rule zdvd_imp_le, blast intro: gcd_greatest, simp)
apply simp
done


text {* versions of Bezout for nat, by Amine Chaieb *}

lemma ind_euclid:
  assumes c: " \<forall>a b. P (a::nat) b \<longleftrightarrow> P b a" and z: "\<forall>a. P a 0"
  and add: "\<forall>a b. P a b \<longrightarrow> P a (a + b)"
  shows "P a b"
proof(induct "a + b" arbitrary: a b rule: less_induct)
  case less
  have "a = b \<or> a < b \<or> b < a" by arith
  moreover {assume eq: "a= b"
    from add [rule_format, OF z [rule_format, of a]] have "P a b" using eq
    by simp}
  moreover
  {assume lt: "a < b"
    hence "a + b - a < a + b \<or> a = 0" by arith
    moreover
    {assume "a =0" with z c have "P a b" by blast }
    moreover
    {assume "a + b - a < a + b"
      also have th0: "a + b - a = a + (b - a)" using lt by arith
      finally have "a + (b - a) < a + b" .
      then have "P a (a + (b - a))" by (rule add [rule_format, OF less])
      then have "P a b" by (simp add: th0[symmetric])}
    ultimately have "P a b" by blast}
  moreover
  {assume lt: "a > b"
    hence "b + a - b < a + b \<or> b = 0" by arith
    moreover
    {assume "b =0" with z c have "P a b" by blast }
    moreover
    {assume "b + a - b < a + b"
      also have th0: "b + a - b = b + (a - b)" using lt by arith
      finally have "b + (a - b) < a + b" .
      then have "P b (b + (a - b))" by (rule add [rule_format, OF less])
      then have "P b a" by (simp add: th0[symmetric])
      hence "P a b" using c by blast }
    ultimately have "P a b" by blast}
ultimately  show "P a b" by blast
qed

lemma bezout_lemma_nat:
  assumes ex: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  shows "\<exists>d x y. d dvd a \<and> d dvd a + b \<and>
    (a * x = (a + b) * y + d \<or> (a + b) * x = a * y + d)"
  using ex
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (case_tac "a * x = b * y + d" , simp_all)
  apply (rule_tac x="x + y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x + y" in exI)
  apply algebra
done

lemma bezout_add_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x = b * y + d \<or> b * x = a * y + d)"
  apply(induct a b rule: ind_euclid)
  apply blast
  apply clarify
  apply (rule_tac x="a" in exI, simp)
  apply clarsimp
  apply (rule_tac x="d" in exI)
  apply (case_tac "a * x = b * y + d", simp_all)
  apply (rule_tac x="x+y" in exI)
  apply (rule_tac x="y" in exI)
  apply algebra
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="x+y" in exI)
  apply algebra
done

lemma bezout1_nat: "\<exists>(d::nat) x y. d dvd a \<and> d dvd b \<and>
    (a * x - b * y = d \<or> b * x - a * y = d)"
  using bezout_add_nat[of a b]
  apply clarsimp
  apply (rule_tac x="d" in exI, simp)
  apply (rule_tac x="x" in exI)
  apply (rule_tac x="y" in exI)
  apply auto
done

lemma bezout_add_strong_nat: assumes nz: "a \<noteq> (0::nat)"
  shows "\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d"
proof-
 from nz have ap: "a > 0" by simp
 from bezout_add_nat[of a b]
 have "(\<exists>d x y. d dvd a \<and> d dvd b \<and> a * x = b * y + d) \<or>
   (\<exists>d x y. d dvd a \<and> d dvd b \<and> b * x = a * y + d)" by blast
 moreover
    {fix d x y assume H: "d dvd a" "d dvd b" "a * x = b * y + d"
     from H have ?thesis by blast }
 moreover
 {fix d x y assume H: "d dvd a" "d dvd b" "b * x = a * y + d"
   {assume b0: "b = 0" with H  have ?thesis by simp}
   moreover
   {assume b: "b \<noteq> 0" hence bp: "b > 0" by simp
     from b dvd_imp_le[OF H(2)] have "d < b \<or> d = b"
       by auto
     moreover
     {assume db: "d=b"
       with nz H have ?thesis apply simp
         apply (rule exI [where x = b], simp)
         apply (rule exI [where x = b])
        by (rule exI [where x = "a - 1"], simp add: diff_mult_distrib2)}
    moreover
    {assume db: "d < b"
        {assume "x=0" hence ?thesis using nz H by simp }
        moreover
        {assume x0: "x \<noteq> 0" hence xp: "x > 0" by simp
          from db have "d \<le> b - 1" by simp
          hence "d*b \<le> b*(b - 1)" by simp
          with xp mult_mono[of "1" "x" "d*b" "b*(b - 1)"]
          have dble: "d*b \<le> x*b*(b - 1)" using bp by simp
          from H (3) have "d + (b - 1) * (b*x) = d + (b - 1) * (a*y + d)"
            by simp
          hence "d + (b - 1) * a * y + (b - 1) * d = d + (b - 1) * b * x"
            by (simp only: mult_assoc distrib_left)
          hence "a * ((b - 1) * y) + d * (b - 1 + 1) = d + x*b*(b - 1)"
            by algebra
          hence "a * ((b - 1) * y) = d + x*b*(b - 1) - d*b" using bp by simp
          hence "a * ((b - 1) * y) = d + (x*b*(b - 1) - d*b)"
            by (simp only: diff_add_assoc[OF dble, of d, symmetric])
          hence "a * ((b - 1) * y) = b*(x*(b - 1) - d) + d"
            by (simp only: diff_mult_distrib2 add_commute mult_ac)
          hence ?thesis using H(1,2)
            apply -
            apply (rule exI [where x=d], simp)
            apply (rule exI [where x="(b - 1) * y"])
            by (rule exI [where x="x*(b - 1) - d"], simp)}
        ultimately have ?thesis by blast}
    ultimately have ?thesis by blast}
  ultimately have ?thesis by blast}
 ultimately show ?thesis by blast
qed

lemma bezout_nat: assumes a: "(a::nat) \<noteq> 0"
  shows "\<exists>x y. a * x = b * y + gcd a b"
proof-
  let ?g = "gcd a b"
  from bezout_add_strong_nat[OF a, of b]
  obtain d x y where d: "d dvd a" "d dvd b" "a * x = b * y + d" by blast
  from d(1,2) have "d dvd ?g" by (rule gcd_greatest)
  then obtain k where k: "?g = d*k" unfolding dvd_def by blast
  from d(3) have "a * x * k = (b * y + d) *k " by auto
  hence "a * (x * k) = b * (y*k) + ?g" by (algebra add: k)
  thus ?thesis by blast
qed


lemma lcm_int_nat: "lcm (int a) (int b) = int (lcm a b)"
proof-
  have "lcm (int a) (int b) = abs (int a * int b) div gcd (int a) (int b)"
      unfolding lcm_int_def ..
  also have "abs (int a * int b) = int (a * b)" 
      by (simp only: of_nat_mult[symmetric] abs_int_eq)
  also have "gcd (int a) (int b) = int (gcd a b)" by simp
  also have "int (a * b) div int (gcd a b) = int (a * b div gcd a b)"
      by (rule zdiv_int[symmetric])
  also have "a * b div gcd a b = lcm a b" unfolding lcm_nat_def ..
  finally show ?thesis .
qed


lemma lcm_abs_int: "lcm (x::int) y = lcm (abs x) (abs y)"
    by (simp add: zabs_def)
lemma abs_lcm_int: "abs (lcm (x::int) y) = lcm x y"
  by (rule lcmI) (simp_all add: lcm_least)
lemma lcm_ge_0_int [simp]: "lcm (x::int) y \<ge> 0"
  by (subst abs_lcm_int[symmetric], rule abs_ge_zero)
lemma lcm_int_le_0_imp [dest]: "lcm (x::int) y \<le> 0 \<Longrightarrow> x = 0 \<or> y = 0"
  by (subgoal_tac "lcm x y = 0", simp add: lcm_zero, rule antisym, simp_all)
lemma lcm_int_le_0_iff [simp]: "lcm (x::int) y \<le> 0 \<longleftrightarrow> x = 0 \<or> y = 0" by auto
lemma lcm_abs1_int [simp]: "lcm (abs x) (y::int) = lcm x y"
  by (rule lcmI) (auto simp add: lcm_least zsgn_def 
                                 zabs_def not_less lcm_zero)
lemma lcm_abs2_int [simp]: "lcm x (abs y::int) = lcm x y"
  by (rule lcmI) (auto simp add: lcm_least zsgn_def 
                                 zabs_def not_less lcm_zero)

lemma lcm_cases_int:
  fixes x :: int and y
  assumes "x \<ge> 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm x y)"
      and "x \<ge> 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm x (-y))"
      and "x \<le> 0 \<Longrightarrow> y >= 0 \<Longrightarrow> P (lcm (-x) y)"
      and "x \<le> 0 \<Longrightarrow> y <= 0 \<Longrightarrow> P (lcm (-x) (-y))"
  shows "P (lcm x y)"
  using assms by (auto simp add: lcm_neg1 lcm_neg2) arith

lemma lcm_altdef_int [code]: "lcm (a::int) b = (abs a) * (abs b) div gcd a b"
  by (simp add: lcm_int_def abs_mult)

lemma prod_gcd_lcm_nat: "(m::nat) * n = gcd m n * lcm m n"
  using lcm_gcd_prod[of m n] by (simp add: algebra_simps)

lemma prod_gcd_lcm_int: "abs (m::int) * abs n = gcd m n * lcm m n"
  using lcm_gcd_prod[of m n] apply (simp add: algebra_simps)
  apply (metis abs_mult gcd_0 gcd_0_int normalisation_factor_int_def)
  done

lemma lcm_pos_nat:
  "(m::nat) > 0 \<Longrightarrow> n > 0 \<Longrightarrow> lcm m n > 0"
  by (metis gr0I mult_is_0 prod_gcd_lcm_nat)

lemma lcm_pos_int:
  "(m::int) \<noteq> 0 \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lcm m n > 0"
  by (metis lcm_zero lcm_ge_0_int le_less)

lemma dvd_pos_nat:
  fixes n m :: nat
  assumes "n > 0" and "m dvd n"
  shows "m > 0"
using assms by (cases m) auto

lemma lcm_unique_nat: "(a::nat) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b" 
  by (auto intro: dvd_antisym lcm_least)
lemma lcm_unique_int: "d >= 0 \<and> (a::int) dvd d \<and> b dvd d \<and>
    (\<forall>e. a dvd e \<and> b dvd e \<longrightarrow> d dvd e) \<longleftrightarrow> d = lcm a b"
  by (auto intro: dvd_antisym [transferred] lcm_least)

lemma lcm_proj1_if_dvd_nat [simp]: "(x::nat) dvd y \<Longrightarrow> lcm y x = y"
  using lcm_proj1_if_dvd[of x y] by (simp split: split_if_asm)
lemma lcm_proj2_if_dvd_nat [simp]: "(y::nat) dvd x \<Longrightarrow> lcm y x = x"
  using lcm_proj2_if_dvd[of y x] by (simp split: split_if_asm)
lemma lcm_proj1_iff_nat [simp]: "lcm (x::nat) y = x \<longleftrightarrow> y dvd x"
  using lcm_proj1_iff[of x y] by (simp split: split_if_asm)
lemma lcm_proj2_iff_nat [simp]: "lcm (x::nat) y = y \<longleftrightarrow> x dvd y"
  using lcm_proj2_iff[of x y] by (simp split: split_if_asm)
lemma lcm_1_iff_nat [simp]: "lcm (a::nat) b = 1 \<longleftrightarrow> a = 1 \<and> b = 1"
  using lcm_1_iff[of a b] by (simp add: is_unit_def)

lemma lcm_proj1_if_dvd_int [simp]: "(x::int) dvd y \<Longrightarrow> lcm y x = abs y"
  using lcm_proj1_if_dvd[of x y] by (simp split: split_if_asm add: zabs_def zsgn_def)
lemma lcm_proj2_if_dvd_int [simp]: "(y::int) dvd x \<Longrightarrow> lcm y x = abs x"
  using lcm_proj2_if_dvd[of y x] by (simp split: split_if_asm add: zabs_def zsgn_def)
lemma lcm_proj1_iff_int [simp]: "lcm (x::int) y = abs x \<longleftrightarrow> y dvd x"
  using lcm_proj1_iff[of x y] by (simp split: split_if_asm add: zabs_def zsgn_def)
lemma lcm_proj2_iff_int [simp]: "lcm (x::int) y = abs y \<longleftrightarrow> x dvd y"
  using lcm_proj2_iff[of x y] by (simp split: split_if_asm add: zabs_def zsgn_def)
lemma lcm_1_iff_int' [simp]: "lcm (a::int) b = 1 \<longleftrightarrow> abs a = 1 \<and> abs b = 1"
  using lcm_1_iff[of a b] by (simp add: is_unit_def)
lemma lcm_1_iff_int [simp]: "lcm (m::int) n = 1 \<longleftrightarrow> (m=1 \<or> m = -1) \<and> (n=1 \<or> n = -1)"
  using lcm_1_iff_int'[of m n] by (simp add: zabs_def)


subsection {* Transfer setup *}

lemma transfer_nat_int_gcd:
  "(x::int) \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> gcd (nat x) (nat y) = nat (gcd x y)"
  "(x::int) \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> lcm (nat x) (nat y) = nat (lcm x y)"
  apply (metis gcd_int_nat nat_0_le nat_int)
  apply (metis lcm_int_nat nat_0_le nat_int)
  done

lemma transfer_nat_int_gcd_closures:
  "x \<ge> (0::int) \<Longrightarrow> y \<ge> 0 \<Longrightarrow> gcd x y \<ge> 0"
  "x \<ge> (0::int) \<Longrightarrow> y \<ge> 0 \<Longrightarrow> lcm x y \<ge> 0"
  by (rule gcd_ge_0_int, rule lcm_ge_0_int)

declare transfer_morphism_nat_int [transfer add return:
    transfer_nat_int_gcd transfer_nat_int_gcd_closures]

lemma transfer_int_nat_gcd:
  "gcd (int x) (int y) = int (gcd x y)"
  "lcm (int x) (int y) = int (lcm x y)"
  by (rule gcd_int_nat, rule lcm_int_nat)

lemma transfer_int_nat_gcd_closures:
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> gcd x y \<ge> 0"
  "is_nat x \<Longrightarrow> is_nat y \<Longrightarrow> lcm x y \<ge> 0"
  by (rule gcd_ge_0_int, rule lcm_ge_0_int)

declare transfer_morphism_int_nat [transfer add return:
    transfer_int_nat_gcd transfer_int_nat_gcd_closures]

lemma gcd_int_altdef: "gcd (x::int) y = int (gcd (nat (abs x)) (nat (abs y)))"
    by (simp add: transfer_nat_int_gcd)

lemma gcd_code_int [code]:
  "gcd k l = \<bar>if l = (0::int) then k else gcd l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
  by (simp add: gcd_int_altdef nat_mod_distrib gcd_non_0)


subsection {* The complete divisibility lattice *}

text {*
  Since divisibility is not antisymmetric on most types, it makes little sense to 
  generalise this beyond @{typ "nat"}.
*}

interpretation gcd_semilattice_nat: semilattice_inf gcd "op dvd" "(\<lambda>(m::nat) n. m dvd n \<and> \<not>n dvd m)"
proof qed (auto intro: dvd_antisym dvd_trans gcd_greatest)

interpretation lcm_semilattice_nat: semilattice_sup lcm "op dvd" "(\<lambda>(m::nat) n. m dvd n \<and> \<not>n dvd m)"
proof qed (auto intro: dvd_antisym dvd_trans lcm_least)

interpretation gcd_lcm_lattice_nat: lattice gcd "op dvd" "(\<lambda>(m::nat) n. m dvd n \<and> \<not>n dvd m)" lcm ..



subsection {* Gcd and Lcm *}

interpretation gcd_lcm_complete_lattice_nat:
  complete_lattice Gcd Lcm gcd Rings.dvd "\<lambda>m n. m dvd n \<and> \<not> n dvd m" lcm 1 "0::nat"
where
  "Inf.INFI Gcd A f = Gcd (f ` A :: nat set)"
  and "Sup.SUPR Lcm A f = Lcm (f ` A)"
proof -
  show "class.complete_lattice Gcd Lcm gcd Rings.dvd (\<lambda>m n. m dvd n \<and> \<not> n dvd m) lcm 1 (0::nat)"
  proof qed (auto intro: Gcd_dvd dvd_Gcd Lcm_dvd dvd_Lcm)
  then interpret gcd_lcm_complete_lattice_nat:
    complete_lattice Gcd Lcm gcd Rings.dvd "\<lambda>m n. m dvd n \<and> \<not> n dvd m" lcm 1 "0::nat" .
  from gcd_lcm_complete_lattice_nat.INF_def show "Inf.INFI Gcd A f = Gcd (f ` A)" .
  from gcd_lcm_complete_lattice_nat.SUP_def show "Sup.SUPR Lcm A f = Lcm (f ` A)" .
qed


text{* Alternative characterizations of Gcd: *}

lemma Gcd_eq_Max: "finite(M::nat set) \<Longrightarrow> M \<noteq> {} \<Longrightarrow> 0 \<notin> M \<Longrightarrow> Gcd M = Max(\<Inter>m\<in>M. {d. d dvd m})"
  apply(rule antisym)
  apply(rule Max_ge)
  apply (metis all_not_in_conv finite_divisors_nat finite_INT)
  apply simp
  apply (rule Max_le_iff [THEN iffD2])
  apply (metis all_not_in_conv finite_divisors_nat finite_INT)
  apply fastforce
  apply clarsimp
  apply (metis Gcd_dvd Max_in dvd_0_left dvd_Gcd dvd_imp_le linorder_antisym_conv3 not_less0)
  done

lemma Gcd_remove0_nat: "finite M \<Longrightarrow> Gcd M = Gcd (M - {0::nat})"
  apply(induct pred:finite)
  apply simp
  apply(case_tac "x=0")
  apply simp
  apply(subgoal_tac "insert x F - {0} = insert x (F - {0})")
  apply simp
  apply blast
  done

lemma Lcm_in_lcm_closed_set_nat:
  "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow> \<forall>m n::nat. m\<in>M \<longrightarrow> n\<in>M \<longrightarrow> lcm m n \<in> M \<Longrightarrow> Lcm M \<in> M"
  apply(induct rule:finite_linorder_min_induct)
  apply simp
  apply simp
  apply(subgoal_tac "ALL m n :: nat. m:A \<longrightarrow> n:A \<longrightarrow> lcm m n : A")
  apply simp
  apply(case_tac "A={}")
  apply simp
  apply simp
  apply (metis lcm_pos_nat lcm_unique_nat linorder_neq_iff nat_dvd_not_less not_less0)
  done

lemma Lcm_eq_Max_nat:
  "finite M \<Longrightarrow> M \<noteq> {} \<Longrightarrow> 0 \<notin> M \<Longrightarrow> \<forall>m n::nat. m\<in>M \<longrightarrow> n\<in>M \<longrightarrow> lcm m n \<in> M \<Longrightarrow> Lcm M = Max M"
  apply(rule antisym)
  apply(rule Max_ge, assumption)
  apply(erule (2) Lcm_in_lcm_closed_set_nat)
  apply clarsimp
  apply (metis Lcm0_iff dvd_Lcm dvd_imp_le neq0_conv)
  done


lemma mult_inj_if_coprime_nat:
  assumes "inj_on f A" "inj_on g B" "\<forall>a\<in>A. \<forall>b\<in>B. coprime (f a) (g b)"
  shows "inj_on (\<lambda>(a,b). f a * g b::nat) (A \<times> B)"
proof (rule inj_onI, clarify)
  fix a1 b1 a2 b2 assume A: "f a1 * g b1 = f a2 * g b2"
  assume B: "a1 \<in> A" "a2 \<in> A" "b1 \<in> B" "b2 \<in> B"
  with assms(3) have "coprime (f a1) (g b2)" "coprime (f a2) (g b1)" by auto
  with A have "f a1 = f a2" and "g b1 = g b2" using coprime_crossproduct_nat by blast+
  with assms(1,2) and B show "a1 = a2 \<and> b1 = b2" by (blast dest: inj_onD)
qed

text{* Nitpick: *}

lemma gcd_eq_nitpick_gcd [nitpick_unfold]: "gcd x y = Nitpick.nat_gcd x y"
by (induct x y rule: nat_gcd.induct)
   (simp add: gcd_nat.simps Nitpick.nat_gcd.simps)

lemma lcm_eq_nitpick_lcm [nitpick_unfold]: "lcm x y = Nitpick.nat_lcm x y"
by (simp only: lcm_nat_def Nitpick.nat_lcm_def gcd_eq_nitpick_gcd)

end
