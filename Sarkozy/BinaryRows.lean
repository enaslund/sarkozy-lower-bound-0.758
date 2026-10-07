module

public import Sarkozy.RecordBinaryTarget
public import Sarkozy.ChainMoments
public import Sarkozy.FastPowerCertificate

@[expose] public section
set_option backward.privateInPublic true

/-!
# Kernel-checked real-power bounds for all record binary growth rows

Integer square-root ladders certify lower bounds for the finitely many powers.
The generated rational endpoints are proposals, and every square comparison,
logarithmic comparison, scale match, and final row sum is checked by the kernel.
-/

namespace Sarkozy

/-- A lower logarithm ladder for the base and an upper logarithm ladder for
the proposed power bound suffice to certify a real-power lower endpoint. -/
theorem rpow_lower_of_square_ladders {n : ℕ} (a b : Fin (n+1) → ℝ) (f : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hf : 0 ≤ f)
    (halower : ∀ i : Fin n, (a i.succ)^2 ≤ a i.castSucc)
    (hbupper : ∀ i : Fin n, b i.castSucc ≤ (b i.succ)^2)
    (hend : b (Fin.last n)-1 ≤ f*(1-(a (Fin.last n))⁻¹)) :
    b 0 ≤ (a 0)^f := by
  apply (Real.log_le_log_iff (hb 0) (Real.rpow_pos_of_pos (ha 0) f)).mp
  rw [Real.log_rpow (ha 0)]
  calc
    Real.log (b 0) ≤ (2:ℝ)^n*(b (Fin.last n)-1) :=
      log_upper_of_square_ladder b hb hbupper
    _ ≤ (2:ℝ)^n*(f*(1-(a (Fin.last n))⁻¹)) :=
      mul_le_mul_of_nonneg_left hend (by positivity)
    _ = f*((2:ℝ)^n*(1-(a (Fin.last n))⁻¹)) := by ring
    _ ≤ f*Real.log (a 0) := mul_le_mul_of_nonneg_left
      (log_lower_of_square_ladder a ha halower) hf

/-- An integer-only certificate for a fractional-power lower endpoint.
No large rational exponent is evaluated. -/
theorem rpow_lower_of_integer_ladders {n : ℕ} (D fn fd : ℕ)
    (a b : Fin (n+1) → ℕ) (hD : 0 < D) (hfd : 0 < fd)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (halower : ∀ i : Fin n, (a i.succ)^2 ≤ a i.castSucc*D)
    (hbupper : ∀ i : Fin n, b i.castSucc*D ≤ (b i.succ)^2)
    (hend : ((b (Fin.last n) : ℤ)-D)*a (Fin.last n)*fd ≤
      (fn : ℤ)*D*((a (Fin.last n) : ℤ)-D)) :
    (b 0 : ℝ)/D ≤ ((a 0 : ℝ)/D)^((fn : ℝ)/fd) := by
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  have hfdR : (0:ℝ) < fd := by exact_mod_cast hfd
  have haR (i) : (0:ℝ) < a i := by exact_mod_cast ha i
  have hbR (i) : (0:ℝ) < b i := by exact_mod_cast hb i
  apply rpow_lower_of_square_ladders (fun i => (a i:ℝ)/D) (fun i => (b i:ℝ)/D)
    ((fn:ℝ)/fd) (fun i => div_pos (haR i) hDR) (fun i => div_pos (hbR i) hDR)
    (by positivity)
  · intro i
    rw [div_pow]
    apply (div_le_div_iff₀ (by positivity) hDR).mpr
    have h : (a i.succ:ℝ)^2 ≤ (a i.castSucc:ℝ)*D := by exact_mod_cast halower i
    convert mul_le_mul_of_nonneg_right h hDR.le using 1 <;> ring
  · intro i
    rw [div_pow]
    apply (div_le_div_iff₀ hDR (by positivity)).mpr
    have h : (b i.castSucc:ℝ)*D ≤ (b i.succ:ℝ)^2 := by exact_mod_cast hbupper i
    convert mul_le_mul_of_nonneg_right h hDR.le using 1 <;> ring
  · rw [inv_div, div_sub_one (ne_of_gt hDR), one_sub_div (ne_of_gt (haR _)),
      div_mul_div_comm]
    apply (div_le_div_iff₀ hDR (mul_pos hfdR (haR _))).mpr
    have h : ((b (Fin.last n):ℝ)-D)*a (Fin.last n)*fd ≤
        (fn:ℝ)*D*((a (Fin.last n):ℝ)-D) := by exact_mod_cast hend
    nlinarith

-- BEGIN GENERATED BINARY POWER CERTIFICATES
namespace RecordBinary

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- Source JSON SHA-256: 1b388dd3cfda324a57d985fc96746a8d36b8e7d2e4ac25ecd264c854a8cb8af7
-- 73 distinct scales, rounded down to denominator 10^30, with
-- 4096th-root endpoint certificates for their powers.
private def rowScaleNumerator : Fin 73 → ℕ :=
  ![68556480836000000000000000000, 68556832574000000000000000000, 69070461809000000000000000000,
    92210133055138464412433254855, 92210133055169642702458359749, 98033074932000000000000000000,
    111908667398911839871689852502, 112747027616616790981170201396, 117957566590286836318951686794,
    119144319871836682077199999828, 156742643127140595786426965150, 158620310634891431214417763155,
    168628915975495206292916601558, 168880639163000000000000000000, 181741526113403002470477091907,
    192541103754456434260933993851, 198842333122522894811284741642, 203928472360626234987909675351,
    227892398168470146910148701854, 246313047759948763057629760028, 268335810241175267606875349652,
    269242332451683428648825446961, 277703715734903961316155309632, 278944633082797334435852241944,
    285512426884457492647859249731, 287187565932834378356522836410, 288673268368134026895873327324,
    290877221939576072529842727810, 296263247993794159469460712554, 296962690492652059963123805735,
    298741235783972074292388387094, 308813840456529948917585242966, 310411421721339325141617835688,
    311685742792158718485108144481, 312421517987819788449157689320, 316461967681368002735346772785,
    316800252387129088209486793376, 324083847705500431428354480607, 342610912844350910066600959250,
    344401244962514399516065428541, 345023880972272451955064276174, 382301974116684406880242573585,
    426958422295756943424459940811, 447826336359622938963858724808, 453306537842324933167365482818,
    454142411399946594013874887830, 480828952638254578186604396141, 483129090507401998212335199229,
    502734626425015220656126196177, 506500196258815101032608215501, 548280202929106684897107127757,
    557288595826250250312270834452, 614643724156791336654679258405, 619247717524307923841165522393,
    999993354871882156856245897824, 999994062015429760379580213124, 999994775770800000000000000000,
    999995259333633672341573150078, 999995982087736827729259451676, 999997330610718494039959977814,
    999997522927052132556961814992, 999997790508864535937165861167, 999997828849788194229361975507,
    999998289226000000000000000000, 999998304351000000000000000000, 999998470116769331967315565254,
    999998866946000000000000000000, 999998984435600000000000000000, 999999218778118300772716370537,
    999999230545000000000000000000, 999999414986000000000000000000, 999999805951470958490122233221,
    999999906369000000000000000000]

private def rowLowerNumerator : Fin 73 → ℕ :=
  ![660199303639660911443326434526, 660199828405804162013034115058, 660963707497472245387829906777,
    691223588829294058490875454563, 691223588829330267205487538737, 697812294279287397361485363793,
    712271247083149439198434931723, 713095314374537780852217136181, 718103950840267970624341299408,
    719218512496382741742897519500, 750437523309378092489339353800, 751823255377588141944691798448,
    758983982420013676937516413490, 759159399118357128902398039016, 767840638280727419536996760598,
    774738159482942005590411733693, 778612966014154054941417121345, 781665607850904591251357117961,
    795236729837151723502960894504, 804871068263352255745329828814, 815620547080951550196352329129,
    816046822009452153380826364012, 819968201729604097394109806587, 820534780856406212090715226028,
    823498515061186699607398896766, 824245196696403503469400335158, 824904364809843987633119360895,
    825876941065819215881361522583, 828227776550322440353784031964, 828530406648769782270643654380,
    829297231210427106538617340088, 833568659438968227945913017290, 834235283743080348750382825362,
    834764945412408417316543711886, 835069931862743232472267380843, 836734001904144210092165288248,
    836872509341708119344081450608, 839824807012147820686162763680, 847089254788349897412830287109,
    847773521786595212173664076889, 848010789567704916605613056275, 861597482647063345392276125372,
    876471027575300354987439406975, 882974645638721032832495793294, 884640056668521637117122679172,
    884892577955787545345003577703, 892755351934858719953375747863, 893415650706427126651207353085,
    898938490669388852633336870316, 899978344858555158483979200837, 911097861798221490455517291211,
    913401081975898733764612604423, 927368911559246032043898688465, 928441700460338314588379146446,
    999998970502037568231195421624, 999999080056684984854175667130, 999999190635606684643185153599,
    999999265551792115852343645300, 999999377524733466314275087369, 999999586444962246507414823232,
    999999616239594454637874850781, 999999657694732383145083017759, 999999663634702887226679219508,
    999999734958507368832348997538, 999999737301748175755549047030, 999999762983010020434883870811,
    999999824461764041108846516812, 999999842663832060407008310169, 999999878969324834251963765313,
    999999880792307693592322709016, 999999909366807062121532437571, 999999969937070110184904259327,
    999999985494236503706168748533]

private def rowRootLow : Fin 73 → ℕ :=
  ![0xc9d0f8c597ca4bd3d5033f446, 0xc9d0f8c9d587b6ec167a6289b, 0xc9d110e3f4c221aad5c7d6e69,
    0xc9d4b5f0690cab9a393727739, 0xc9d4b5f0690cb04ac69fd2e8e, 0xc9d57bafa300c975c0a865d36,
    0xc9d7272ff9139b441074dc98c, 0xc9d73f4a6120f01f44b7e6554, 0xc9d7d13152d34df16350b96b7,
    0xc9d7f185915e99793258d2477, 0xc9db674df246468b34df95c97, 0xc9db8dc3ab7cdcf10a31e2b3a,
    0xc9dc536225414f0ad511bb61c, 0xc9dc58337975521329f531bf7, 0xc9dd453f2e1ad0b041794b4e6,
    0xc9ddffaff41332a03fd16143d, 0xc9de67b2ad947cb82d33427ee, 0xc9deb946ae9869d88449ba643,
    0xc9e020238f7bc0e2d6e4325f6, 0xc9e11b3575c6c5c8c7e01b904, 0xc9e22fd25cd9eb85a9c37609e,
    0xc9e23ab73b9d4c903656b9a84, 0xc9e29eaa874c3d200e7b91b38, 0xc9e2ad11650ff1022ee716667,
    0xc9e2f83dcbcd94dc5a8e3693d, 0xc9e30b2350a215ee1350b726f, 0xc9e31bce39dc63d0765690d82,
    0xc9e3345fab91a745d4eff0b52, 0xc9e36fa3894a5fe9fa884141d, 0xc9e37741881796357057534f3,
    0xc9e38a8b61136af30abdaa88b, 0xc9e3f5a96e0c3c39126c1b85d, 0xc9e406546aa33d143124a8959,
    0xc9e413904b6c0a00f72abe95b, 0xc9e41b2e1b8fec152c58e06b2, 0xc9e444b03086f9f56b51d3340,
    0xc9e44823b0e18034908142385, 0xc9e49190f4e31d7ae9c32129d, 0xc9e5452635cc1e9a8c71f6464,
    0xc9e555fc4f0bce78d3bc8d5d9, 0xc9e55bd2035fc9486a1b622f2, 0xc9e6a73f6b82f9f5a5d39842d,
    0xc9e80c22ab361c9fdbe802e7c, 0xc9e8a64ad43ca07cc586e6e5e, 0xc9e8cd95ec3c492cd6e3e0aee,
    0xc9e8d389808843e76a262bf0d, 0xc9e98c0160f1d095bd337df9c, 0xc9e99b6c37fa076971fec9917,
    0xc9ea1bee975a19bdaec88c492, 0xc9ea340a32f10863a8965c619, 0xc9eb341bbd987e82918045bc9,
    0xc9eb68c226677f3637ecae859, 0xc9eca53dcd04b864b7a226155, 0xc9ecbd59fc32ea3a4eaf880a5,
    0xc9f2c9c7853cfe8feb38d8ad6, 0xc9f2c9c81afb9064bf80a3624, 0xc9f2c9c8b220893cef35bf531,
    0xc9f2c9c91886a9104833b14b0, 0xc9f2c9c9b193690f250921bc9, 0xc9f2c9cacf233b6994b49f2ae,
    0xc9f2c9caf7dcbf8c7a39f9881, 0xc9f2c9cb30866bdcaf1066597, 0xc9f2c9cb38a4e43ae743153e5,
    0xc9f2c9cb9a21fc01d1c897c6c, 0xc9f2c9cb9d55e9e7b5faa9673, 0xc9f2c9cbc0701bc9735943681,
    0xc9f2c9cc14784afa11a637c1e, 0xc9f2c9cc2d596c776bbb609ef, 0xc9f2c9cc5ef92b217d4fbbfb1,
    0xc9f2c9cc61770d8b76bc46e67, 0xc9f2c9cc8885a056c1963f311, 0xc9f2c9ccdb4fea4c4aa8f2a60,
    0xc9f2c9ccf0938fa89c9bf6de8]

private def rowRootHigh : Fin 73 → ℕ :=
  ![0xc9ed8c3ddb0cd7ce19cb33602, 0xc9ed8c3e8359ea4f969aba456, 0xc9ed8ffaf2276cb3e263e552d,
    0xc9ee209ba89547ab0e341f35f, 0xc9ee209ba8954865246dd496f, 0xc9ee3f424276d2edc3aac26dc,
    0xc9ee81852cd49fc75c2811f9c, 0xc9ee85418e2b02e86959bd598, 0xc9ee9bdeb8cade1908e9ba119,
    0xc9eea0e17b427db6bbc9a90a7, 0xc9ef2a2ab6c92f66688de41ea, 0xc9ef3020a45f04846b49fed3c,
    0xc9ef4ec14a1032f2a3b3e0274, 0xc9ef4f806ec4aba45e2593354, 0xc9ef743d38e4d9024b02ad69b,
    0xc9ef91222671bd038840f5a72, 0xc9efa140adb36ae0fe228b59b, 0xc9efade532ca164f1458ebc1f,
    0xc9efe58278b68957ef61b6fce, 0xc9f00c6b0cfbf1c001f5aa937, 0xc9f03748ccb65f3670dbb1010,
    0xc9f038f8fb5ebae3210626285, 0xc9f0487626209f1e53cc47fad, 0xc9f04ab17c956dae9b308e728,
    0xc9f05657b323e68770ed60384, 0xc9f05945584151839e9c349a8, 0xc9f05bda909b332dc71f814b5,
    0xc9f05fa93468bc50b58fe15a7, 0xc9f068d84c1ec7028a652f6f3, 0xc9f06a0679c8a17d017a731aa,
    0xc9f06d03a97224d7e7d20424a, 0xc9f07d9d0fd7d1c87c3c10928, 0xc9f0803248a8b325ec2e1cb46,
    0xc9f0823f46cee4ec7b6b7039e, 0xc9f0836d6c6e557f1c430724a, 0xc9f089dc0f608731e638a5bf4,
    0xc9f08a64f80410def94c20f93, 0xc9f095c5d0abdb52db30d3cce, 0xc9f0b199d3a931ac3e2ff47b7,
    0xc9f0b435b713f4afe204ecedc, 0xc9f0b51d2d872937e3968272b, 0xc9f0e87894e8bc0c96bfd68fe,
    0xc9f11fc5a921377c61ceaca97, 0xc9f137a8ae50335afe5d07070, 0xc9f13dbf571aa9c80b6e60b41,
    0xc9f13eab6b3f88d3406dd2321, 0xc9f15b40b76e65f9871f6fb6b, 0xc9f15da4459f30459078300a3,
    0xc9f1718dca1cd4dd33a08b307, 0xc9f1754a0f393d622846a24b7, 0xc9f19cf7453add332d9ce98b7,
    0xc9f1a51faa634bb952f87bd0e, 0xc9f1d62901577d39cccfef6e9, 0xc9f1d9e5532b6fc55fa0ebce2,
    0xc9f2c9cc2a66153ef856aeb4b, 0xc9f2c9cc41990ee0b54b362f0, 0xc9f2c9cc59038f0404ea0c497,
    0xc9f2c9cc68e0c6be2958fc4d8, 0xc9f2c9cc8096d884626dd2edc, 0xc9f2c9ccacd4709f583c95149,
    0xc9f2c9ccb3239c5eef05abb90, 0xc9f2c9ccbbeae62ff6704a826, 0xc9f2c9ccbd2ce7dd955b5104a,
    0xc9f2c9cccc4760c9911fb5ed2, 0xc9f2c9ccccc667cb6e3635dd2, 0xc9f2c9ccd23696fc7748ef097,
    0xc9f2c9ccdf3b5c43dfce4fdf8, 0xc9f2c9cce31618beab4fa8f4a, 0xc9f2c9cceac638bd690ba2298,
    0xc9f2c9cceb290bb6542584ff0, 0xc9f2c9ccf1361297bfaea0acc, 0xc9f2c9ccfe0997e6ca8d11bc9,
    0xc9f2c9cd0154f2f5df494c4c3]

private def rowScale (i : Fin 73) : ℚ := (rowScaleNumerator i : ℚ)/1000000000000000000000000000000
private def rowLower (i : Fin 73) : ℚ := (rowLowerNumerator i : ℚ)/1000000000000000000000000000000

private def rowBranchIndex : Fin 25 → Fin 4 → Fin 73 :=
  ![![56, 0, 56,
      0],
    ![22, 50, 51,
      21],
    ![20, 37, 20,
      37],
    ![28, 32, 26,
      40],
    ![30, 31, 25,
      39],
    ![42, 46, 42,
      46],
    ![55, 11, 54,
      10],
    ![60, 4, 57,
      3],
    ![72, 0, 72,
      0],
    ![67, 0, 67,
      0],
    ![23, 24, 23,
      24],
    ![18, 44, 35,
      41],
    ![16, 48, 16,
      48],
    ![15, 49, 15,
      49],
    ![58, 13, 61,
      12],
    ![36, 52, 36,
      52],
    ![33, 53, 33,
      53],
    ![29, 34, 27,
      38],
    ![43, 45, 43,
      45],
    ![19, 17, 14,
      47],
    ![62, 8, 68,
      6],
    ![64, 0, 69,
      1],
    ![59, 5, 70,
      5],
    ![66, 9, 71,
      7],
    ![65, 2, 63,
      2]]

private def rowIndex (s : Fin 25) (r : ℤ) : Fin 73 :=
  rowBranchIndex s ⟨r.toNat%4, Nat.mod_lt _ (by decide)⟩
private def rowCertificate (i : Fin 73) : PowerChecker.EndpointCertificate :=
  ⟨rowScaleNumerator i, rowLowerNumerator i, rowRootLow i, rowRootHigh i⟩

private theorem row_certificates_valid : ∀ i,
    PowerChecker.EndpointValid 1000000000000000000000000000000 1549247890379023302829202 10000000000000000000000000 4095 (rowCertificate i) := by
  decide +kernel

/-- All fractional-power endpoints are proved by exact integer power tests and
the shared logarithm comparison. -/
private theorem row_power_lower (i : Fin 73) :
    (rowLower i : ℝ) ≤ (rowScale i : ℝ)^(componentPowers 8) := by
  have h := PowerChecker.endpoint_valid_sound (row_certificates_valid i)
  change ((rowLowerNumerator i : ℕ) : ℝ)/((1000000000000000000000000000000 : ℕ) : ℝ) ≤
    (((rowScaleNumerator i : ℕ) : ℝ)/((1000000000000000000000000000000 : ℕ) : ℝ))^
      (((1549247890379023302829202 : ℕ) : ℝ)/((10000000000000000000000000 : ℕ) : ℝ)) at h
  have hf : componentPowers 8 = (1549247890379023302829202/10000000000000000000000000:ℝ) := rfl
  rw [hf]
  norm_num only [Nat.cast_ofNat] at h
  norm_num only [rowScale, rowLower, Rat.cast_div, Rat.cast_natCast]
  exact h

private theorem row_scale_rational : ∀ s (r : Fin 4),
    (r:ℤ) ∈ rationalPolicy.branches s →
    rowScale (rowIndex s r) ≤ rationalPolicy.scale s r := by decide +kernel

private theorem row_sum_rational : ∀ s,
    (1430135321718334301514215293356149372101/500000000000000000000000000000000000000:ℚ)*rationalVector s ≤
      ∑ r ∈ rationalPolicy.branches s,
        rowLower (rowIndex s r)*rationalVector (rationalPolicy.child s r) := by
  decide +kernel

private theorem row_scale_below (s : Fin 25) (r : ℤ) (hr : r ∈ policy.branches s) :
    (rowScale (rowIndex s r):ℝ) ≤ policy.scale s r := by
  have hb := policy_valid.branch s r hr
  let j : Fin 4 := ⟨r.toNat, by omega⟩
  have hj : (j:ℤ) = r := by dsimp [j]; omega
  have h := row_scale_rational s j
    (by simpa only [hj, policy, RationalBinaryPolicy.toReal] using hr)
  rw [hj] at h
  exact Rat.cast_le.mpr h

/-- The actual record policy's 25 growth inequalities require no hypotheses. -/
theorem rows_verified : Rows := by
  intro s
  have hrat : (((1430135321718334301514215293356149372101/500000000000000000000000000000000000000:ℚ)*rationalVector s:ℚ):ℝ) ≤
      ((∑ r ∈ rationalPolicy.branches s,
        rowLower (rowIndex s r)*rationalVector (rationalPolicy.child s r):ℚ):ℝ) :=
    Rat.cast_le.mpr (row_sum_rational s)
  push_cast at hrat
  change growth*vector s ≤ ∑ r ∈ policy.branches s,
    (rowLower (rowIndex s r):ℝ)*vector (policy.child s r) at hrat
  apply hrat.trans
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_right _ (vector_pos _).le
  apply (row_power_lower (rowIndex s r)).trans
  apply Real.rpow_le_rpow
  · have hp : ∀ i, 0 ≤ rowScale i := by decide +kernel
    exact Rat.cast_nonneg.mpr (hp _)
  · exact row_scale_below s r hr
  · exact componentPowers_nonneg 8

end RecordBinary

-- END GENERATED BINARY POWER CERTIFICATES

end Sarkozy
