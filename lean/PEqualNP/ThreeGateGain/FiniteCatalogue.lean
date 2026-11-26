import PEqualNP.ThreeGateGain.FiniteValue
import Mathlib.Tactic.FinCases

/-! Literal certificates for the three-gate host quotient. Words that already fire
in isolation are erased, as are zero rows. Type zero is reserved for these words.
The theorems below check the tables against all physical inputs in the Lean kernel. -/
namespace GainFinite

set_option maxRecDepth 20000
set_option maxHeartbeats 0

abbrev Scalar := Fin 36
abbrev Host := Fin 16
abbrev WordType := Fin 27

def scalarBits (i : Fin 36) : Nat :=
  #[
    0,
    9838263505978427528,
    17294086455919964160,
    17870556004450629632,
    17330115802703130752,
    17908837185407744136,
    18446462598732840960,
    18446612716429770752,
    18446726481523507200,
    18446735277616529408,
    18446727031279321088,
    18446735861732081664,
    18446462601023455232,
    18446612718720419976,
    18446726483814154240,
    18446735279907178496,
    18446727033569968256,
    18446735864022730888,
    18446462602759372800,
    18446462602893590528,
    18446462602767761408,
    18446462602902503424,
    18446612720456335360,
    18446612720590555136,
    18446612720464724096,
    18446612720599468168,
    18446726485550100480,
    18446735281777342464,
    18446727035314303104,
    18446735865901807752,
    18446735865758674944,
    18446735865892894720,
    18446735865767063680,
    18446726485693231104,
    18446735281786255360,
    18446727035449045120][i.val]!

def typeBits (i : Fin 36) : Nat :=
  #[
    0,
    4237038871530880453359697826891417779723553781562442134792310082035349907849922365160108853280,
    131421613225749266883226669942638671518616481956052379941994918619971575361097232836198400,
    12254543372373347861685578887355600422533474594613360570005019123609365708849321092417568,
    197132337525447203191152245101677554054327347949423783128652262805644907361783442292443168,
    16361167138716934639535935459053341866808272671800526095157499286734720416432284559738912,
    113990133211508666424728823870458054862969341615006331423889616692838400,
    10628969110098989915849204607598550287654946104536690804442242046068768,
    326128335265868166677660889983258319232919080462860200523831705600,
    23725403489260294157138568453641296055546228095685106898522179616,
    597901495443970166169698716750819828621232394011766546912491178016,
    30518991582197183489468450389412397002407924533066135540500367392,
    170985199817262999637093173879943100420624096269215544496378345406171168,
    14191055460566533460887897305233452794512472408361848049202693282990112,
    597901835674443801192336168935765125649965914047816676476440381472,
    30519122846709277732192559321598926614617203187656569974467692576,
    163064067146493875388609514612637201119503680299484769530457196576,
    33916061847459351811637179131256064684441272492201220698792790048,
    170985199817262999637093165088135688157868283864958373927814741334425600,
    398965466240280332486550718538373441144499696403678598462598000470493216,
    398965466240280332486550718538848388475956096860992854841361096331331616,
    170985199817262999637093165087891165839883626418670479531427598180648992,
    24877314511969164096004370430228521655571154806928731119518581824522272,
    26658357687202935868523783836981408788957328235172933718841742581663776,
    26658357687202935868523783837091047397174030992492612814055467638687776,
    19534184986267848778446130208095358217700704093702890248077458636015648,
    434837797633411068839785911538241691966548482923279019121914675200,
    33807332778938009819299710398416228155720631498872005220155824224,
    597901505058844000235696708920177091474728228734775245283076118624,
    44107272643245857137817119752885436224107815490357604675822290976,
    33806793195941696915162421936564729710092079324749967504019069024,
    40710202377983688690371044981483456778890215012898110599415826464,
    35614606699181790612361166894574224876594959516273373339089733664,
    597901991184725422295126373303918069953310699021256464807962646624,
    25423522308368653968089730853270625437328885301757789609530591264,
    163064062286955149702516673869826348547267937589312913246996498464][i.val]!

def hostBits (i : Fin 16) : Nat :=
  #[
    0,
    36028797555834880,
    245532278381858558261257124534841712801382020415488,
    19588086498297155600963030379961415472761236248433923100146443223040,
    6724198710133810998440045118695927433638938555706165560042644228944377108950765897898320284227990362000704818005409792,
    38128687640344667999696890624204375962587449622685754712893972308181002176003961333346229059459247745135209314761894913807598870622744637370731992186880,
    0,
    0,
    2755588333101741337057189960848904748217748238033206218138307432341056790997304867917500193849346707054988529926779333736295200015844260662868476485242791824373892251648,
    0,
    1031420127009880616117228312191858919497467348313450654843366126518566752545062649318991733861932497149236685059527109596861893511548680615305971908365380079665781657524554928690974756370123636934505495338329665448181760,
    0,
    14313170335930675820249103283360145434134009358990461722054946134428549335717260174906519589696737711210575564299872574044430427916584827472840894658656261482206828221204807549719654292073154261830074368,
    0,
    0,
    0][i.val]!

def wiringScalar (w : BitVec 9) : Scalar :=
  Fin.ofNat 36 ((2674263077233790219411517039140200900792417144674983521637826958989347749189145976926710242721594187464896167855467222315487717142386504905533638171998054914668893260531076525387451488031428355355280065622448910220252494396297027410344269231273557066843810076752595083551470839637110936396554252180485793961650287496260157812520588343866680416062630361951812582988528361885431435482390569301920483236288973373200709400086540102184955378801216057316858880153274889308675828655266746488092510294241519787928114586034338632405163124022673871466578153441442213539931527010257290550459425854834994511884656764691840694096536196459706490316038304521233113635612457245775821749675474767269020765384849163410559927667505439275662003500702171516881605922960262609657834626491166539943017059145547202512394846807813857789750447527165554474133001139400816049429969877869913226421541160992005533459511065357760863470182834915771710177280 >>> (6*w.toNat)) % 64)

def scalarHost (s : Scalar) : Host :=
  Fin.ofNat 16 ((17818812582020610020119265792979695800819984 >>> (4*s.val)) % 16)

def wordType (s : Scalar) (x : BitVec 6) : WordType :=
  Fin.ofNat 27 (((typeBits s) >>> (5*x.toNat)) % 32)

def hostEdge (h : Host) (i j : WordType) : Bool :=
  (hostBits h).testBit (27*i.val + j.val)

def scalarValue (s : Scalar) (x : BitVec 6) : Bool :=
  (scalarBits s).testBit x.toNat

private theorem wiring_0 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (0+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_1 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (16+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_2 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (32+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_3 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (48+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_4 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (64+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_5 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (80+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_6 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (96+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_7 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (112+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_8 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (128+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_9 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (144+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_10 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (160+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_11 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (176+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_12 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (192+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_13 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (208+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_14 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (224+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_15 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (240+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_16 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (256+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_17 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (272+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_18 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (288+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_19 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (304+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_20 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (320+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_21 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (336+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_22 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (352+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_23 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (368+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_24 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (384+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_25 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (400+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_26 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (416+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_27 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (432+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_28 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (448+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_29 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (464+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_30 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (480+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
private theorem wiring_31 : ∀ (a : Fin 16) (b : Fin 64),
    let w := BitVec.ofNat 9 (496+a.val)
    scalarValue (wiringScalar w) (BitVec.ofFin b) = threeValue w (BitVec.ofFin b) := by decide +kernel
theorem wiring_spec (w : BitVec 9) (x : BitVec 6) :
    scalarValue (wiringScalar w) x = threeValue w x := by
  let batch : Fin 32 := ⟨w.toNat / 16, by have := w.isLt; omega⟩
  let off : Fin 16 := ⟨w.toNat % 16, Nat.mod_lt _ (by decide)⟩
  have hw : w = BitVec.ofNat 9 (16*batch.val+off.val) := by
    apply BitVec.eq_of_toNat_eq
    dsimp [batch, off]; rw [Nat.div_add_mod]; simp
  have he : ∀ j : Fin 32, ∀ (a : Fin 16) (b : Fin 64),
      let u := BitVec.ofNat 9 (16*j.val+a.val)
      scalarValue (wiringScalar u) (BitVec.ofFin b) = threeValue u (BitVec.ofFin b) := by
    intro j; fin_cases j
    · exact wiring_0
    · exact wiring_1
    · exact wiring_2
    · exact wiring_3
    · exact wiring_4
    · exact wiring_5
    · exact wiring_6
    · exact wiring_7
    · exact wiring_8
    · exact wiring_9
    · exact wiring_10
    · exact wiring_11
    · exact wiring_12
    · exact wiring_13
    · exact wiring_14
    · exact wiring_15
    · exact wiring_16
    · exact wiring_17
    · exact wiring_18
    · exact wiring_19
    · exact wiring_20
    · exact wiring_21
    · exact wiring_22
    · exact wiring_23
    · exact wiring_24
    · exact wiring_25
    · exact wiring_26
    · exact wiring_27
    · exact wiring_28
    · exact wiring_29
    · exact wiring_30
    · exact wiring_31
  conv => lhs; rw [hw]
  conv => rhs; rw [hw]
  exact he batch off x.toFin

private theorem host_0 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 0 x && !scalarValue 0 y && scalarValue 0 (x ||| y)) =
      hostEdge (scalarHost 0) (wordType 0 x) (wordType 0 y) := by decide +kernel
private theorem host_1 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 1 x && !scalarValue 1 y && scalarValue 1 (x ||| y)) =
      hostEdge (scalarHost 1) (wordType 1 x) (wordType 1 y) := by decide +kernel
private theorem host_2 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 2 x && !scalarValue 2 y && scalarValue 2 (x ||| y)) =
      hostEdge (scalarHost 2) (wordType 2 x) (wordType 2 y) := by decide +kernel
private theorem host_3 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 3 x && !scalarValue 3 y && scalarValue 3 (x ||| y)) =
      hostEdge (scalarHost 3) (wordType 3 x) (wordType 3 y) := by decide +kernel
private theorem host_4 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 4 x && !scalarValue 4 y && scalarValue 4 (x ||| y)) =
      hostEdge (scalarHost 4) (wordType 4 x) (wordType 4 y) := by decide +kernel
private theorem host_5 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 5 x && !scalarValue 5 y && scalarValue 5 (x ||| y)) =
      hostEdge (scalarHost 5) (wordType 5 x) (wordType 5 y) := by decide +kernel
private theorem host_6 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 6 x && !scalarValue 6 y && scalarValue 6 (x ||| y)) =
      hostEdge (scalarHost 6) (wordType 6 x) (wordType 6 y) := by decide +kernel
private theorem host_7 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 7 x && !scalarValue 7 y && scalarValue 7 (x ||| y)) =
      hostEdge (scalarHost 7) (wordType 7 x) (wordType 7 y) := by decide +kernel
private theorem host_8 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 8 x && !scalarValue 8 y && scalarValue 8 (x ||| y)) =
      hostEdge (scalarHost 8) (wordType 8 x) (wordType 8 y) := by decide +kernel
private theorem host_9 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 9 x && !scalarValue 9 y && scalarValue 9 (x ||| y)) =
      hostEdge (scalarHost 9) (wordType 9 x) (wordType 9 y) := by decide +kernel
private theorem host_10 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 10 x && !scalarValue 10 y && scalarValue 10 (x ||| y)) =
      hostEdge (scalarHost 10) (wordType 10 x) (wordType 10 y) := by decide +kernel
private theorem host_11 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 11 x && !scalarValue 11 y && scalarValue 11 (x ||| y)) =
      hostEdge (scalarHost 11) (wordType 11 x) (wordType 11 y) := by decide +kernel
private theorem host_12 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 12 x && !scalarValue 12 y && scalarValue 12 (x ||| y)) =
      hostEdge (scalarHost 12) (wordType 12 x) (wordType 12 y) := by decide +kernel
private theorem host_13 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 13 x && !scalarValue 13 y && scalarValue 13 (x ||| y)) =
      hostEdge (scalarHost 13) (wordType 13 x) (wordType 13 y) := by decide +kernel
private theorem host_14 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 14 x && !scalarValue 14 y && scalarValue 14 (x ||| y)) =
      hostEdge (scalarHost 14) (wordType 14 x) (wordType 14 y) := by decide +kernel
private theorem host_15 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 15 x && !scalarValue 15 y && scalarValue 15 (x ||| y)) =
      hostEdge (scalarHost 15) (wordType 15 x) (wordType 15 y) := by decide +kernel
private theorem host_16 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 16 x && !scalarValue 16 y && scalarValue 16 (x ||| y)) =
      hostEdge (scalarHost 16) (wordType 16 x) (wordType 16 y) := by decide +kernel
private theorem host_17 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 17 x && !scalarValue 17 y && scalarValue 17 (x ||| y)) =
      hostEdge (scalarHost 17) (wordType 17 x) (wordType 17 y) := by decide +kernel
private theorem host_18 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 18 x && !scalarValue 18 y && scalarValue 18 (x ||| y)) =
      hostEdge (scalarHost 18) (wordType 18 x) (wordType 18 y) := by decide +kernel
private theorem host_19 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 19 x && !scalarValue 19 y && scalarValue 19 (x ||| y)) =
      hostEdge (scalarHost 19) (wordType 19 x) (wordType 19 y) := by decide +kernel
private theorem host_20 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 20 x && !scalarValue 20 y && scalarValue 20 (x ||| y)) =
      hostEdge (scalarHost 20) (wordType 20 x) (wordType 20 y) := by decide +kernel
private theorem host_21 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 21 x && !scalarValue 21 y && scalarValue 21 (x ||| y)) =
      hostEdge (scalarHost 21) (wordType 21 x) (wordType 21 y) := by decide +kernel
private theorem host_22 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 22 x && !scalarValue 22 y && scalarValue 22 (x ||| y)) =
      hostEdge (scalarHost 22) (wordType 22 x) (wordType 22 y) := by decide +kernel
private theorem host_23 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 23 x && !scalarValue 23 y && scalarValue 23 (x ||| y)) =
      hostEdge (scalarHost 23) (wordType 23 x) (wordType 23 y) := by decide +kernel
private theorem host_24 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 24 x && !scalarValue 24 y && scalarValue 24 (x ||| y)) =
      hostEdge (scalarHost 24) (wordType 24 x) (wordType 24 y) := by decide +kernel
private theorem host_25 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 25 x && !scalarValue 25 y && scalarValue 25 (x ||| y)) =
      hostEdge (scalarHost 25) (wordType 25 x) (wordType 25 y) := by decide +kernel
private theorem host_26 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 26 x && !scalarValue 26 y && scalarValue 26 (x ||| y)) =
      hostEdge (scalarHost 26) (wordType 26 x) (wordType 26 y) := by decide +kernel
private theorem host_27 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 27 x && !scalarValue 27 y && scalarValue 27 (x ||| y)) =
      hostEdge (scalarHost 27) (wordType 27 x) (wordType 27 y) := by decide +kernel
private theorem host_28 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 28 x && !scalarValue 28 y && scalarValue 28 (x ||| y)) =
      hostEdge (scalarHost 28) (wordType 28 x) (wordType 28 y) := by decide +kernel
private theorem host_29 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 29 x && !scalarValue 29 y && scalarValue 29 (x ||| y)) =
      hostEdge (scalarHost 29) (wordType 29 x) (wordType 29 y) := by decide +kernel
private theorem host_30 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 30 x && !scalarValue 30 y && scalarValue 30 (x ||| y)) =
      hostEdge (scalarHost 30) (wordType 30 x) (wordType 30 y) := by decide +kernel
private theorem host_31 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 31 x && !scalarValue 31 y && scalarValue 31 (x ||| y)) =
      hostEdge (scalarHost 31) (wordType 31 x) (wordType 31 y) := by decide +kernel
private theorem host_32 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 32 x && !scalarValue 32 y && scalarValue 32 (x ||| y)) =
      hostEdge (scalarHost 32) (wordType 32 x) (wordType 32 y) := by decide +kernel
private theorem host_33 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 33 x && !scalarValue 33 y && scalarValue 33 (x ||| y)) =
      hostEdge (scalarHost 33) (wordType 33 x) (wordType 33 y) := by decide +kernel
private theorem host_34 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 34 x && !scalarValue 34 y && scalarValue 34 (x ||| y)) =
      hostEdge (scalarHost 34) (wordType 34 x) (wordType 34 y) := by decide +kernel
private theorem host_35 : ∀ (r c : Fin 64),
    let x := BitVec.ofFin r; let y := BitVec.ofFin c
    (!scalarValue 35 x && !scalarValue 35 y && scalarValue 35 (x ||| y)) =
      hostEdge (scalarHost 35) (wordType 35 x) (wordType 35 y) := by decide +kernel
theorem scalar_quotient (s : Scalar) (x y : BitVec 6) :
    (!scalarValue s x && !scalarValue s y && scalarValue s (x ||| y)) =
      hostEdge (scalarHost s) (wordType s x) (wordType s y) := by
  fin_cases s
  · exact host_0 x.toFin y.toFin
  · exact host_1 x.toFin y.toFin
  · exact host_2 x.toFin y.toFin
  · exact host_3 x.toFin y.toFin
  · exact host_4 x.toFin y.toFin
  · exact host_5 x.toFin y.toFin
  · exact host_6 x.toFin y.toFin
  · exact host_7 x.toFin y.toFin
  · exact host_8 x.toFin y.toFin
  · exact host_9 x.toFin y.toFin
  · exact host_10 x.toFin y.toFin
  · exact host_11 x.toFin y.toFin
  · exact host_12 x.toFin y.toFin
  · exact host_13 x.toFin y.toFin
  · exact host_14 x.toFin y.toFin
  · exact host_15 x.toFin y.toFin
  · exact host_16 x.toFin y.toFin
  · exact host_17 x.toFin y.toFin
  · exact host_18 x.toFin y.toFin
  · exact host_19 x.toFin y.toFin
  · exact host_20 x.toFin y.toFin
  · exact host_21 x.toFin y.toFin
  · exact host_22 x.toFin y.toFin
  · exact host_23 x.toFin y.toFin
  · exact host_24 x.toFin y.toFin
  · exact host_25 x.toFin y.toFin
  · exact host_26 x.toFin y.toFin
  · exact host_27 x.toFin y.toFin
  · exact host_28 x.toFin y.toFin
  · exact host_29 x.toFin y.toFin
  · exact host_30 x.toFin y.toFin
  · exact host_31 x.toFin y.toFin
  · exact host_32 x.toFin y.toFin
  · exact host_33 x.toFin y.toFin
  · exact host_34 x.toFin y.toFin
  · exact host_35 x.toFin y.toFin

/-- The trimmed prediction of every wiring is the pullback of a literal host. -/
theorem trimmed_host (w : BitVec 9) (x y : BitVec 6) :
    (!threeValue w x && !threeValue w y && threeValue w (x ||| y)) =
      hostEdge (scalarHost (wiringScalar w)) (wordType (wiringScalar w) x)
        (wordType (wiringScalar w) y) := by
  simpa only [wiring_spec] using scalar_quotient (wiringScalar w) x y

/-- The neutral type has no neighbors on either shore. -/
theorem neutral : ∀ (h : Host) (v : WordType),
    hostEdge h 0 v = false ∧ hostEdge h v 0 = false := by decide +kernel

#print axioms trimmed_host
end GainFinite
