import FusionFanoFastFirst

/- Explicit Boolean checks, with a proved soundness bridge to Good. The first
   batch is reused from the successful benchmark; later batches are sequential. -/
namespace FusionFanoCertificates

set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem fast1 : cases1.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast1

theorem fast2 : cases2.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast2

theorem fast3 : cases3.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast3

theorem fast4 : cases4.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast4

theorem fast5 : cases5.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast5

theorem fast6 : cases6.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast6

theorem fast7 : cases7.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast7

theorem fast8 : cases8.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast8

theorem fast9 : cases9.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast9

theorem fast10 : cases10.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast10

theorem fast11 : cases11.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast11

theorem fast12 : cases12.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast12

theorem fast13 : cases13.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast13

theorem fast14 : cases14.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast14

theorem fast15 : cases15.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast15

theorem fast16 : cases16.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast16

theorem fast17 : cases17.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast17

theorem fast18 : cases18.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast18

theorem fast19 : cases19.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast19

theorem fast20 : cases20.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast20

theorem fast21 : cases21.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast21

theorem fast22 : cases22.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast22

theorem fast23 : cases23.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast23

theorem fast24 : cases24.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast24

theorem fast25 : cases25.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast25

theorem fast26 : cases26.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast26

theorem fast27 : cases27.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast27

theorem fast28 : cases28.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast28

theorem fast29 : cases29.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast29

theorem fast30 : cases30.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast30

theorem fast31 : cases31.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast31

theorem fast32 : cases32.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast32

theorem fast33 : cases33.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast33

theorem fast34 : cases34.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast34

theorem fast35 : cases35.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast35

theorem fast36 : cases36.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast36

theorem fast37 : cases37.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast37

theorem fast38 : cases38.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast38

theorem fast39 : cases39.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast39

theorem fast40 : cases40.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast40

theorem fast41 : cases41.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast41

theorem fast42 : cases42.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast42

theorem fast43 : cases43.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast43

theorem fast44 : cases44.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast44

theorem fast45 : cases45.all FusionFanoFastCheck.fastCheck = true := by
  decide +kernel

#print axioms fast45

theorem all_checked : cases.all FusionFanoFastCheck.fastCheck = true := by
  simp only [cases, List.all_append, fast0, fast1, fast2, fast3, fast4, fast5, fast6, fast7, fast8, fast9, fast10, fast11, fast12, fast13, fast14, fast15, fast16, fast17, fast18, fast19, fast20, fast21, fast22, fast23, fast24, fast25, fast26, fast27, fast28, fast29, fast30, fast31, fast32, fast33, fast34, fast35, fast36, fast37, fast38, fast39, fast40, fast41, fast42, fast43, fast44, fast45, Bool.true_and]

theorem case_good (c : Case) (hc : c ∈ cases) : Good c := by
  apply FusionFanoFastCheck.fastCheck_sound
  exact (List.all_eq_true.mp all_checked) c hc

#print axioms case_good

end FusionFanoCertificates
