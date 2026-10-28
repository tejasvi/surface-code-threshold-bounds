import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9384 = true := by
  decide +kernel

theorem tot9384 : totK PD2M8K2 D2M8K2.t9384 = [0, 159618780853, 445066106758, 278778473347, 20498434120, 0, 0, 0] := by
  decide +kernel

theorem rows9385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9385 = true := by
  decide +kernel

theorem tot9385 : totK PD2M8K2 D2M8K2.t9385 = [0, 91625694353, 352107072065, 361467599240, 70401355910, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9386 = true := by
  decide +kernel

theorem tot9386 : totK PD2M8K2 D2M8K2.t9386 = [0, 0, 314890757337, 516027399949, 80079831688, 0, 0, 0] := by
  decide +kernel

theorem rows9387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9387 = true := by
  decide +kernel

theorem tot9387 : totK PD2M8K2 D2M8K2.t9387 = [0, 164629600731, 391249217027, 239203966673, 67257611406, 2814597007, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
