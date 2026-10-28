import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t428 = true := by
  decide +kernel

theorem tot428 : totK PD2M8K2 D2M8K2.t428 = [0, 277064951932, 508409214512, 111466871132, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t429 = true := by
  decide +kernel

theorem tot429 : totK PD2M8K2 D2M8K2.t429 = [25631151726, 209299341414, 447918040262, 186765343376, 11879463720, 0, 0, 0] := by
  decide +kernel

theorem rows430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t430 = true := by
  decide +kernel

theorem tot430 : totK PD2M8K2 D2M8K2.t430 = [193195313760, 469316718823, 231240627192, 21528527609, 0, 0, 0, 0] := by
  decide +kernel

theorem rows431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t431 = true := by
  decide +kernel

theorem tot431 : totK PD2M8K2 D2M8K2.t431 = [107934332411, 428293001672, 342856276024, 32472918817, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
