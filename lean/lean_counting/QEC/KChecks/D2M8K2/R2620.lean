import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10480 = true := by
  decide +kernel

theorem tot10480 : totK PD2M8K2 D2M8K2.t10480 = [0, 0, 0, 124494235298, 445369734356, 280419885942, 20606516993, 0] := by
  decide +kernel

theorem rows10481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10481 = true := by
  decide +kernel

theorem tot10481 : totK PD2M8K2 D2M8K2.t10481 = [0, 0, 0, 0, 313168698542, 429127411757, 75950389437, 1095107716] := by
  decide +kernel

theorem rows10482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10482 = true := by
  decide +kernel

theorem tot10482 : totK PD2M8K2 D2M8K2.t10482 = [0, 0, 165934850155, 376194819964, 151091961748, 113962209996, 61725179771, 3819176523] := by
  decide +kernel

theorem rows10483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10483 = true := by
  decide +kernel

theorem tot10483 : totK PD2M8K2 D2M8K2.t10483 = [0, 0, 185518941695, 470575160358, 212850800551, 12422136039, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
