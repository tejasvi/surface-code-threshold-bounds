import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3648 = true := by
  decide +kernel

theorem tot3648 : totK PD2M8K2 D2M8K2.t3648 = [0, 135115210903, 443465436565, 297560954410, 22711588023, 0, 0, 0] := by
  decide +kernel

theorem rows3649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3649 = true := by
  decide +kernel

theorem tot3649 : totK PD2M8K2 D2M8K2.t3649 = [0, 0, 201866850935, 491989736363, 184963898799, 9649412842, 0, 0] := by
  decide +kernel

theorem rows3650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3650 = true := by
  decide +kernel

theorem tot3650 : totK PD2M8K2 D2M8K2.t3650 = [0, 82287593761, 314513858842, 378804049666, 100925226281, 3521263076, 0, 0] := by
  decide +kernel

theorem rows3651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3651 = true := by
  decide +kernel

theorem tot3651 : totK PD2M8K2 D2M8K2.t3651 = [0, 158319012441, 448795935574, 265540610967, 23873634473, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
