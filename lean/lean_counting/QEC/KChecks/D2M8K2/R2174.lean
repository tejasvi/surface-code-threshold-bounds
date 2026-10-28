import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8696 = true := by
  decide +kernel

theorem tot8696 : totK PD2M8K2 D2M8K2.t8696 = [0, 0, 207361549780, 467837128577, 224302365313, 21890168488, 0, 0] := by
  decide +kernel

theorem rows8697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8697 = true := by
  decide +kernel

theorem tot8697 : totK PD2M8K2 D2M8K2.t8697 = [0, 0, 191715360142, 469542849217, 215928460171, 9121934200, 0, 0] := by
  decide +kernel

theorem rows8698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8698 = true := by
  decide +kernel

theorem tot8698 : totK PD2M8K2 D2M8K2.t8698 = [0, 0, 8125304319, 347505915596, 465747995927, 68932397615, 0, 0] := by
  decide +kernel

theorem rows8699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8699 = true := by
  decide +kernel

theorem tot8699 : totK PD2M8K2 D2M8K2.t8699 = [0, 0, 63453265887, 259561844585, 391914967846, 126146217564, 5126512042, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
