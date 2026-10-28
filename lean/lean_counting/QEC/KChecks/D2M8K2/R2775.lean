import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11100 = true := by
  decide +kernel

theorem tot11100 : totK PD2M8K2 D2M8K2.t11100 = [0, 66356778640, 297981114435, 395274619278, 105506059375, 3804183361, 0, 0] := by
  decide +kernel

theorem rows11101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11101 = true := by
  decide +kernel

theorem tot11101 : totK PD2M8K2 D2M8K2.t11101 = [0, 178654432925, 461120997346, 245672579127, 20677109819, 0, 0, 0] := by
  decide +kernel

theorem rows11102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11102 = true := by
  decide +kernel

theorem tot11102 : totK PD2M8K2 D2M8K2.t11102 = [0, 154925078361, 456649518354, 260374811445, 17512225899, 0, 0, 0] := by
  decide +kernel

theorem rows11103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11103 = true := by
  decide +kernel

theorem tot11103 : totK PD2M8K2 D2M8K2.t11103 = [0, 0, 241925885592, 495630088635, 126977457734, 2160984415, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
