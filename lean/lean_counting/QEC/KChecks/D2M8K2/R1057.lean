import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4228 = true := by
  decide +kernel

theorem tot4228 : totK PD2M8K2 D2M8K2.t4228 = [0, 0, 0, 170350051523, 462733082626, 240998923249, 10291575752, 0] := by
  decide +kernel

theorem rows4229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4229 = true := by
  decide +kernel

theorem tot4229 : totK PD2M8K2 D2M8K2.t4229 = [0, 0, 0, 0, 280334661836, 469741656995, 119601177306, 3962658158] := by
  decide +kernel

theorem rows4230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4230 = true := by
  decide +kernel

theorem tot4230 : totK PD2M8K2 D2M8K2.t4230 = [0, 0, 0, 102100777276, 332860775456, 351969129377, 74307796321, 1163853884] := by
  decide +kernel

theorem rows4231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4231 = true := by
  decide +kernel

theorem tot4231 : totK PD2M8K2 D2M8K2.t4231 = [0, 0, 0, 170398232184, 434425907399, 269215171938, 28460070216, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
