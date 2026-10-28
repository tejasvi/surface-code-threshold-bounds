import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6208 = true := by
  decide +kernel

theorem tot6208 : totK PD2M8K2 D2M8K2.t6208 = [167263955936, 442288714257, 279267317800, 30251713087, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6209 = true := by
  decide +kernel

theorem tot6209 : totK PD2M8K2 D2M8K2.t6209 = [116467896570, 425977292986, 311465549974, 27500142951, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6210 = true := by
  decide +kernel

theorem tot6210 : totK PD2M8K2 D2M8K2.t6210 = [0, 288745673914, 514329552591, 105166469724, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6211 = true := by
  decide +kernel

theorem tot6211 : totK PD2M8K2 D2M8K2.t6211 = [165576442519, 375125245901, 262566570988, 82479723335, 3884009855, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
