import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4540 = true := by
  decide +kernel

theorem tot4540 : totK PD2M8K2 D2M8K2.t4540 = [0, 0, 70766166162, 339896706492, 399270991657, 78192224682, 1369150432, 0] := by
  decide +kernel

theorem rows4541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4541 = true := by
  decide +kernel

theorem tot4541 : totK PD2M8K2 D2M8K2.t4541 = [0, 0, 57682422340, 363263506528, 433106123987, 42278242244, 0, 0] := by
  decide +kernel

theorem rows4542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4542 = true := by
  decide +kernel

theorem tot4542 : totK PD2M8K2 D2M8K2.t4542 = [0, 0, 194341419351, 480774617129, 227628497103, 11604633750, 0, 0] := by
  decide +kernel

theorem rows4543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4543 = true := by
  decide +kernel

theorem tot4543 : totK PD2M8K2 D2M8K2.t4543 = [0, 0, 170568503821, 460279000329, 238166530942, 13632511348, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
