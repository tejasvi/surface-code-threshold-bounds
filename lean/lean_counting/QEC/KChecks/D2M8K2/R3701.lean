import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14804 = true := by
  decide +kernel

theorem tot14804 : totK PD2M8K2 D2M8K2.t14804 = [69195761676, 336117368997, 402645685525, 91487719936, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14805 = true := by
  decide +kernel

theorem tot14805 : totK PD2M8K2 D2M8K2.t14805 = [40738718386, 343390818848, 457851538882, 61406507160, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14806 = true := by
  decide +kernel

theorem tot14806 : totK PD2M8K2 D2M8K2.t14806 = [171556885865, 442030179278, 283316770029, 30455970377, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14807 = true := by
  decide +kernel

theorem tot14807 : totK PD2M8K2 D2M8K2.t14807 = [206308557884, 491483514622, 198975214417, 9460467948, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
