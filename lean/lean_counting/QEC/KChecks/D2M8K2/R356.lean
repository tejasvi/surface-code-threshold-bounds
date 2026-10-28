import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1424 = true := by
  decide +kernel

theorem tot1424 : totK PD2M8K2 D2M8K2.t1424 = [0, 0, 203559682770, 482165343315, 219277439269, 13131754800, 0, 0] := by
  decide +kernel

theorem rows1425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1425 = true := by
  decide +kernel

theorem tot1425 : totK PD2M8K2 D2M8K2.t1425 = [0, 0, 222611610516, 487862223382, 178042655473, 8943467364, 0, 0] := by
  decide +kernel

theorem rows1426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1426 = true := by
  decide +kernel

theorem tot1426 : totK PD2M8K2 D2M8K2.t1426 = [0, 0, 178737381806, 466986185497, 241666907204, 18419450353, 0, 0] := by
  decide +kernel

theorem rows1427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1427 = true := by
  decide +kernel

theorem tot1427 : totK PD2M8K2 D2M8K2.t1427 = [0, 0, 167444035739, 458741080827, 239781687299, 13859269504, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
