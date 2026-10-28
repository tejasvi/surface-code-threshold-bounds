import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1452 = true := by
  decide +kernel

theorem tot1452 : totK PD2M8K2 D2M8K2.t1452 = [0, 0, 191299850614, 466274702294, 216359917936, 17076867616, 0, 0] := by
  decide +kernel

theorem rows1453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1453 = true := by
  decide +kernel

theorem tot1453 : totK PD2M8K2 D2M8K2.t1453 = [0, 0, 188938261393, 494667380850, 188799973414, 3705122438, 0, 0] := by
  decide +kernel

theorem rows1454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1454 = true := by
  decide +kernel

theorem tot1454 : totK PD2M8K2 D2M8K2.t1454 = [0, 0, 162902740829, 463245495717, 232594320677, 14211321525, 0, 0] := by
  decide +kernel

theorem rows1455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1455 = true := by
  decide +kernel

theorem tot1455 : totK PD2M8K2 D2M8K2.t1455 = [0, 0, 0, 308463197145, 458083029415, 66681920151, 1200365979, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
