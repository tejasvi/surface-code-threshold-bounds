import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1408 = true := by
  decide +kernel

theorem tot1408 : totK PD2M8K2 D2M8K2.t1408 = [0, 60626216081, 233801692158, 406562759516, 187241872303, 8073511420, 0, 0] := by
  decide +kernel

theorem rows1409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1409 = true := by
  decide +kernel

theorem tot1409 : totK PD2M8K2 D2M8K2.t1409 = [0, 187040916554, 458274444909, 248253807960, 22378593804, 0, 0, 0] := by
  decide +kernel

theorem rows1410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1410 = true := by
  decide +kernel

theorem tot1410 : totK PD2M8K2 D2M8K2.t1410 = [0, 190126444849, 479879733011, 217029099379, 12272470228, 0, 0, 0] := by
  decide +kernel

theorem rows1411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1411 = true := by
  decide +kernel

theorem tot1411 : totK PD2M8K2 D2M8K2.t1411 = [0, 0, 295757522527, 494883186251, 100038054348, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
