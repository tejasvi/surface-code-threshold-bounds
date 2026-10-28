import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1520 = true := by
  decide +kernel

theorem tot1520 : totK PD2M8K2 D2M8K2.t1520 = [0, 176963408456, 445991823423, 255323054875, 25602304099, 0, 0, 0] := by
  decide +kernel

theorem rows1521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1521 = true := by
  decide +kernel

theorem tot1521 : totK PD2M8K2 D2M8K2.t1521 = [0, 157850600128, 448500582212, 278631850365, 23636470495, 0, 0, 0] := by
  decide +kernel

theorem rows1522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1522 = true := by
  decide +kernel

theorem tot1522 : totK PD2M8K2 D2M8K2.t1522 = [0, 0, 223733473476, 492185150220, 160367341456, 4967996017, 0, 0] := by
  decide +kernel

theorem rows1523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1523 = true := by
  decide +kernel

theorem tot1523 : totK PD2M8K2 D2M8K2.t1523 = [0, 0, 178028804118, 476841770174, 212385743784, 10003724324, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
