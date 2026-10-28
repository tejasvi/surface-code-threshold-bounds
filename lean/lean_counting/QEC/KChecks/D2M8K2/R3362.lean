import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13448 = true := by
  decide +kernel

theorem tot13448 : totK PD2M8K2 D2M8K2.t13448 = [0, 0, 161830903420, 453066017891, 253745043849, 18068955215, 0, 0] := by
  decide +kernel

theorem rows13449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13449 = true := by
  decide +kernel

theorem tot13449 : totK PD2M8K2 D2M8K2.t13449 = [0, 0, 0, 289589841339, 502050418119, 96007583071, 1096505104, 0] := by
  decide +kernel

theorem rows13450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13450 = true := by
  decide +kernel

theorem tot13450 : totK PD2M8K2 D2M8K2.t13450 = [0, 0, 79593250177, 312744990433, 375682583330, 106039831565, 3884009855, 0] := by
  decide +kernel

theorem rows13451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13451 = true := by
  decide +kernel

theorem tot13451 : totK PD2M8K2 D2M8K2.t13451 = [0, 0, 172392509647, 480582438514, 248561564889, 18395498295, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
