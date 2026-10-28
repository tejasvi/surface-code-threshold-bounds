import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8460 = true := by
  decide +kernel

theorem tot8460 : totK PD2M8K2 D2M8K2.t8460 = [0, 144215413515, 457578045943, 264344042904, 16264020352, 0, 0, 0] := by
  decide +kernel

theorem rows8461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8461 = true := by
  decide +kernel

theorem tot8461 : totK PD2M8K2 D2M8K2.t8461 = [0, 0, 240606307904, 502371734891, 130684313686, 2309606161, 0, 0] := by
  decide +kernel

theorem rows8462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8462 = true := by
  decide +kernel

theorem tot8462 : totK PD2M8K2 D2M8K2.t8462 = [0, 84858698819, 283714169453, 354155011508, 129863907737, 10673843635, 0, 0] := by
  decide +kernel

theorem rows8463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8463 = true := by
  decide +kernel

theorem tot8463 : totK PD2M8K2 D2M8K2.t8463 = [0, 171534765116, 454429958434, 264192794322, 22260015795, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
