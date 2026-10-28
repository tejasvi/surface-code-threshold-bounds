import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7388 = true := by
  decide +kernel

theorem tot7388 : totK PD2M8K2 D2M8K2.t7388 = [0, 167708129111, 432417155816, 276117895774, 35416436031, 0, 0, 0] := by
  decide +kernel

theorem rows7389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7389 = true := by
  decide +kernel

theorem tot7389 : totK PD2M8K2 D2M8K2.t7389 = [0, 202237352660, 460349574078, 220236319300, 15910158796, 0, 0, 0] := by
  decide +kernel

theorem rows7390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7390 = true := by
  decide +kernel

theorem tot7390 : totK PD2M8K2 D2M8K2.t7390 = [0, 30129762109, 378669140647, 436546192867, 54501395139, 0, 0, 0] := by
  decide +kernel

theorem rows7391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7391 = true := by
  decide +kernel

theorem tot7391 : totK PD2M8K2 D2M8K2.t7391 = [0, 68046986000, 315442149112, 400768779980, 107710018396, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
