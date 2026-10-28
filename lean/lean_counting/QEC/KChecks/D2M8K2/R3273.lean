import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13092 = true := by
  decide +kernel

theorem tot13092 : totK PD2M8K2 D2M8K2.t13092 = [0, 0, 293994745642, 496060581185, 109037351795, 1197396724, 0, 0] := by
  decide +kernel

theorem rows13093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13093 = true := by
  decide +kernel

theorem tot13093 : totK PD2M8K2 D2M8K2.t13093 = [0, 0, 191343635343, 469641857191, 193246596047, 12040273252, 0, 0] := by
  decide +kernel

theorem rows13094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13094 = true := by
  decide +kernel

theorem tot13094 : totK PD2M8K2 D2M8K2.t13094 = [0, 184974427266, 446014123320, 262989342820, 30673283609, 0, 0, 0] := by
  decide +kernel

theorem rows13095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13095 = true := by
  decide +kernel

theorem tot13095 : totK PD2M8K2 D2M8K2.t13095 = [0, 188980993793, 461946902629, 238717841912, 17019586267, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
