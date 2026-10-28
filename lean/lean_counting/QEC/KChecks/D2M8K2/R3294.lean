import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13176 = true := by
  decide +kernel

theorem tot13176 : totK PD2M8K2 D2M8K2.t13176 = [0, 0, 65232340698, 362599899336, 356382989330, 58943233323, 1138244013, 0] := by
  decide +kernel

theorem rows13177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13177 = true := by
  decide +kernel

theorem tot13177 : totK PD2M8K2 D2M8K2.t13177 = [0, 0, 92861591997, 414083912680, 343074173857, 32821770873, 0, 0] := by
  decide +kernel

theorem rows13178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13178 = true := by
  decide +kernel

theorem tot13178 : totK PD2M8K2 D2M8K2.t13178 = [0, 0, 167720490159, 443325203282, 266686646861, 28900386813, 0, 0] := by
  decide +kernel

theorem rows13179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13179 = true := by
  decide +kernel

theorem tot13179 : totK PD2M8K2 D2M8K2.t13179 = [0, 0, 175138784322, 485684000551, 235771027684, 11439199413, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
