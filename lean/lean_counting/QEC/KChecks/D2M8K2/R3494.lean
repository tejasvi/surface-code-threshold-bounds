import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13976 = true := by
  decide +kernel

theorem tot13976 : totK PD2M8K2 D2M8K2.t13976 = [0, 0, 0, 177359433308, 446650647157, 248835929468, 25191558099, 0] := by
  decide +kernel

theorem rows13977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13977 = true := by
  decide +kernel

theorem tot13977 : totK PD2M8K2 D2M8K2.t13977 = [0, 0, 0, 207949050434, 486834423824, 181318598454, 5206224793, 0] := by
  decide +kernel

theorem rows13978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13978 = true := by
  decide +kernel

theorem tot13978 : totK PD2M8K2 D2M8K2.t13978 = [0, 0, 154622867567, 366602857909, 264465592959, 104128973856, 6524090962, 0] := by
  decide +kernel

theorem rows13979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13979 = true := by
  decide +kernel

theorem tot13979 : totK PD2M8K2 D2M8K2.t13979 = [0, 0, 174888877728, 461358702650, 239550921256, 12395811615, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
