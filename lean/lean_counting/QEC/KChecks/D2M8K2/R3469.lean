import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13876 = true := by
  decide +kernel

theorem tot13876 : totK PD2M8K2 D2M8K2.t13876 = [0, 197614118936, 482978778881, 212315880311, 11295872662, 0, 0, 0] := by
  decide +kernel

theorem rows13877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13877 = true := by
  decide +kernel

theorem tot13877 : totK PD2M8K2 D2M8K2.t13877 = [0, 197344191915, 474990971023, 215966875054, 12876692821, 0, 0, 0] := by
  decide +kernel

theorem rows13878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13878 = true := by
  decide +kernel

theorem tot13878 : totK PD2M8K2 D2M8K2.t13878 = [0, 159069295007, 443105483915, 282242116281, 27214788375, 0, 0, 0] := by
  decide +kernel

theorem rows13879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13879 = true := by
  decide +kernel

theorem tot13879 : totK PD2M8K2 D2M8K2.t13879 = [0, 103548025847, 417883345135, 325320193010, 31490885541, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
