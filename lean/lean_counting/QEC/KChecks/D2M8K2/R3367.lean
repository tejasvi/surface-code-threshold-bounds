import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13468 = true := by
  decide +kernel

theorem tot13468 : totK PD2M8K2 D2M8K2.t13468 = [0, 0, 210356144328, 496027600564, 203104172547, 11346028654, 0, 0] := by
  decide +kernel

theorem rows13469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13469 = true := by
  decide +kernel

theorem tot13469 : totK PD2M8K2 D2M8K2.t13469 = [0, 0, 170934236997, 471594891756, 243941833941, 13841717787, 0, 0] := by
  decide +kernel

theorem rows13470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13470 = true := by
  decide +kernel

theorem tot13470 : totK PD2M8K2 D2M8K2.t13470 = [0, 0, 168150236967, 458401654398, 229722254456, 14566626306, 0, 0] := by
  decide +kernel

theorem rows13471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13471 = true := by
  decide +kernel

theorem tot13471 : totK PD2M8K2 D2M8K2.t13471 = [0, 0, 153088874588, 429793785661, 258467387427, 18998562816, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
