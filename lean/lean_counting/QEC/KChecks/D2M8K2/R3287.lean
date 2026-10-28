import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13148 = true := by
  decide +kernel

theorem tot13148 : totK PD2M8K2 D2M8K2.t13148 = [0, 0, 103309103831, 354084380492, 329073352916, 81274021857, 3472187823, 0] := by
  decide +kernel

theorem rows13149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13149 = true := by
  decide +kernel

theorem tot13149 : totK PD2M8K2 D2M8K2.t13149 = [0, 0, 208775788245, 467187869020, 212943111823, 13258498675, 0, 0] := by
  decide +kernel

theorem rows13150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13150 = true := by
  decide +kernel

theorem tot13150 : totK PD2M8K2 D2M8K2.t13150 = [0, 0, 106144867291, 436702641859, 312291827256, 23740717996, 0, 0] := by
  decide +kernel

theorem rows13151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13151 = true := by
  decide +kernel

theorem tot13151 : totK PD2M8K2 D2M8K2.t13151 = [0, 0, 0, 311294796128, 471255429434, 79779347303, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
