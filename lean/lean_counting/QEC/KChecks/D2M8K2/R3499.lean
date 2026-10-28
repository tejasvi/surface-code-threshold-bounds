import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13996 = true := by
  decide +kernel

theorem tot13996 : totK PD2M8K2 D2M8K2.t13996 = [0, 164557777352, 423501199096, 315082029122, 40630354644, 0, 0, 0] := by
  decide +kernel

theorem rows13997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13997 = true := by
  decide +kernel

theorem tot13997 : totK PD2M8K2 D2M8K2.t13997 = [0, 172941826698, 462740686708, 241625211465, 15670360577, 0, 0, 0] := by
  decide +kernel

theorem rows13998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13998 = true := by
  decide +kernel

theorem tot13998 : totK PD2M8K2 D2M8K2.t13998 = [0, 88183717169, 376818557632, 359356065812, 79768491901, 10443890748, 0, 0] := by
  decide +kernel

theorem rows13999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13999 = true := by
  decide +kernel

theorem tot13999 : totK PD2M8K2 D2M8K2.t13999 = [0, 0, 161716995139, 452842399023, 266572133099, 17754548031, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
