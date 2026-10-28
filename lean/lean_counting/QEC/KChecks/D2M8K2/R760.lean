import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3040 = true := by
  decide +kernel

theorem tot3040 : totK PD2M8K2 D2M8K2.t3040 = [0, 0, 156513048187, 461325890775, 257945295998, 18817155634, 0, 0] := by
  decide +kernel

theorem rows3041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3041 = true := by
  decide +kernel

theorem tot3041 : totK PD2M8K2 D2M8K2.t3041 = [0, 0, 0, 222211071021, 462126469452, 165011216956, 8137081540, 0] := by
  decide +kernel

theorem rows3042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3042 = true := by
  decide +kernel

theorem tot3042 : totK PD2M8K2 D2M8K2.t3042 = [0, 0, 80976635065, 309828589225, 353873201536, 95719277021, 4879115834, 0] := by
  decide +kernel

theorem rows3043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3043 = true := by
  decide +kernel

theorem tot3043 : totK PD2M8K2 D2M8K2.t3043 = [0, 0, 173901998697, 468256279370, 232423045203, 14178121691, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
