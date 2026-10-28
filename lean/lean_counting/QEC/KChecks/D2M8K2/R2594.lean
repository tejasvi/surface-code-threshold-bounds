import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10376 = true := by
  decide +kernel

theorem tot10376 : totK PD2M8K2 D2M8K2.t10376 = [0, 0, 159757390681, 466422234594, 268176290375, 22541468612, 0, 0] := by
  decide +kernel

theorem rows10377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10377 = true := by
  decide +kernel

theorem tot10377 : totK PD2M8K2 D2M8K2.t10377 = [0, 0, 177537856126, 447739519877, 253706078443, 18839509015, 0, 0] := by
  decide +kernel

theorem rows10378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10378 = true := by
  decide +kernel

theorem tot10378 : totK PD2M8K2 D2M8K2.t10378 = [0, 0, 86588537956, 361853313862, 366232115230, 66594122834, 1198073392, 0] := by
  decide +kernel

theorem rows10379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10379 = true := by
  decide +kernel

theorem tot10379 : totK PD2M8K2 D2M8K2.t10379 = [0, 0, 0, 247215257172, 481244694608, 156183008607, 8470662040, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
