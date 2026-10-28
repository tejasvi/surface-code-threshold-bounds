import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9320 = true := by
  decide +kernel

theorem tot9320 : totK PD2M8K2 D2M8K2.t9320 = [0, 174394133180, 447959720120, 253184429909, 22828318141, 0, 0, 0] := by
  decide +kernel

theorem rows9321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9321 = true := by
  decide +kernel

theorem tot9321 : totK PD2M8K2 D2M8K2.t9321 = [0, 92671400364, 399483042889, 324926006972, 47986835285, 1095107716, 0, 0] := by
  decide +kernel

theorem rows9322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9322 = true := by
  decide +kernel

theorem tot9322 : totK PD2M8K2 D2M8K2.t9322 = [0, 0, 325327592683, 478520206938, 76352294153, 0, 0, 0] := by
  decide +kernel

theorem rows9323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9323 = true := by
  decide +kernel

theorem tot9323 : totK PD2M8K2 D2M8K2.t9323 = [0, 176358628726, 394223416070, 240444135809, 77672818729, 3882006667, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
