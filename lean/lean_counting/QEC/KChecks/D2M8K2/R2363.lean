import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9452 = true := by
  decide +kernel

theorem tot9452 : totK PD2M8K2 D2M8K2.t9452 = [151142883956, 455653172736, 265246358819, 18474313437, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9453 = true := by
  decide +kernel

theorem tot9453 : totK PD2M8K2 D2M8K2.t9453 = [82254482516, 356544296377, 370765189178, 66974688420, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows9454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9454 = true := by
  decide +kernel

theorem tot9454 : totK PD2M8K2 D2M8K2.t9454 = [87932767747, 302863634408, 388496717516, 111572701421, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows9455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9455 = true := by
  decide +kernel

theorem tot9455 : totK PD2M8K2 D2M8K2.t9455 = [157974559089, 456527064210, 263240653677, 22243819490, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
