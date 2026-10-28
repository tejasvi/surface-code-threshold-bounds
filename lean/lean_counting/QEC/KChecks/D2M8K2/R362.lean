import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1448 = true := by
  decide +kernel

theorem tot1448 : totK PD2M8K2 D2M8K2.t1448 = [0, 139502450880, 359888726237, 297493353543, 77946308840, 3821179711, 0, 0] := by
  decide +kernel

theorem rows1449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1449 = true := by
  decide +kernel

theorem tot1449 : totK PD2M8K2 D2M8K2.t1449 = [0, 177987633766, 447153542988, 256246878742, 26430504404, 0, 0, 0] := by
  decide +kernel

theorem rows1450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1450 = true := by
  decide +kernel

theorem tot1450 : totK PD2M8K2 D2M8K2.t1450 = [0, 108354261105, 424835527501, 345086834872, 30407781501, 0, 0, 0] := by
  decide +kernel

theorem rows1451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1451 = true := by
  decide +kernel

theorem tot1451 : totK PD2M8K2 D2M8K2.t1451 = [0, 0, 209346799269, 485499595734, 177194611609, 4899206309, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
