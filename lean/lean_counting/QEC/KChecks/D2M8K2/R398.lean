import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1592 = true := by
  decide +kernel

theorem tot1592 : totK PD2M8K2 D2M8K2.t1592 = [0, 0, 172757610090, 470279171146, 223931443961, 10794973564, 0, 0] := by
  decide +kernel

theorem rows1593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1593 = true := by
  decide +kernel

theorem tot1593 : totK PD2M8K2 D2M8K2.t1593 = [0, 0, 86510406232, 340502575070, 365516743314, 71594423272, 1239866073, 0] := by
  decide +kernel

theorem rows1594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1594 = true := by
  decide +kernel

theorem tot1594 : totK PD2M8K2 D2M8K2.t1594 = [0, 0, 55468276947, 373704543698, 419954936136, 39581647298, 0, 0] := by
  decide +kernel

theorem rows1595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1595 = true := by
  decide +kernel

theorem tot1595 : totK PD2M8K2 D2M8K2.t1595 = [0, 0, 187694863964, 486318104876, 220321103891, 10684372091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
