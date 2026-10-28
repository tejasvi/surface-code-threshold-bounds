import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12592 = true := by
  decide +kernel

theorem tot12592 : totK PD2M8K2 D2M8K2.t12592 = [0, 0, 172030995867, 486358435122, 225411283303, 14633607569, 0, 0] := by
  decide +kernel

theorem rows12593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12593 = true := by
  decide +kernel

theorem tot12593 : totK PD2M8K2 D2M8K2.t12593 = [0, 0, 190549441700, 466712287487, 222796516258, 13852297158, 0, 0] := by
  decide +kernel

theorem rows12594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12594 = true := by
  decide +kernel

theorem tot12594 : totK PD2M8K2 D2M8K2.t12594 = [0, 0, 184677668763, 469069117332, 222901334750, 12370590376, 0, 0] := by
  decide +kernel

theorem rows12595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12595 = true := by
  decide +kernel

theorem tot12595 : totK PD2M8K2 D2M8K2.t12595 = [0, 0, 196872893003, 479005208981, 196403641660, 9170465948, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
