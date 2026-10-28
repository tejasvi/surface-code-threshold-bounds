import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12580 = true := by
  decide +kernel

theorem tot12580 : totK PD2M8K2 D2M8K2.t12580 = [0, 172087658137, 455349389919, 262951506157, 25902139110, 0, 0, 0] := by
  decide +kernel

theorem rows12581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12581 = true := by
  decide +kernel

theorem tot12581 : totK PD2M8K2 D2M8K2.t12581 = [0, 154803055490, 455904754477, 265594307598, 16991412865, 0, 0, 0] := by
  decide +kernel

theorem rows12582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12582 = true := by
  decide +kernel

theorem tot12582 : totK PD2M8K2 D2M8K2.t12582 = [0, 0, 225770754417, 494935763854, 160055642158, 3544300177, 0, 0] := by
  decide +kernel

theorem rows12583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12583 = true := by
  decide +kernel

theorem tot12583 : totK PD2M8K2 D2M8K2.t12583 = [0, 86654048599, 284214846603, 369522554773, 132049690797, 7481811052, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
