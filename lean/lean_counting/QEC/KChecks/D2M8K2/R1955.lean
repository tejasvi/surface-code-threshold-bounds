import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7820 = true := by
  decide +kernel

theorem tot7820 : totK PD2M8K2 D2M8K2.t7820 = [0, 175059783510, 438889369340, 262899499490, 25307278098, 0, 0, 0] := by
  decide +kernel

theorem rows7821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7821 = true := by
  decide +kernel

theorem tot7821 : totK PD2M8K2 D2M8K2.t7821 = [0, 67273539862, 396315891273, 400453390824, 49734817715, 0, 0, 0] := by
  decide +kernel

theorem rows7822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7822 = true := by
  decide +kernel

theorem tot7822 : totK PD2M8K2 D2M8K2.t7822 = [0, 0, 199580468019, 475527009347, 191733493914, 12040273252, 0, 0] := by
  decide +kernel

theorem rows7823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7823 = true := by
  decide +kernel

theorem tot7823 : totK PD2M8K2 D2M8K2.t7823 = [0, 160134897378, 447545034234, 286324864952, 30560584817, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
