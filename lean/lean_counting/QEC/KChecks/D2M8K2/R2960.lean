import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11840 = true := by
  decide +kernel

theorem tot11840 : totK PD2M8K2 D2M8K2.t11840 = [0, 0, 183639454095, 459246499555, 233282717892, 18095854657, 0, 0] := by
  decide +kernel

theorem rows11841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11841 = true := by
  decide +kernel

theorem tot11841 : totK PD2M8K2 D2M8K2.t11841 = [0, 0, 157715201058, 484196408830, 206017899886, 8835786784, 0, 0] := by
  decide +kernel

theorem rows11842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11842 = true := by
  decide +kernel

theorem tot11842 : totK PD2M8K2 D2M8K2.t11842 = [0, 0, 288374373674, 480150980859, 123050766083, 3832851649, 0, 0] := by
  decide +kernel

theorem rows11843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11843 = true := by
  decide +kernel

theorem tot11843 : totK PD2M8K2 D2M8K2.t11843 = [0, 0, 198711328596, 473913143977, 196622107757, 10818414931, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
