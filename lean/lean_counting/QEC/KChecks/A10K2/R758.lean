import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3032 = true := by
  decide +kernel

theorem tot3032 : totK PA10K2 A10K2.t3032 = [0, 119627100822, 1098914180008, 2183255082514, 1429417301279, 251689338264, 6574379264, 0, 0, 0] := by
  decide +kernel

theorem rows3033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3033 = true := by
  decide +kernel

theorem tot3033 : totK PA10K2 A10K2.t3033 = [0, 0, 497468715910, 1928249471774, 2047613239856, 538388278369, 18784622171, 0, 0, 0] := by
  decide +kernel

theorem rows3034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3034 = true := by
  decide +kernel

theorem tot3034 : totK PA10K2 A10K2.t3034 = [0, 0, 567919615415, 1815321857382, 1763578098223, 622962347174, 63765033835, 0, 0, 0] := by
  decide +kernel

theorem rows3035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3035 = true := by
  decide +kernel

theorem tot3035 : totK PA10K2 A10K2.t3035 = [0, 0, 292243983067, 1540525682859, 2194996850556, 824952886577, 61866981726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
