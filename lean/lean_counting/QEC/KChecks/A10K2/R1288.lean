import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5152 = true := by
  decide +kernel

theorem tot5152 : totK PA10K2 A10K2.t5152 = [0, 0, 219518222225, 1299238695130, 2225356145627, 899436059453, 61657562972, 0, 0, 0] := by
  decide +kernel

theorem rows5153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5153 = true := by
  decide +kernel

theorem tot5153 : totK PA10K2 A10K2.t5153 = [0, 0, 112037851608, 712306035847, 1769208210321, 1552983497674, 398254569372, 30388749007, 0, 0] := by
  decide +kernel

theorem rows5154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5154 = true := by
  decide +kernel

theorem tot5154 : totK PA10K2 A10K2.t5154 = [0, 0, 473026617761, 1714030092039, 1875386305900, 598646307700, 51464731716, 0, 0, 0] := by
  decide +kernel

theorem rows5155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5155 = true := by
  decide +kernel

theorem tot5155 : totK PA10K2 A10K2.t5155 = [0, 0, 193659019073, 1383263642273, 2225398147393, 862308472305, 66077604078, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
