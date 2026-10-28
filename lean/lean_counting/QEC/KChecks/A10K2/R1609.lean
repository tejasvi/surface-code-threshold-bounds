import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6436 = true := by
  decide +kernel

theorem tot6436 : totK PA10K2 A10K2.t6436 = [0, 0, 777363517912, 2228835965459, 1664989615296, 256641719044, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows6437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6437 = true := by
  decide +kernel

theorem tot6437 : totK PA10K2 A10K2.t6437 = [0, 0, 481547604140, 1868017031879, 2054278788263, 556622100958, 17732757243, 0, 0, 0] := by
  decide +kernel

theorem rows6438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6438 = true := by
  decide +kernel

theorem tot6438 : totK PA10K2 A10K2.t6438 = [0, 495669055860, 1747380613804, 1822827425450, 582288684059, 175111804001, 37310410385, 0, 0, 0] := by
  decide +kernel

theorem rows6439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6439 = true := by
  decide +kernel

theorem tot6439 : totK PA10K2 A10K2.t6439 = [0, 280441419433, 1383172442628, 2186688710316, 1116450541506, 115293656729, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
