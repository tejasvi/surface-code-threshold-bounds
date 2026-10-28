import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5212 = true := by
  decide +kernel

theorem tot5212 : totK PA10K2 A10K2.t5212 = [0, 0, 475411191922, 1748007228107, 1967232150372, 699031069695, 64143685861, 0, 0, 0] := by
  decide +kernel

theorem rows5213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5213 = true := by
  decide +kernel

theorem tot5213 : totK PA10K2 A10K2.t5213 = [0, 0, 498733537531, 1855078733673, 1964274376448, 535176934700, 22912789428, 0, 0, 0] := by
  decide +kernel

theorem rows5214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5214 = true := by
  decide +kernel

theorem tot5214 : totK PA10K2 A10K2.t5214 = [0, 0, 0, 759806655629, 2209939832162, 1588434526359, 265231792377, 6904928264, 0, 0] := by
  decide +kernel

theorem rows5215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5215 = true := by
  decide +kernel

theorem tot5215 : totK PA10K2 A10K2.t5215 = [0, 0, 279805444759, 1349708660178, 2184348899985, 1131161753916, 105035608681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
