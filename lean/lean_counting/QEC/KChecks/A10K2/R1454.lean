import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5816 = true := by
  decide +kernel

theorem tot5816 : totK PA10K2 A10K2.t5816 = [0, 0, 0, 186682551146, 905772634670, 2034825673635, 1295227849007, 194820493153, 6121173289, 0] := by
  decide +kernel

theorem rows5817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5817 = true := by
  decide +kernel

theorem tot5817 : totK PA10K2 A10K2.t5817 = [0, 0, 270642845702, 1083405439998, 1893504346584, 1457268269109, 283767945853, 15154228141, 0, 0] := by
  decide +kernel

theorem rows5818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5818 = true := by
  decide +kernel

theorem tot5818 : totK PA10K2 A10K2.t5818 = [0, 0, 279361398950, 1507385034110, 2106739485729, 700228970459, 52146068715, 0, 0, 0] := by
  decide +kernel

theorem rows5819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5819 = true := by
  decide +kernel

theorem tot5819 : totK PA10K2 A10K2.t5819 = [0, 0, 176859691838, 740708318507, 1647944192548, 1576538837032, 414442546271, 30402056026, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
