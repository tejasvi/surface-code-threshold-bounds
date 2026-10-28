import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7068 = true := by
  decide +kernel

theorem tot7068 : totK PA10K2 A10K2.t7068 = [0, 0, 0, 542569140857, 1953412224444, 1867653044131, 410048013566, 12719058911, 0, 0] := by
  decide +kernel

theorem rows7069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7069 = true := by
  decide +kernel

theorem tot7069 : totK PA10K2 A10K2.t7069 = [0, 0, 0, 168715268967, 1123184530700, 2164745673244, 1243468375977, 182046319862, 6860445330, 0] := by
  decide +kernel

theorem rows7070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7070 = true := by
  decide +kernel

theorem tot7070 : totK PA10K2 A10K2.t7070 = [0, 0, 0, 581357240507, 1822509078293, 1775452600119, 620521138375, 59905560340, 0, 0] := by
  decide +kernel

theorem rows7071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7071 = true := by
  decide +kernel

theorem tot7071 : totK PA10K2 A10K2.t7071 = [0, 0, 0, 560296867560, 1976567335594, 1991738270565, 485511506640, 18214947114, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
