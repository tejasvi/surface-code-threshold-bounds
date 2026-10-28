import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1124 = true := by
  decide +kernel

theorem tot1124 : totK PA10K2 A10K2.t1124 = [0, 0, 0, 604631608687, 1980123716974, 1906297636549, 457330782571, 18214947114, 0, 0] := by
  decide +kernel

theorem rows1125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1125 = true := by
  decide +kernel

theorem tot1125 : totK PA10K2 A10K2.t1125 = [0, 0, 334044182069, 1136743741197, 1523720331916, 1286659771657, 535650311569, 50432252117, 0, 0] := by
  decide +kernel

theorem rows1126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1126 = true := by
  decide +kernel

theorem tot1126 : totK PA10K2 A10K2.t1126 = [0, 0, 412682044044, 1728243989893, 2048097852441, 755879279681, 65939807273, 0, 0, 0] := by
  decide +kernel

theorem rows1127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1127 = true := by
  decide +kernel

theorem tot1127 : totK PA10K2 A10K2.t1127 = [0, 0, 0, 643151094714, 2090897091363, 1701768364638, 293493890830, 11694325420, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
