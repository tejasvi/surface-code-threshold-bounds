import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6448 = true := by
  decide +kernel

theorem tot6448 : totK PA10K2 A10K2.t6448 = [0, 450236693064, 1439643789412, 1568658196321, 995863874112, 405008039537, 43720954405, 0, 0, 0] := by
  decide +kernel

theorem rows6449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6449 = true := by
  decide +kernel

theorem tot6449 : totK PA10K2 A10K2.t6449 = [0, 388654510407, 1671143302843, 2083911075643, 717572716399, 56042958553, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6450 = true := by
  decide +kernel

theorem tot6450 : totK PA10K2 A10K2.t6450 = [0, 0, 489831033059, 1871622631486, 1807338841419, 434248925124, 25680132735, 0, 0, 0] := by
  decide +kernel

theorem rows6451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6451 = true := by
  decide +kernel

theorem tot6451 : totK PA10K2 A10K2.t6451 = [0, 321146256371, 1438733394860, 1968407920088, 1012800971977, 166064725859, 5626791703, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
