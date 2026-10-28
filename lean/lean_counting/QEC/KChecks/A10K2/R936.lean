import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3744 = true := by
  decide +kernel

theorem tot3744 : totK PA10K2 A10K2.t3744 = [0, 0, 0, 425800756446, 1641488880933, 1820206530880, 553955732498, 50109395967, 0, 0] := by
  decide +kernel

theorem rows3745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3745 = true := by
  decide +kernel

theorem tot3745 : totK PA10K2 A10K2.t3745 = [0, 0, 0, 286579721414, 1553044253466, 2021088834921, 666997469352, 51971636734, 0, 0] := by
  decide +kernel

theorem rows3746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3746 = true := by
  decide +kernel

theorem tot3746 : totK PA10K2 A10K2.t3746 = [0, 0, 317769054122, 920297972869, 965171336124, 1257535674851, 985981440623, 213642913445, 6354482628, 0] := by
  decide +kernel

theorem rows3747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3747 = true := by
  decide +kernel

theorem tot3747 : totK PA10K2 A10K2.t3747 = [0, 0, 522958244919, 1831993481942, 1902555316448, 511137676753, 32040661968, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
