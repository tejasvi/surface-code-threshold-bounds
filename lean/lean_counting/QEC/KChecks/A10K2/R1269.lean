import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5076 = true := by
  decide +kernel

theorem tot5076 : totK PA10K2 A10K2.t5076 = [0, 579135734717, 1880708443839, 1777035710346, 521400215525, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5077 = true := by
  decide +kernel

theorem tot5077 : totK PA10K2 A10K2.t5077 = [0, 0, 974373588696, 2410337147623, 1215537999898, 106684548160, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5078 = true := by
  decide +kernel

theorem tot5078 : totK PA10K2 A10K2.t5078 = [0, 449553052964, 1480742670332, 1829749324833, 995952849184, 194600193000, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5079 = true := by
  decide +kernel

theorem tot5079 : totK PA10K2 A10K2.t5079 = [0, 178914173052, 1186876535674, 2210588749766, 1322454650491, 183847222238, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
