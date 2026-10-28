import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2644 = true := by
  decide +kernel

theorem tot2644 : totK PA10K2 A10K2.t2644 = [0, 0, 463468567384, 1830069246527, 1904696999429, 492258823955, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows2645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2645 = true := by
  decide +kernel

theorem tot2645 : totK PA10K2 A10K2.t2645 = [0, 559356954831, 1945200735971, 1839785111819, 461330940675, 49009071388, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2646 = true := by
  decide +kernel

theorem tot2646 : totK PA10K2 A10K2.t2646 = [0, 0, 648417191365, 2065022305402, 1640951460391, 332222547175, 25299471099, 0, 0, 0] := by
  decide +kernel

theorem rows2647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2647 = true := by
  decide +kernel

theorem tot2647 : totK PA10K2 A10K2.t2647 = [0, 511776002785, 1617233390164, 1634457735218, 789434072328, 162752639212, 6034215561, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
