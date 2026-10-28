import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3652 = true := by
  decide +kernel

theorem tot3652 : totK PA10K2 A10K2.t3652 = [0, 0, 117664770764, 1051384158171, 2341145708455, 1505664665940, 179493347373, 0, 0, 0] := by
  decide +kernel

theorem rows3653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3653 = true := by
  decide +kernel

theorem tot3653 : totK PA10K2 A10K2.t3653 = [0, 0, 0, 608558222497, 1973111437365, 1863516234482, 535487732371, 36427600291, 0, 0] := by
  decide +kernel

theorem rows3654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3654 = true := by
  decide +kernel

theorem tot3654 : totK PA10K2 A10K2.t3654 = [0, 0, 0, 424578250448, 1757258748630, 1985252132361, 549319811006, 32523532663, 0, 0] := by
  decide +kernel

theorem rows3655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3655 = true := by
  decide +kernel

theorem tot3655 : totK PA10K2 A10K2.t3655 = [0, 0, 0, 110887952724, 876278803206, 1972407054483, 1433984101116, 355503002260, 25565504801, 0] := by
  decide +kernel

end QECKChecks.A10K2
