import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5084 = true := by
  decide +kernel

theorem tot5084 : totK PA10K2 A10K2.t5084 = [0, 0, 538785052632, 1794052798756, 1853106183272, 528202929016, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows5085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5085 = true := by
  decide +kernel

theorem tot5085 : totK PA10K2 A10K2.t5085 = [0, 0, 39815911663, 1192889320276, 2372070561143, 990005150054, 71978678543, 0, 0, 0] := by
  decide +kernel

theorem rows5086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5086 = true := by
  decide +kernel

theorem tot5086 : totK PA10K2 A10K2.t5086 = [0, 0, 406760905271, 1451983769047, 1883659601162, 972556534306, 155050195325, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5087 = true := by
  decide +kernel

theorem tot5087 : totK PA10K2 A10K2.t5087 = [0, 272465788330, 1131169215388, 1672700542974, 1293954775177, 481524883670, 35778483473, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
