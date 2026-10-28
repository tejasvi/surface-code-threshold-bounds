import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8108 = true := by
  decide +kernel

theorem tot8108 : totK PA10K2 A10K2.t8108 = [0, 0, 496719956537, 1874358133730, 1943666081445, 470174314684, 25686058060, 0, 0, 0] := by
  decide +kernel

theorem rows8109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8109 = true := by
  decide +kernel

theorem tot8109 : totK PA10K2 A10K2.t8109 = [0, 0, 0, 722643146365, 2104812667203, 1634000447319, 374536111292, 18469913835, 0, 0] := by
  decide +kernel

theorem rows8110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8110 = true := by
  decide +kernel

theorem tot8110 : totK PA10K2 A10K2.t8110 = [0, 0, 271052620795, 1256281871325, 1999021228953, 1125943191013, 160080657806, 0, 0, 0] := by
  decide +kernel

theorem rows8111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8111 = true := by
  decide +kernel

theorem tot8111 : totK PA10K2 A10K2.t8111 = [0, 0, 283001762435, 1455068396980, 2177901042982, 811747014052, 49181564158, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
