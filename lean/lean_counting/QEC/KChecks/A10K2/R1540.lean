import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6160 = true := by
  decide +kernel

theorem tot6160 : totK PA10K2 A10K2.t6160 = [0, 0, 0, 0, 527674722674, 1791615735940, 1691733768013, 459608224666, 30605747850, 0] := by
  decide +kernel

theorem rows6161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6161 = true := by
  decide +kernel

theorem tot6161 : totK PA10K2 A10K2.t6161 = [0, 0, 0, 505902306987, 1729533504555, 1746309525254, 542886003748, 47067195030, 0, 0] := by
  decide +kernel

theorem rows6162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6162 = true := by
  decide +kernel

theorem tot6162 : totK PA10K2 A10K2.t6162 = [0, 0, 0, 158790277817, 1261993118807, 2058228705346, 807542495318, 64484471583, 0, 0] := by
  decide +kernel

theorem rows6163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6163 = true := by
  decide +kernel

theorem tot6163 : totK PA10K2 A10K2.t6163 = [0, 0, 0, 470147374211, 1507024007067, 1752615710181, 815883533587, 139655289773, 5528811039, 0] := by
  decide +kernel

end QECKChecks.A10K2
