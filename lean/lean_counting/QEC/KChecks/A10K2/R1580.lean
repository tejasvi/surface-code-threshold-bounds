import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6320 = true := by
  decide +kernel

theorem tot6320 : totK PA10K2 A10K2.t6320 = [0, 0, 665935230418, 2194929367113, 1891534422028, 369881563196, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows6321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6321 = true := by
  decide +kernel

theorem tot6321 : totK PA10K2 A10K2.t6321 = [0, 0, 434582905311, 1718126972842, 2007426626295, 690164860387, 54689313144, 0, 0, 0] := by
  decide +kernel

theorem rows6322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6322 = true := by
  decide +kernel

theorem tot6322 : totK PA10K2 A10K2.t6322 = [0, 0, 542272113780, 1935459816575, 1875187705950, 418615552232, 11933990244, 0, 0, 0] := by
  decide +kernel

theorem rows6323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6323 = true := by
  decide +kernel

theorem tot6323 : totK PA10K2 A10K2.t6323 = [0, 0, 0, 658783100283, 1976706428605, 1601735418307, 391479734628, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
