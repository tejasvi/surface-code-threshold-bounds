import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t304 = true := by
  decide +kernel

theorem tot304 : totK PA10K2 A10K2.t304 = [0, 0, 474456652457, 1871229828030, 2113513761890, 587212102740, 24426038563, 0, 0, 0] := by
  decide +kernel

theorem rows305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t305 = true := by
  decide +kernel

theorem tot305 : totK PA10K2 A10K2.t305 = [0, 0, 580138270545, 1969936390440, 1791708057887, 418214429440, 36744399143, 0, 0, 0] := by
  decide +kernel

theorem rows306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t306 = true := by
  decide +kernel

theorem tot306 : totK PA10K2 A10K2.t306 = [0, 0, 257156802630, 1385805709283, 2200148746695, 902853289786, 67381822398, 0, 0, 0] := by
  decide +kernel

theorem rows307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t307 = true := by
  decide +kernel

theorem tot307 : totK PA10K2 A10K2.t307 = [0, 0, 0, 518968159817, 1836020122515, 1723048270289, 471773502294, 30650496230, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
