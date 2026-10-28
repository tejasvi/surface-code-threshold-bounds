import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4776 = true := by
  decide +kernel

theorem tot4776 : totK PA10K2 A10K2.t4776 = [0, 0, 110199583916, 1237051949642, 2336765523568, 974287078403, 63093111125, 0, 0, 0] := by
  decide +kernel

theorem rows4777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4777 = true := by
  decide +kernel

theorem tot4777 : totK PA10K2 A10K2.t4777 = [0, 0, 294868491376, 1234827570735, 1898532588619, 1110118301438, 198163112039, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4778 = true := by
  decide +kernel

theorem tot4778 : totK PA10K2 A10K2.t4778 = [0, 0, 259935271792, 1250315053770, 2084601382028, 1198264480036, 195279290839, 6962742351, 0, 0] := by
  decide +kernel

theorem rows4779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4779 = true := by
  decide +kernel

theorem tot4779 : totK PA10K2 A10K2.t4779 = [0, 0, 376288107933, 1480543283532, 2004720756828, 919481777290, 110904198726, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
