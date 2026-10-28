import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4720 = true := by
  decide +kernel

theorem tot4720 : totK PA10K2 A10K2.t4720 = [0, 0, 0, 673477151963, 2096832077236, 1703771948621, 347942769068, 18533161629, 0, 0] := by
  decide +kernel

theorem rows4721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4721 = true := by
  decide +kernel

theorem tot4721 : totK PA10K2 A10K2.t4721 = [0, 0, 0, 323183811971, 1653052345883, 2045942403280, 542239654590, 31889781550, 0, 0] := by
  decide +kernel

theorem rows4722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4722 = true := by
  decide +kernel

theorem tot4722 : totK PA10K2 A10K2.t4722 = [0, 0, 219277734088, 513360812588, 842918162416, 1711943134068, 1122011571290, 187919439061, 5982052406, 0] := by
  decide +kernel

theorem rows4723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4723 = true := by
  decide +kernel

theorem tot4723 : totK PA10K2 A10K2.t4723 = [0, 0, 371527699039, 1613615073118, 2096310175381, 857995480915, 76748597971, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
