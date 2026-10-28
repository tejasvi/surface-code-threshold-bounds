import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4216 = true := by
  decide +kernel

theorem tot4216 : totK PA10K2 A10K2.t4216 = [0, 527726960312, 1763992869125, 1781954583701, 572143789463, 55738710373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4217 = true := by
  decide +kernel

theorem tot4217 : totK PA10K2 A10K2.t4217 = [0, 308170643447, 1538398526751, 2103755212830, 742245856091, 44423345534, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4218 = true := by
  decide +kernel

theorem tot4218 : totK PA10K2 A10K2.t4218 = [0, 0, 673265333126, 2109014375127, 1562186604456, 267960777950, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4219 = true := by
  decide +kernel

theorem tot4219 : totK PA10K2 A10K2.t4219 = [0, 0, 474223370744, 1794907951643, 1850985244278, 479263695071, 31193351345, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
