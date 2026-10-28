import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4216 = true := by
  decide +kernel

theorem tot4216 : totK PD2M8K2 D2M8K2.t4216 = [0, 0, 0, 299806553937, 510970065333, 96157663675, 0, 0] := by
  decide +kernel

theorem rows4217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4217 = true := by
  decide +kernel

theorem tot4217 : totK PD2M8K2 D2M8K2.t4217 = [0, 0, 0, 197601816688, 485933610422, 183342621628, 4627616211, 0] := by
  decide +kernel

theorem rows4218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4218 = true := by
  decide +kernel

theorem tot4218 : totK PD2M8K2 D2M8K2.t4218 = [0, 0, 0, 174865454023, 430002881992, 285228085674, 33047998259, 0] := by
  decide +kernel

theorem rows4219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4219 = true := by
  decide +kernel

theorem tot4219 : totK PD2M8K2 D2M8K2.t4219 = [0, 0, 0, 179460505655, 474521317078, 235827166173, 12844960481, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
