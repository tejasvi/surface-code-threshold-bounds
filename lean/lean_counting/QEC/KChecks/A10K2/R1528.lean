import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6112 = true := by
  decide +kernel

theorem tot6112 : totK PA10K2 A10K2.t6112 = [0, 388194435581, 1589037910475, 1858695674006, 550464243742, 27461139606, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6113 = true := by
  decide +kernel

theorem tot6113 : totK PA10K2 A10K2.t6113 = [0, 0, 679132142712, 2088818267232, 1512314653741, 181523793969, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6114 = true := by
  decide +kernel

theorem tot6114 : totK PA10K2 A10K2.t6114 = [0, 583442206499, 1960255066631, 1948896126125, 564552398983, 76951464059, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6115 = true := by
  decide +kernel

theorem tot6115 : totK PA10K2 A10K2.t6115 = [0, 203638033980, 1234522911191, 2207022741474, 1196268601946, 135155016656, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
