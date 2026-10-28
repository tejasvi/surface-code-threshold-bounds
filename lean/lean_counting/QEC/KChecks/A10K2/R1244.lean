import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4976 = true := by
  decide +kernel

theorem tot4976 : totK PA10K2 A10K2.t4976 = [0, 459752176240, 1866988030504, 1967423942974, 482409829570, 27327534915, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4977 = true := by
  decide +kernel

theorem tot4977 : totK PA10K2 A10K2.t4977 = [0, 111145374367, 934703152772, 2109954200928, 1275099413282, 177654065331, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows4978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4978 = true := by
  decide +kernel

theorem tot4978 : totK PA10K2 A10K2.t4978 = [214169341392, 804358139362, 1610115249026, 1685537344412, 590928288963, 58509527586, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4979 = true := by
  decide +kernel

theorem tot4979 : totK PA10K2 A10K2.t4979 = [407879137342, 1729199557796, 2020870546662, 582864065429, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
