import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3232 = true := by
  decide +kernel

theorem tot3232 : totK PA10K2 A10K2.t3232 = [0, 0, 0, 436150433304, 1648224495138, 1861491700522, 636343792651, 54913717558, 0, 0] := by
  decide +kernel

theorem rows3233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3233 = true := by
  decide +kernel

theorem tot3233 : totK PA10K2 A10K2.t3233 = [0, 0, 0, 279666710650, 1480978664543, 2086048415720, 679339481072, 39251623300, 0, 0] := by
  decide +kernel

theorem rows3234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3234 = true := by
  decide +kernel

theorem tot3234 : totK PA10K2 A10K2.t3234 = [0, 0, 0, 471712450556, 1466343561922, 1716493533102, 912423482385, 160569842129, 5685526223, 0] := by
  decide +kernel

theorem rows3235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3235 = true := by
  decide +kernel

theorem tot3235 : totK PA10K2 A10K2.t3235 = [0, 0, 166940909255, 707931884443, 1566173215902, 1814876910471, 652121994539, 51666332465, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
