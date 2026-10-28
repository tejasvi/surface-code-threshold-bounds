import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3768 = true := by
  decide +kernel

theorem tot3768 : totK PA10K2 A10K2.t3768 = [0, 0, 0, 626224929896, 2132387699363, 1866364012054, 290102684323, 5526792442, 0, 0] := by
  decide +kernel

theorem rows3769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3769 = true := by
  decide +kernel

theorem tot3769 : totK PA10K2 A10K2.t3769 = [0, 0, 0, 476996154951, 1808931409235, 1896851178997, 466386940212, 31088438951, 0, 0] := by
  decide +kernel

theorem rows3770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3770 = true := by
  decide +kernel

theorem tot3770 : totK PA10K2 A10K2.t3770 = [0, 0, 0, 411578125515, 1761671452999, 1965311936872, 493188682627, 31772334738, 0, 0] := by
  decide +kernel

theorem rows3771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3771 = true := by
  decide +kernel

theorem tot3771 : totK PA10K2 A10K2.t3771 = [0, 0, 118410781347, 275418770379, 842078140896, 1966573022137, 1202056142734, 189373599726, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2
