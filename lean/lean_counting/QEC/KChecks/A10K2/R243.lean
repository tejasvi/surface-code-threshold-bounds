import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t972 = true := by
  decide +kernel

theorem tot972 : totK PA10K2 A10K2.t972 = [0, 0, 196085955764, 1179511228141, 2111800548745, 1267494299966, 210229931254, 6904928264, 0, 0] := by
  decide +kernel

theorem rows973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t973 = true := by
  decide +kernel

theorem tot973 : totK PA10K2 A10K2.t973 = [0, 0, 254188123548, 1283579030057, 2143913806031, 1115787683038, 125786543078, 0, 0, 0] := by
  decide +kernel

theorem rows974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t974 = true := by
  decide +kernel

theorem tot974 : totK PA10K2 A10K2.t974 = [0, 0, 303258801711, 1471425936913, 2180780841684, 942796591086, 76004717364, 0, 0, 0] := by
  decide +kernel

theorem rows975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t975 = true := by
  decide +kernel

theorem tot975 : totK PA10K2 A10K2.t975 = [0, 0, 286110476401, 1207267295836, 1926919566628, 1344201642553, 229004075411, 6766355402, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
