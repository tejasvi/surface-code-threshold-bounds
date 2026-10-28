import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6 : KTree.allE (rowCheckK PA6K2 tA6K2) A6K2.t6 = true := by
  decide +kernel

theorem tot6 : totK PA6K2 A6K2.t6 = [0, 542299276541, 1767169811102, 1664625153343, 444980229694, 30542341996] := by
  decide +kernel

end QECKChecks.A6K2
