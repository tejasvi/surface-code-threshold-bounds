import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t656 = true := by
  decide +kernel

theorem tot656 : totK PA10K2 A10K2.t656 = [0, 0, 510154847730, 1768007570421, 1822581050467, 517052169020, 45824864222, 0, 0, 0] := by
  decide +kernel

theorem rows657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t657 = true := by
  decide +kernel

theorem tot657 : totK PA10K2 A10K2.t657 = [0, 0, 302082434609, 1537416709381, 2089636079920, 682372027291, 43560737560, 0, 0, 0] := by
  decide +kernel

theorem rows658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t658 = true := by
  decide +kernel

theorem tot658 : totK PA10K2 A10K2.t658 = [0, 213371739588, 562576911074, 796830304425, 1635947686954, 1166553305488, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t659 = true := by
  decide +kernel

theorem tot659 : totK PA10K2 A10K2.t659 = [0, 474190380768, 1766940920594, 1954939224115, 560516934079, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
