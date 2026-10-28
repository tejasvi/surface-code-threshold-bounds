import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5284 = true := by
  decide +kernel

theorem tot5284 : totK PA10K2 A10K2.t5284 = [0, 564595576905, 1930774391534, 1796899888884, 445822972528, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5285 = true := by
  decide +kernel

theorem tot5285 : totK PA10K2 A10K2.t5285 = [0, 0, 952203098777, 2376212448641, 1257202506316, 113943173993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5286 = true := by
  decide +kernel

theorem tot5286 : totK PA10K2 A10K2.t5286 = [0, 0, 441544693214, 1831265430469, 1930516334849, 530878760974, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows5287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5287 = true := by
  decide +kernel

theorem tot5287 : totK PA10K2 A10K2.t5287 = [0, 0, 569411275742, 1949423785735, 1852515186611, 432883110125, 13149912228, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
