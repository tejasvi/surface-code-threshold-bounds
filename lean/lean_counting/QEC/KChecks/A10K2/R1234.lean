import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4936 = true := by
  decide +kernel

theorem tot4936 : totK PA10K2 A10K2.t4936 = [0, 285378750548, 1491822434731, 2095244407542, 752138551273, 44652943964, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4937 = true := by
  decide +kernel

theorem tot4937 : totK PA10K2 A10K2.t4937 = [0, 187308237962, 941569607034, 2045888968107, 1358370730184, 202549362824, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows4938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4938 = true := by
  decide +kernel

theorem tot4938 : totK PA10K2 A10K2.t4938 = [0, 440236534549, 1820055308981, 2068125313215, 627317147140, 33001472292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4939 = true := by
  decide +kernel

theorem tot4939 : totK PA10K2 A10K2.t4939 = [0, 0, 686884568956, 2191970364853, 1828270826294, 351141116181, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
