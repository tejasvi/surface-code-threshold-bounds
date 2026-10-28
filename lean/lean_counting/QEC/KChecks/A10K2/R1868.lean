import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7472 = true := by
  decide +kernel

theorem tot7472 : totK PA10K2 A10K2.t7472 = [0, 0, 0, 498000013582, 1916233122422, 1826786751661, 427007089608, 25734533292, 0, 0] := by
  decide +kernel

theorem rows7473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7473 = true := by
  decide +kernel

theorem tot7473 : totK PA10K2 A10K2.t7473 = [0, 0, 411997530451, 1542834601327, 1800889939260, 858215376832, 158032515224, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7474 = true := by
  decide +kernel

theorem tot7474 : totK PA10K2 A10K2.t7474 = [0, 0, 270960021267, 1464830437222, 2040859834973, 688429963750, 44652943964, 0, 0, 0] := by
  decide +kernel

theorem rows7475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7475 = true := by
  decide +kernel

theorem tot7475 : totK PA10K2 A10K2.t7475 = [0, 0, 177412673197, 1000137314439, 2002182521829, 1296400119233, 202549362824, 6239673734, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
