import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6060 = true := by
  decide +kernel

theorem tot6060 : totK PA10K2 A10K2.t6060 = [0, 476236816663, 1772332387159, 2011445741194, 671516708577, 30057177631, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6061 = true := by
  decide +kernel

theorem tot6061 : totK PA10K2 A10K2.t6061 = [0, 0, 773721551478, 2227950863029, 1550173794870, 272869508763, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows6062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6062 = true := by
  decide +kernel

theorem tot6062 : totK PA10K2 A10K2.t6062 = [0, 600380009038, 1920224545326, 1859408009734, 611589881284, 63782358112, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6063 = true := by
  decide +kernel

theorem tot6063 : totK PA10K2 A10K2.t6063 = [0, 84539485306, 934108528723, 2187321968641, 1546766630355, 269437599551, 7047025452, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
