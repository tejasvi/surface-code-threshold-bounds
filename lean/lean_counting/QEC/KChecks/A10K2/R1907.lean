import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7628 = true := by
  decide +kernel

theorem tot7628 : totK PA10K2 A10K2.t7628 = [0, 0, 0, 346082439795, 1504473424730, 2153724186544, 877087794362, 67827945323, 0, 0] := by
  decide +kernel

theorem rows7629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7629 = true := by
  decide +kernel

theorem tot7629 : totK PA10K2 A10K2.t7629 = [0, 0, 0, 418021379034, 1709696136316, 2037969392353, 758738630593, 62702525251, 0, 0] := by
  decide +kernel

theorem rows7630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7630 = true := by
  decide +kernel

theorem tot7630 : totK PA10K2 A10K2.t7630 = [0, 0, 0, 192978286149, 1104615590009, 2012473764775, 1340757596505, 214449877947, 6439430839, 0] := by
  decide +kernel

theorem rows7631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7631 = true := by
  decide +kernel

theorem tot7631 : totK PA10K2 A10K2.t7631 = [0, 0, 0, 482731890138, 1834447294211, 2039782910926, 554383919476, 22108643497, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
