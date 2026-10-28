import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6824 = true := by
  decide +kernel

theorem tot6824 : totK PA10K2 A10K2.t6824 = [0, 537462021078, 1810134802851, 1820784014891, 583815135823, 56932753151, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6825 = true := by
  decide +kernel

theorem tot6825 : totK PA10K2 A10K2.t6825 = [0, 227291314947, 1294477673771, 2181052367211, 1177410411812, 125990791242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6826 = true := by
  decide +kernel

theorem tot6826 : totK PA10K2 A10K2.t6826 = [0, 280981490432, 1323241738149, 1994738711134, 1156735459724, 206516259453, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows6827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6827 = true := by
  decide +kernel

theorem tot6827 : totK PA10K2 A10K2.t6827 = [0, 596984120681, 1905602167339, 1870172665874, 542680592921, 23620721234, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
