import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1644 = true := by
  decide +kernel

theorem tot1644 : totK PA10K2 A10K2.t1644 = [0, 388272196882, 1718688877194, 2171238413750, 753682888144, 56413849035, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1645 = true := by
  decide +kernel

theorem tot1645 : totK PA10K2 A10K2.t1645 = [0, 0, 503715355508, 1915814285511, 2043227032351, 591255485026, 36540832150, 0, 0, 0] := by
  decide +kernel

theorem rows1646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1646 = true := by
  decide +kernel

theorem tot1646 : totK PA10K2 A10K2.t1646 = [0, 0, 461108409457, 1824292849927, 1940750774586, 457088567458, 25667075836, 0, 0, 0] := by
  decide +kernel

theorem rows1647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1647 = true := by
  decide +kernel

theorem tot1647 : totK PA10K2 A10K2.t1647 = [0, 0, 231235616086, 1152289521543, 1966568397819, 1196673973653, 253625118017, 20060612110, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
