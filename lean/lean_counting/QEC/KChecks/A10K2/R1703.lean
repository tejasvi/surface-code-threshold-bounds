import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6812 = true := by
  decide +kernel

theorem tot6812 : totK PA10K2 A10K2.t6812 = [453332237001, 1541493400483, 1557560550316, 846095106550, 379367339818, 44535473551, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6813 = true := by
  decide +kernel

theorem tot6813 : totK PA10K2 A10K2.t6813 = [308706262922, 1461798264475, 2150383045514, 946109512397, 82106650890, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6814 = true := by
  decide +kernel

theorem tot6814 : totK PA10K2 A10K2.t6814 = [0, 549528898098, 1956356250420, 1838342296982, 461404527330, 29778615803, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6815 = true := by
  decide +kernel

theorem tot6815 : totK PA10K2 A10K2.t6815 = [537990084717, 1866861965355, 1857997317748, 509220464234, 44959861167, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
