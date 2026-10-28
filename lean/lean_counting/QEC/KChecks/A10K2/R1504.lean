import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6016 = true := by
  decide +kernel

theorem tot6016 : totK PA10K2 A10K2.t6016 = [0, 282819497165, 1371979830429, 2009414780813, 966240063014, 163843497175, 14405838956, 0, 0, 0] := by
  decide +kernel

theorem rows6017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6017 = true := by
  decide +kernel

theorem tot6017 : totK PA10K2 A10K2.t6017 = [0, 271912620389, 1070814019848, 1689540123679, 1310051276147, 290862955104, 16597605730, 0, 0, 0] := by
  decide +kernel

theorem rows6018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6018 = true := by
  decide +kernel

theorem tot6018 : totK PA10K2 A10K2.t6018 = [0, 484401670405, 1641102184228, 1840591545226, 624661192408, 51963961291, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6019 = true := by
  decide +kernel

theorem tot6019 : totK PA10K2 A10K2.t6019 = [0, 62583825325, 1135498500757, 2308980486681, 1066147623568, 91769404032, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
