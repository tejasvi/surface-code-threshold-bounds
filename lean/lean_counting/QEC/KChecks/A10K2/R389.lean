import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1556 = true := by
  decide +kernel

theorem tot1556 : totK PA10K2 A10K2.t1556 = [0, 0, 0, 789828803741, 2290156241078, 1714414185824, 250630129591, 6066958478, 0, 0] := by
  decide +kernel

theorem rows1557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1557 = true := by
  decide +kernel

theorem tot1557 : totK PA10K2 A10K2.t1557 = [0, 0, 318420800840, 1158131113679, 1717462690044, 1364513519953, 416337244770, 29541060178, 0, 0] := by
  decide +kernel

theorem rows1558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1558 = true := by
  decide +kernel

theorem tot1558 : totK PA10K2 A10K2.t1558 = [0, 0, 506492027639, 1798374070102, 1909291986028, 516136618299, 31923522143, 0, 0, 0] := by
  decide +kernel

theorem rows1559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1559 = true := by
  decide +kernel

theorem tot1559 : totK PA10K2 A10K2.t1559 = [0, 0, 30259347190, 766617281115, 2074772107192, 1604484676777, 363842522923, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
