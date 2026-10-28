import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6248 = true := by
  decide +kernel

theorem tot6248 : totK PA10K2 A10K2.t6248 = [0, 0, 516195587665, 1818926298258, 1970327390845, 690374742739, 56126783694, 0, 0, 0] := by
  decide +kernel

theorem rows6249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6249 = true := by
  decide +kernel

theorem tot6249 : totK PA10K2 A10K2.t6249 = [0, 0, 581655340520, 1935987093296, 1904562959572, 521917688033, 32070512872, 0, 0, 0] := by
  decide +kernel

theorem rows6250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6250 = true := by
  decide +kernel

theorem tot6250 : totK PA10K2 A10K2.t6250 = [0, 0, 0, 898247594650, 2281959905171, 1489267727317, 251646424280, 7380853412, 0, 0] := by
  decide +kernel

theorem rows6251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6251 = true := by
  decide +kernel

theorem tot6251 : totK PA10K2 A10K2.t6251 = [0, 0, 504494621672, 1860795536101, 2074076879825, 683721523159, 49551933704, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
