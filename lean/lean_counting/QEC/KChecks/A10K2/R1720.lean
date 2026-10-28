import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6880 = true := by
  decide +kernel

theorem tot6880 : totK PA10K2 A10K2.t6880 = [0, 0, 593181773731, 2032628925705, 2005761523488, 475946913393, 13532411735, 0, 0, 0] := by
  decide +kernel

theorem rows6881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6881 = true := by
  decide +kernel

theorem tot6881 : totK PA10K2 A10K2.t6881 = [0, 0, 525189321057, 1862750605201, 1922142484992, 600921129088, 49111353342, 0, 0, 0] := by
  decide +kernel

theorem rows6882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6882 = true := by
  decide +kernel

theorem tot6882 : totK PA10K2 A10K2.t6882 = [0, 0, 526962436300, 1808438773866, 1811304792998, 482842503064, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows6883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6883 = true := by
  decide +kernel

theorem tot6883 : totK PA10K2 A10K2.t6883 = [0, 0, 0, 764162188835, 2127813226935, 1547259496399, 368794868059, 25239774317, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
