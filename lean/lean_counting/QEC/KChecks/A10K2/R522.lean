import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2088 = true := by
  decide +kernel

theorem tot2088 : totK PA10K2 A10K2.t2088 = [0, 0, 271870474702, 1052679006595, 1909624174267, 1210466275345, 187669909920, 5685526223, 0, 0] := by
  decide +kernel

theorem rows2089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2089 = true := by
  decide +kernel

theorem tot2089 : totK PA10K2 A10K2.t2089 = [0, 0, 492534805529, 1984383266375, 2012120158712, 514674502503, 27250992027, 0, 0, 0] := by
  decide +kernel

theorem rows2090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2090 = true := by
  decide +kernel

theorem tot2090 : totK PA10K2 A10K2.t2090 = [0, 424355675811, 1546840166019, 1691548987143, 736679861423, 206449711597, 24415340438, 0, 0, 0] := by
  decide +kernel

theorem rows2091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2091 = true := by
  decide +kernel

theorem tot2091 : totK PA10K2 A10K2.t2091 = [0, 309417675788, 1220036935395, 1828054376366, 1077738131122, 179754666553, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
