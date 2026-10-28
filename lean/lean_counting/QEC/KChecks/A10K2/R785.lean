import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3140 = true := by
  decide +kernel

theorem tot3140 : totK PA10K2 A10K2.t3140 = [0, 0, 537680587155, 1914272020731, 2031098873028, 581624640001, 29323168872, 0, 0, 0] := by
  decide +kernel

theorem rows3141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3141 = true := by
  decide +kernel

theorem tot3141 : totK PA10K2 A10K2.t3141 = [0, 0, 0, 805270940109, 2263643828245, 1645828379467, 273277671015, 6853348008, 0, 0] := by
  decide +kernel

theorem rows3142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3142 = true := by
  decide +kernel

theorem tot3142 : totK PA10K2 A10K2.t3142 = [0, 0, 0, 431932993080, 1760128904775, 2162260472889, 731703931132, 41529508497, 0, 0] := by
  decide +kernel

theorem rows3143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3143 = true := by
  decide +kernel

theorem tot3143 : totK PA10K2 A10K2.t3143 = [0, 0, 0, 589187642918, 1954634280668, 1833640116373, 399500209255, 12496645144, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
