import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12280 = true := by
  decide +kernel

theorem tot12280 : totK PD2M8K2 D2M8K2.t12280 = [190657011352, 470877906656, 234498435602, 16716523752, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12281 = true := by
  decide +kernel

theorem tot12281 : totK PD2M8K2 D2M8K2.t12281 = [79541284804, 371422525228, 364653059028, 85671355057, 10443687594, 0, 0, 0] := by
  decide +kernel

theorem rows12282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12282 = true := by
  decide +kernel

theorem tot12282 : totK PD2M8K2 D2M8K2.t12282 = [0, 158153423328, 451184472811, 272303869474, 18931388505, 0, 0, 0] := by
  decide +kernel

theorem rows12283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12283 = true := by
  decide +kernel

theorem tot12283 : totK PD2M8K2 D2M8K2.t12283 = [42866401516, 218601115866, 431272527286, 193869579323, 8036408690, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
