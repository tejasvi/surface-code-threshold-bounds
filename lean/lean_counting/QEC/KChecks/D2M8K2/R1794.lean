import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7176 = true := by
  decide +kernel

theorem tot7176 : totK PD2M8K2 D2M8K2.t7176 = [0, 193835162488, 479988439221, 208481833974, 9845055932, 0, 0, 0] := by
  decide +kernel

theorem rows7177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7177 = true := by
  decide +kernel

theorem tot7177 : totK PD2M8K2 D2M8K2.t7177 = [0, 167092244580, 465056698049, 245006505497, 13787972337, 0, 0, 0] := by
  decide +kernel

theorem rows7178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7178 = true := by
  decide +kernel

theorem tot7178 : totK PD2M8K2 D2M8K2.t7178 = [0, 0, 271703907669, 507789357982, 111852955936, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7179 = true := by
  decide +kernel

theorem tot7179 : totK PD2M8K2 D2M8K2.t7179 = [0, 89458300890, 382851249684, 392940880809, 53539726615, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
