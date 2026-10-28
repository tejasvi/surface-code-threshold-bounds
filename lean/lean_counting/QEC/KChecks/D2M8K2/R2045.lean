import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8180 = true := by
  decide +kernel

theorem tot8180 : totK PD2M8K2 D2M8K2.t8180 = [0, 132604513239, 432399819385, 298153823730, 28175607806, 0, 0, 0] := by
  decide +kernel

theorem rows8181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8181 = true := by
  decide +kernel

theorem tot8181 : totK PD2M8K2 D2M8K2.t8181 = [0, 0, 271730977615, 498568363381, 106216060225, 1369150432, 0, 0] := by
  decide +kernel

theorem rows8182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8182 = true := by
  decide +kernel

theorem tot8182 : totK PD2M8K2 D2M8K2.t8182 = [0, 161935565392, 419564971214, 314903507711, 40805025532, 0, 0, 0] := by
  decide +kernel

theorem rows8183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8183 = true := by
  decide +kernel

theorem tot8183 : totK PD2M8K2 D2M8K2.t8183 = [0, 172145540122, 463244730846, 240969563928, 15730020004, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
