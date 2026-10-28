import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11636 = true := by
  decide +kernel

theorem tot11636 : totK PD2M8K2 D2M8K2.t11636 = [0, 157181202861, 453961354440, 273222207014, 17765848274, 0, 0, 0] := by
  decide +kernel

theorem rows11637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11637 = true := by
  decide +kernel

theorem tot11637 : totK PD2M8K2 D2M8K2.t11637 = [18547827660, 193226389908, 451582146446, 211805621277, 9185044720, 0, 0, 0] := by
  decide +kernel

theorem rows11638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11638 = true := by
  decide +kernel

theorem tot11638 : totK PD2M8K2 D2M8K2.t11638 = [190979170537, 463208443402, 248520346070, 23124774842, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11639 = true := by
  decide +kernel

theorem tot11639 : totK PD2M8K2 D2M8K2.t11639 = [184533498879, 482174718642, 232610919072, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
