import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t728 = true := by
  decide +kernel

theorem tot728 : totK PD2M8K2 D2M8K2.t728 = [0, 186142684379, 451917375514, 244928986694, 24078004775, 0, 0, 0] := by
  decide +kernel

theorem rows729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t729 = true := by
  decide +kernel

theorem tot729 : totK PD2M8K2 D2M8K2.t729 = [0, 181396451794, 492962938333, 216550622012, 6610549359, 0, 0, 0] := by
  decide +kernel

theorem rows730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t730 = true := by
  decide +kernel

theorem tot730 : totK PD2M8K2 D2M8K2.t730 = [174121612761, 418876487004, 241842068901, 67633419050, 5618966238, 0, 0, 0] := by
  decide +kernel

theorem rows731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t731 = true := by
  decide +kernel

theorem tot731 : totK PD2M8K2 D2M8K2.t731 = [155061492323, 448364237313, 286391460783, 23464583082, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
