import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7016 = true := by
  decide +kernel

theorem tot7016 : totK PD2M8K2 D2M8K2.t7016 = [0, 183773375668, 460416442672, 230431848251, 15797041242, 0, 0, 0] := by
  decide +kernel

theorem rows7017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7017 = true := by
  decide +kernel

theorem tot7017 : totK PD2M8K2 D2M8K2.t7017 = [0, 60173805979, 293853738653, 376799702392, 170759554192, 16716266525, 0, 0] := by
  decide +kernel

theorem rows7018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7018 = true := by
  decide +kernel

theorem tot7018 : totK PD2M8K2 D2M8K2.t7018 = [0, 0, 205608308508, 472959814659, 196837020320, 6886221117, 0, 0] := by
  decide +kernel

theorem rows7019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7019 = true := by
  decide +kernel

theorem tot7019 : totK PD2M8K2 D2M8K2.t7019 = [0, 84425303906, 262585854947, 383006957898, 157044457326, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
