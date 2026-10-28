import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5008 = true := by
  decide +kernel

theorem tot5008 : totK PD2M8K2 D2M8K2.t5008 = [0, 0, 182556428197, 497718509111, 225969297791, 6614277394, 0, 0] := by
  decide +kernel

theorem rows5009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5009 = true := by
  decide +kernel

theorem tot5009 : totK PD2M8K2 D2M8K2.t5009 = [0, 173216670710, 426254966652, 239964306700, 60012704406, 5592585378, 0, 0] := by
  decide +kernel

theorem rows5010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5010 = true := by
  decide +kernel

theorem tot5010 : totK PD2M8K2 D2M8K2.t5010 = [0, 181028765080, 476411286060, 237214416286, 14983329606, 0, 0, 0] := by
  decide +kernel

theorem rows5011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5011 = true := by
  decide +kernel

theorem tot5011 : totK PD2M8K2 D2M8K2.t5011 = [0, 83471534099, 336424553650, 383164417947, 85182274591, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
