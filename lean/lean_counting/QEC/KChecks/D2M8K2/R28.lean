import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t112 = true := by
  decide +kernel

theorem tot112 : totK PD2M8K2 D2M8K2.t112 = [179581806258, 446858383416, 257542738260, 19954917495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t113 = true := by
  decide +kernel

theorem tot113 : totK PD2M8K2 D2M8K2.t113 = [68165910898, 343047212451, 391612305900, 80062323023, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t114 = true := by
  decide +kernel

theorem tot114 : totK PD2M8K2 D2M8K2.t114 = [0, 237184041944, 480752523793, 159211922119, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t115 = true := by
  decide +kernel

theorem tot115 : totK PD2M8K2 D2M8K2.t115 = [163482807363, 396713729120, 270098416403, 58538201516, 2481160468, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
