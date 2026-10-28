import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9456 = true := by
  decide +kernel

theorem tot9456 : totK PD2M8K2 D2M8K2.t9456 = [179867083042, 466472675587, 245766988706, 16936954192, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9457 = true := by
  decide +kernel

theorem tot9457 : totK PD2M8K2 D2M8K2.t9457 = [0, 263066512666, 502815203337, 123342998506, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows9458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9458 = true := by
  decide +kernel

theorem tot9458 : totK PD2M8K2 D2M8K2.t9458 = [0, 197394599064, 483349197216, 192203387864, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows9459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9459 = true := by
  decide +kernel

theorem tot9459 : totK PD2M8K2 D2M8K2.t9459 = [0, 176312216880, 461109255855, 231359663003, 15860424110, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
