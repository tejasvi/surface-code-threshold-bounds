import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16080 = true := by
  decide +kernel

theorem tot16080 : totK PD2M8K2 D2M8K2.t16080 = [0, 0, 79341861146, 377054103563, 368831253000, 40044910090, 0, 0] := by
  decide +kernel

theorem rows16081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16081 = true := by
  decide +kernel

theorem tot16081 : totK PD2M8K2 D2M8K2.t16081 = [0, 0, 164574254448, 488416893120, 240090442929, 9677551141, 0, 0] := by
  decide +kernel

theorem rows16082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16082 = true := by
  decide +kernel

theorem tot16082 : totK PD2M8K2 D2M8K2.t16082 = [0, 0, 181957123347, 462469515818, 219808834077, 10869304733, 0, 0] := by
  decide +kernel

theorem rows16083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16083 = true := by
  decide +kernel

theorem tot16083 : totK PD2M8K2 D2M8K2.t16083 = [0, 0, 217801702309, 500361095216, 187983771489, 3984357976, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
