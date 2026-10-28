import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t984 = true := by
  decide +kernel

theorem tot984 : totK PD2M8K2 D2M8K2.t984 = [0, 170226334296, 469565747396, 240580320274, 12752126925, 0, 0, 0] := by
  decide +kernel

theorem rows985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t985 = true := by
  decide +kernel

theorem tot985 : totK PD2M8K2 D2M8K2.t985 = [0, 0, 258594691404, 479887688866, 127469014854, 2305904642, 0, 0] := by
  decide +kernel

theorem rows986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t986 = true := by
  decide +kernel

theorem tot986 : totK PD2M8K2 D2M8K2.t986 = [0, 66352686105, 255017159776, 373479998341, 146014131130, 10710292732, 0, 0] := by
  decide +kernel

theorem rows987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t987 = true := by
  decide +kernel

theorem tot987 : totK PD2M8K2 D2M8K2.t987 = [0, 187563674060, 485609286866, 217122472700, 11056080877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
