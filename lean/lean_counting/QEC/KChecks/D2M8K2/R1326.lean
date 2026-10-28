import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5304 = true := by
  decide +kernel

theorem tot5304 : totK PD2M8K2 D2M8K2.t5304 = [0, 0, 173581853378, 488425326857, 246468829581, 12206498855, 0, 0] := by
  decide +kernel

theorem rows5305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5305 = true := by
  decide +kernel

theorem tot5305 : totK PD2M8K2 D2M8K2.t5305 = [0, 0, 86354224797, 419646545396, 355430504875, 26263605064, 0, 0] := by
  decide +kernel

theorem rows5306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5306 = true := by
  decide +kernel

theorem tot5306 : totK PD2M8K2 D2M8K2.t5306 = [0, 0, 83030568158, 339551901340, 364326194300, 73744802644, 1330264907, 0] := by
  decide +kernel

theorem rows5307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5307 = true := by
  decide +kernel

theorem tot5307 : totK PD2M8K2 D2M8K2.t5307 = [0, 0, 177414678640, 451282331890, 263316853606, 25454216038, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
