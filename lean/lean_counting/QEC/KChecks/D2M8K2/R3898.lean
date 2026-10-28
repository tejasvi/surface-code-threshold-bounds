import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15592 = true := by
  decide +kernel

theorem tot15592 : totK PD2M8K2 D2M8K2.t15592 = [0, 0, 208561563180, 498405929074, 178034040651, 4967996017, 0, 0] := by
  decide +kernel

theorem rows15593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15593 = true := by
  decide +kernel

theorem tot15593 : totK PD2M8K2 D2M8K2.t15593 = [0, 0, 193471696463, 459451411484, 218754085319, 17047412850, 0, 0] := by
  decide +kernel

theorem rows15594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15594 = true := by
  decide +kernel

theorem tot15594 : totK PD2M8K2 D2M8K2.t15594 = [0, 0, 182130810464, 481125134832, 209885359586, 11023652771, 0, 0] := by
  decide +kernel

theorem rows15595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15595 = true := by
  decide +kernel

theorem tot15595 : totK PD2M8K2 D2M8K2.t15595 = [0, 0, 168344330939, 469798017801, 214405946264, 7693443986, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
