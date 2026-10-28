import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows0 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t0 = true := by
  decide +kernel

theorem tot0 : totK PD2M8K2 D2M8K2.t0 = [208771193549, 492027178810, 203436985353, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1 = true := by
  decide +kernel

theorem tot1 : totK PD2M8K2 D2M8K2.t1 = [193246328557, 474730915058, 224319287537, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2 = true := by
  decide +kernel

theorem tot2 : totK PD2M8K2 D2M8K2.t2 = [37537489105, 320293816347, 446477234633, 97721069935, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows3 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3 = true := by
  decide +kernel

theorem tot3 : totK PD2M8K2 D2M8K2.t3 = [51861757563, 354088710260, 458068167990, 57863872286, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
