import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11020 = true := by
  decide +kernel

theorem tot11020 : totK PD2M8K2 D2M8K2.t11020 = [84865244063, 330543356202, 363305669283, 97161447816, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11021 = true := by
  decide +kernel

theorem tot11021 : totK PD2M8K2 D2M8K2.t11021 = [183816046749, 433588911161, 259514242163, 28766990757, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11022 = true := by
  decide +kernel

theorem tot11022 : totK PD2M8K2 D2M8K2.t11022 = [143538345355, 459329627138, 278695299216, 18713532954, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11023 = true := by
  decide +kernel

theorem tot11023 : totK PD2M8K2 D2M8K2.t11023 = [0, 280630857717, 518812665646, 104041881997, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
