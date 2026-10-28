import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9020 = true := by
  decide +kernel

theorem tot9020 : totK PD2M8K2 D2M8K2.t9020 = [0, 0, 298589080615, 483628552960, 87971400053, 1164319620, 0, 0] := by
  decide +kernel

theorem rows9021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9021 = true := by
  decide +kernel

theorem tot9021 : totK PD2M8K2 D2M8K2.t9021 = [0, 160548355868, 447575855105, 278435261998, 25467063204, 0, 0, 0] := by
  decide +kernel

theorem rows9022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9022 = true := by
  decide +kernel

theorem tot9022 : totK PD2M8K2 D2M8K2.t9022 = [0, 177537856126, 442984524233, 257193053673, 26592020564, 0, 0, 0] := by
  decide +kernel

theorem rows9023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9023 = true := by
  decide +kernel

theorem tot9023 : totK PD2M8K2 D2M8K2.t9023 = [0, 87346212865, 384866519762, 360258007335, 54701040600, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
