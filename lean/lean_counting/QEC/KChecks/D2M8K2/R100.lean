import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t400 = true := by
  decide +kernel

theorem tot400 : totK PD2M8K2 D2M8K2.t400 = [172438341442, 390983059415, 254175942848, 71215815399, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t401 = true := by
  decide +kernel

theorem tot401 : totK PD2M8K2 D2M8K2.t401 = [170648880015, 436257823156, 271880067919, 29592388275, 0, 0, 0, 0] := by
  decide +kernel

theorem rows402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t402 = true := by
  decide +kernel

theorem tot402 : totK PD2M8K2 D2M8K2.t402 = [92722701599, 407188195028, 337858256306, 47713942949, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t403 = true := by
  decide +kernel

theorem tot403 : totK PD2M8K2 D2M8K2.t403 = [0, 306323616502, 521119089068, 87773586300, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
