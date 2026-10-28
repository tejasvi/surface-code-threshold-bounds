import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13944 = true := by
  decide +kernel

theorem tot13944 : totK PD2M8K2 D2M8K2.t13944 = [0, 183902421640, 442440737710, 259007573366, 28172471682, 0, 0, 0] := by
  decide +kernel

theorem rows13945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13945 = true := by
  decide +kernel

theorem tot13945 : totK PD2M8K2 D2M8K2.t13945 = [0, 199261606720, 474794562816, 209184077251, 12058613711, 0, 0, 0] := by
  decide +kernel

theorem rows13946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13946 = true := by
  decide +kernel

theorem tot13946 : totK PD2M8K2 D2M8K2.t13946 = [0, 30623113973, 339214861731, 443518640825, 76095252166, 1107157161, 0, 0] := by
  decide +kernel

theorem rows13947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13947 = true := by
  decide +kernel

theorem tot13947 : totK PD2M8K2 D2M8K2.t13947 = [0, 75371252259, 307189098414, 379693428139, 105217504717, 3824247485, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
