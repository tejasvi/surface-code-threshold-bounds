import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13048 = true := by
  decide +kernel

theorem tot13048 : totK PD2M8K2 D2M8K2.t13048 = [0, 0, 65446076470, 312726247982, 385492514147, 100764188079, 3804183361, 0] := by
  decide +kernel

theorem rows13049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13049 = true := by
  decide +kernel

theorem tot13049 : totK PD2M8K2 D2M8K2.t13049 = [0, 0, 191611978475, 462129356804, 239695349580, 19146825962, 0, 0] := by
  decide +kernel

theorem rows13050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13050 = true := by
  decide +kernel

theorem tot13050 : totK PD2M8K2 D2M8K2.t13050 = [0, 0, 165811727347, 485822551380, 247599498898, 10834427765, 0, 0] := by
  decide +kernel

theorem rows13051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13051 = true := by
  decide +kernel

theorem tot13051 : totK PD2M8K2 D2M8K2.t13051 = [0, 173576733255, 421592416705, 207762996010, 78352930382, 12385654569, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
