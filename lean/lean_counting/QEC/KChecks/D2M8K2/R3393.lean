import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13572 = true := by
  decide +kernel

theorem tot13572 : totK PD2M8K2 D2M8K2.t13572 = [191320459823, 463903306059, 219520257241, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13573 = true := by
  decide +kernel

theorem tot13573 : totK PD2M8K2 D2M8K2.t13573 = [4188399740, 298957672860, 480427990649, 103925034533, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows13574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13574 = true := by
  decide +kernel

theorem tot13574 : totK PD2M8K2 D2M8K2.t13574 = [89174640444, 381657971647, 398930230114, 49609000985, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13575 = true := by
  decide +kernel

theorem tot13575 : totK PD2M8K2 D2M8K2.t13575 = [156846216414, 435115613728, 291964221225, 31556044309, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
