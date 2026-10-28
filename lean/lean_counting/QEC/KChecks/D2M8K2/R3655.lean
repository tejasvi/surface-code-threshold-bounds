import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14620 = true := by
  decide +kernel

theorem tot14620 : totK PD2M8K2 D2M8K2.t14620 = [0, 0, 157340014571, 449029772980, 240107641683, 18964648663, 0, 0] := by
  decide +kernel

theorem rows14621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14621 = true := by
  decide +kernel

theorem tot14621 : totK PD2M8K2 D2M8K2.t14621 = [0, 0, 233565876254, 493177767980, 143295160707, 2227891822, 0, 0] := by
  decide +kernel

theorem rows14622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14622 = true := by
  decide +kernel

theorem tot14622 : totK PD2M8K2 D2M8K2.t14622 = [0, 0, 174937934406, 494836942565, 219384361299, 6649401931, 0, 0] := by
  decide +kernel

theorem rows14623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14623 = true := by
  decide +kernel

theorem tot14623 : totK PD2M8K2 D2M8K2.t14623 = [0, 0, 169276469888, 451230595312, 223082063214, 14917588509, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
