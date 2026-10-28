import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10044 = true := by
  decide +kernel

theorem tot10044 : totK PD2M8K2 D2M8K2.t10044 = [0, 0, 20599152287, 203574590448, 451793745880, 204119801710, 8969136212, 0] := by
  decide +kernel

theorem rows10045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10045 = true := by
  decide +kernel

theorem tot10045 : totK PD2M8K2 D2M8K2.t10045 = [0, 0, 208268743844, 473065439749, 221633202970, 21899705541, 0, 0] := by
  decide +kernel

theorem rows10046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10046 = true := by
  decide +kernel

theorem tot10046 : totK PD2M8K2 D2M8K2.t10046 = [0, 0, 170267687701, 463642808890, 240973744593, 9440393694, 0, 0] := by
  decide +kernel

theorem rows10047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10047 = true := by
  decide +kernel

theorem tot10047 : totK PD2M8K2 D2M8K2.t10047 = [0, 0, 0, 285054303216, 492291027209, 115054282279, 4009909289, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
