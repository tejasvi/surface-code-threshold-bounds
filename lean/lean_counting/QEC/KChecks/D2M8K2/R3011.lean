import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12044 = true := by
  decide +kernel

theorem tot12044 : totK PD2M8K2 D2M8K2.t12044 = [0, 0, 224077411156, 493245087184, 166472643110, 7233348802, 0, 0] := by
  decide +kernel

theorem rows12045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12045 = true := by
  decide +kernel

theorem tot12045 : totK PD2M8K2 D2M8K2.t12045 = [0, 75915933367, 281474654080, 381291913785, 125845237256, 5956649706, 0, 0] := by
  decide +kernel

theorem rows12046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12046 = true := by
  decide +kernel

theorem tot12046 : totK PD2M8K2 D2M8K2.t12046 = [0, 154522210884, 456192697398, 263254959797, 18369502288, 0, 0, 0] := by
  decide +kernel

theorem rows12047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12047 = true := by
  decide +kernel

theorem tot12047 : totK PD2M8K2 D2M8K2.t12047 = [0, 177019497597, 474828710374, 228685821591, 12169895203, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
