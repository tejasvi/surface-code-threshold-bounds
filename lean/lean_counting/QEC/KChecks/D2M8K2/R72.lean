import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t288 = true := by
  decide +kernel

theorem tot288 : totK PD2M8K2 D2M8K2.t288 = [187952900090, 475691845584, 222398713617, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t289 = true := by
  decide +kernel

theorem tot289 : totK PD2M8K2 D2M8K2.t289 = [33615612074, 312701365648, 454492911137, 96357746943, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t290 = true := by
  decide +kernel

theorem tot290 : totK PD2M8K2 D2M8K2.t290 = [0, 197070467007, 476206707190, 189170789938, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t291 = true := by
  decide +kernel

theorem tot291 : totK PD2M8K2 D2M8K2.t291 = [175822662127, 463711684776, 254033787377, 23575502741, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
