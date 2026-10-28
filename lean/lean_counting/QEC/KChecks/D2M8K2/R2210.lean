import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8840 = true := by
  decide +kernel

theorem tot8840 : totK PD2M8K2 D2M8K2.t8840 = [82780561812, 393082280840, 358525052923, 53836406989, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows8841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8841 = true := by
  decide +kernel

theorem tot8841 : totK PD2M8K2 D2M8K2.t8841 = [0, 182423141422, 465402829373, 189040676832, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows8842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8842 = true := by
  decide +kernel

theorem tot8842 : totK PD2M8K2 D2M8K2.t8842 = [160867177514, 444912342265, 278051100199, 35971859697, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8843 = true := by
  decide +kernel

theorem tot8843 : totK PD2M8K2 D2M8K2.t8843 = [178093191501, 467770843629, 238691965949, 15404046937, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
