import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5500 = true := by
  decide +kernel

theorem tot5500 : totK PD2M8K2 D2M8K2.t5500 = [0, 0, 0, 0, 325162758023, 446678571218, 84746063341, 1415681459] := by
  decide +kernel

theorem rows5501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5501 = true := by
  decide +kernel

theorem tot5501 : totK PD2M8K2 D2M8K2.t5501 = [0, 0, 0, 173635257284, 460572703818, 251557858961, 23151530337, 0] := by
  decide +kernel

theorem rows5502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5502 = true := by
  decide +kernel

theorem tot5502 : totK PD2M8K2 D2M8K2.t5502 = [0, 0, 0, 187901623605, 448211647572, 236630046040, 14764353637, 0] := by
  decide +kernel

theorem rows5503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5503 = true := by
  decide +kernel

theorem tot5503 : totK PD2M8K2 D2M8K2.t5503 = [0, 0, 0, 79844595637, 412518111047, 379101078721, 41104235805, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
