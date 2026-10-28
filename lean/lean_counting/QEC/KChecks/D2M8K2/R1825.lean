import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7300 = true := by
  decide +kernel

theorem tot7300 : totK PD2M8K2 D2M8K2.t7300 = [0, 0, 172906536359, 446562305584, 271452806481, 24042154819, 0, 0] := by
  decide +kernel

theorem rows7301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7301 = true := by
  decide +kernel

theorem tot7301 : totK PD2M8K2 D2M8K2.t7301 = [0, 0, 93773531552, 406637301236, 369178668691, 37699493677, 0, 0] := by
  decide +kernel

theorem rows7302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7302 = true := by
  decide +kernel

theorem tot7302 : totK PD2M8K2 D2M8K2.t7302 = [0, 0, 0, 260716930599, 485792717445, 146767373384, 4882834716, 0] := by
  decide +kernel

theorem rows7303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7303 = true := by
  decide +kernel

theorem tot7303 : totK PD2M8K2 D2M8K2.t7303 = [0, 94445126902, 239990604536, 233975746559, 243462924958, 107192755503, 8981457347, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
