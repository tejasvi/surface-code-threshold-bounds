import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6676 = true := by
  decide +kernel

theorem tot6676 : totK PD2M8K2 D2M8K2.t6676 = [0, 0, 221826202826, 501872138833, 156783295092, 4880895167, 0, 0] := by
  decide +kernel

theorem rows6677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6677 = true := by
  decide +kernel

theorem tot6677 : totK PD2M8K2 D2M8K2.t6677 = [0, 155064126121, 441012640377, 266891060997, 29955758408, 0, 0, 0] := by
  decide +kernel

theorem rows6678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6678 = true := by
  decide +kernel

theorem tot6678 : totK PD2M8K2 D2M8K2.t6678 = [0, 175631737691, 455467079678, 239900982875, 14996382985, 0, 0, 0] := by
  decide +kernel

theorem rows6679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6679 = true := by
  decide +kernel

theorem tot6679 : totK PD2M8K2 D2M8K2.t6679 = [0, 63502904405, 322143340291, 397008006548, 84844510208, 1310517177, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
