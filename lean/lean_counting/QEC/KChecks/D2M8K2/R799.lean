import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3196 = true := by
  decide +kernel

theorem tot3196 : totK PD2M8K2 D2M8K2.t3196 = [0, 169351759426, 452050482035, 254479595526, 19635349523, 0, 0, 0] := by
  decide +kernel

theorem rows3197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3197 = true := by
  decide +kernel

theorem tot3197 : totK PD2M8K2 D2M8K2.t3197 = [0, 207095060902, 462499306480, 209683867827, 12096313584, 0, 0, 0] := by
  decide +kernel

theorem rows3198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3198 = true := by
  decide +kernel

theorem tot3198 : totK PD2M8K2 D2M8K2.t3198 = [0, 37670822061, 351156420680, 398844213416, 62233942815, 1053411165, 0, 0] := by
  decide +kernel

theorem rows3199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3199 = true := by
  decide +kernel

theorem tot3199 : totK PD2M8K2 D2M8K2.t3199 = [0, 63955021880, 294894912980, 392827895410, 97294300204, 3667207281, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
