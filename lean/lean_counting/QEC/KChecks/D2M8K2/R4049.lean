import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16196 = true := by
  decide +kernel

theorem tot16196 : totK PD2M8K2 D2M8K2.t16196 = [0, 0, 160539232489, 456282009595, 265051630446, 23097160531, 0, 0] := by
  decide +kernel

theorem rows16197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16197 = true := by
  decide +kernel

theorem tot16197 : totK PD2M8K2 D2M8K2.t16197 = [0, 0, 181688270574, 471940968847, 249498378249, 14658973218, 0, 0] := by
  decide +kernel

theorem rows16198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16198 = true := by
  decide +kernel

theorem tot16198 : totK PD2M8K2 D2M8K2.t16198 = [0, 186864078631, 455704530974, 212688349130, 33762855784, 7093611788, 0, 0] := by
  decide +kernel

theorem rows16199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16199 = true := by
  decide +kernel

theorem tot16199 : totK PD2M8K2 D2M8K2.t16199 = [0, 203528159980, 470141675749, 203058093360, 10442318729, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
