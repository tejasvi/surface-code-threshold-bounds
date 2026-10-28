import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6300 = true := by
  decide +kernel

theorem tot6300 : totK PD2M8K2 D2M8K2.t6300 = [0, 89869257916, 343941842739, 377321058397, 85381572967, 1242138600, 0, 0] := by
  decide +kernel

theorem rows6301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6301 = true := by
  decide +kernel

theorem tot6301 : totK PD2M8K2 D2M8K2.t6301 = [0, 0, 235542397015, 463713065681, 154995879225, 7182288656, 0, 0] := by
  decide +kernel

theorem rows6302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6302 = true := by
  decide +kernel

theorem tot6302 : totK PD2M8K2 D2M8K2.t6302 = [0, 92081819623, 316645074373, 331111460602, 142848381624, 13326740810, 0, 0] := by
  decide +kernel

theorem rows6303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6303 = true := by
  decide +kernel

theorem tot6303 : totK PD2M8K2 D2M8K2.t6303 = [0, 187175120736, 452896101254, 230662503531, 16995378214, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
