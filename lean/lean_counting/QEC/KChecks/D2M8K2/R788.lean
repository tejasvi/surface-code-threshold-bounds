import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3152 = true := by
  decide +kernel

theorem tot3152 : totK PD2M8K2 D2M8K2.t3152 = [0, 15884411423, 291945878431, 475250407696, 125906192467, 4009909289, 0, 0] := by
  decide +kernel

theorem rows3153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3153 = true := by
  decide +kernel

theorem tot3153 : totK PD2M8K2 D2M8K2.t3153 = [0, 78063362335, 338081065781, 389657292114, 80066020803, 1149959346, 0, 0] := by
  decide +kernel

theorem rows3154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3154 = true := by
  decide +kernel

theorem tot3154 : totK PD2M8K2 D2M8K2.t3154 = [0, 174454988170, 444797675383, 278394250477, 30435264497, 0, 0, 0] := by
  decide +kernel

theorem rows3155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3155 = true := by
  decide +kernel

theorem tot3155 : totK PD2M8K2 D2M8K2.t3155 = [0, 172739149261, 464134622598, 246601221536, 15440132108, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
