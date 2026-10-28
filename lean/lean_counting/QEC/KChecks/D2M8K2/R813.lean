import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3252 = true := by
  decide +kernel

theorem tot3252 : totK PD2M8K2 D2M8K2.t3252 = [157524901095, 456788948159, 287429920063, 23459543939, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3253 = true := by
  decide +kernel

theorem tot3253 : totK PD2M8K2 D2M8K2.t3253 = [0, 237643197799, 497945260210, 146280813875, 2304167554, 0, 0, 0] := by
  decide +kernel

theorem rows3254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3254 = true := by
  decide +kernel

theorem tot3254 : totK PD2M8K2 D2M8K2.t3254 = [0, 181091003179, 466949087443, 222808062534, 12667552787, 0, 0, 0] := by
  decide +kernel

theorem rows3255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3255 = true := by
  decide +kernel

theorem tot3255 : totK PD2M8K2 D2M8K2.t3255 = [0, 204523342580, 473431037231, 207957688527, 12413128817, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
