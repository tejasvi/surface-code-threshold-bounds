import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14580 = true := by
  decide +kernel

theorem tot14580 : totK PD2M8K2 D2M8K2.t14580 = [0, 193077208353, 464005252241, 222482699970, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows14581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14581 = true := by
  decide +kernel

theorem tot14581 : totK PD2M8K2 D2M8K2.t14581 = [0, 202548345855, 490824546864, 193387555602, 5336070015, 0, 0, 0] := by
  decide +kernel

theorem rows14582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14582 = true := by
  decide +kernel

theorem tot14582 : totK PD2M8K2 D2M8K2.t14582 = [0, 164142508919, 474552853149, 232293132359, 8917007962, 0, 0, 0] := by
  decide +kernel

theorem rows14583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14583 = true := by
  decide +kernel

theorem tot14583 : totK PD2M8K2 D2M8K2.t14583 = [0, 0, 275208574295, 503618232029, 92947381264, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
