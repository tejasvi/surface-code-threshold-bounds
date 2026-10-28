import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11308 = true := by
  decide +kernel

theorem tot11308 : totK PD2M8K2 D2M8K2.t11308 = [0, 229693589771, 494768559845, 169598517936, 6326225059, 0, 0, 0] := by
  decide +kernel

theorem rows11309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11309 = true := by
  decide +kernel

theorem tot11309 : totK PD2M8K2 D2M8K2.t11309 = [0, 192622881730, 460399910690, 215716159859, 14603436651, 0, 0, 0] := by
  decide +kernel

theorem rows11310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11310 = true := by
  decide +kernel

theorem tot11310 : totK PD2M8K2 D2M8K2.t11310 = [0, 185950553881, 471998424660, 214925884458, 12361325328, 0, 0, 0] := by
  decide +kernel

theorem rows11311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11311 = true := by
  decide +kernel

theorem tot11311 : totK PD2M8K2 D2M8K2.t11311 = [0, 0, 291938118804, 480960037227, 87955277846, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
