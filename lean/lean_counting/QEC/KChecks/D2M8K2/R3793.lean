import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15172 = true := by
  decide +kernel

theorem tot15172 : totK PD2M8K2 D2M8K2.t15172 = [0, 0, 225032369628, 489954336771, 159542771013, 9404247146, 0, 0] := by
  decide +kernel

theorem rows15173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15173 = true := by
  decide +kernel

theorem tot15173 : totK PD2M8K2 D2M8K2.t15173 = [0, 154319968341, 428977940422, 273198679506, 46087219703, 2481160468, 0, 0] := by
  decide +kernel

theorem rows15174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15174 = true := by
  decide +kernel

theorem tot15174 : totK PD2M8K2 D2M8K2.t15174 = [0, 177699138832, 453765708954, 251723351623, 15183549182, 0, 0, 0] := by
  decide +kernel

theorem rows15175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15175 = true := by
  decide +kernel

theorem tot15175 : totK PD2M8K2 D2M8K2.t15175 = [0, 68351372962, 332252088874, 406993489879, 84887406144, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
