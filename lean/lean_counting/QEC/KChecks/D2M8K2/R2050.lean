import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8200 = true := by
  decide +kernel

theorem tot8200 : totK PD2M8K2 D2M8K2.t8200 = [0, 0, 185999020654, 480818813952, 209073899035, 7984731767, 0, 0] := by
  decide +kernel

theorem rows8201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8201 = true := by
  decide +kernel

theorem tot8201 : totK PD2M8K2 D2M8K2.t8201 = [0, 0, 131670941957, 429602544885, 288461344522, 22733488377, 0, 0] := by
  decide +kernel

theorem rows8202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8202 = true := by
  decide +kernel

theorem tot8202 : totK PD2M8K2 D2M8K2.t8202 = [0, 0, 0, 278944279331, 496104436199, 84573544659, 1310285577, 0] := by
  decide +kernel

theorem rows8203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8203 = true := by
  decide +kernel

theorem tot8203 : totK PD2M8K2 D2M8K2.t8203 = [0, 0, 179945842210, 427539395508, 281591040249, 37581555579, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
