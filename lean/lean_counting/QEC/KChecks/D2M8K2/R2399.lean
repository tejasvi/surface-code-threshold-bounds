import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9596 = true := by
  decide +kernel

theorem tot9596 : totK PD2M8K2 D2M8K2.t9596 = [0, 173756607032, 469893809507, 225473578296, 14631128802, 0, 0, 0] := by
  decide +kernel

theorem rows9597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9597 = true := by
  decide +kernel

theorem tot9597 : totK PD2M8K2 D2M8K2.t9597 = [0, 182354883610, 469597995031, 207331151541, 7913321096, 0, 0, 0] := by
  decide +kernel

theorem rows9598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9598 = true := by
  decide +kernel

theorem tot9598 : totK PD2M8K2 D2M8K2.t9598 = [0, 55661912469, 324137821122, 419519255033, 81283600511, 1310285577, 0, 0] := by
  decide +kernel

theorem rows9599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9599 = true := by
  decide +kernel

theorem tot9599 : totK PD2M8K2 D2M8K2.t9599 = [0, 74173181751, 358917518811, 416170906687, 40854223675, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
