import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10704 = true := by
  decide +kernel

theorem tot10704 : totK PD2M8K2 D2M8K2.t10704 = [0, 0, 243621378679, 452188493835, 209945458568, 46080300104, 2813333534, 0] := by
  decide +kernel

theorem rows10705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10705 = true := by
  decide +kernel

theorem tot10705 : totK PD2M8K2 D2M8K2.t10705 = [0, 0, 177206166541, 478914795242, 246703400464, 14661533494, 0, 0] := by
  decide +kernel

theorem rows10706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10706 = true := by
  decide +kernel

theorem tot10706 : totK PD2M8K2 D2M8K2.t10706 = [0, 0, 185121592086, 476626832895, 205376473296, 9668425298, 0, 0] := by
  decide +kernel

theorem rows10707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10707 = true := by
  decide +kernel

theorem tot10707 : totK PD2M8K2 D2M8K2.t10707 = [0, 0, 120083296751, 436852196441, 298507826374, 21699417843, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
