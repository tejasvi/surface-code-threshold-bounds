import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12916 = true := by
  decide +kernel

theorem tot12916 : totK PD2M8K2 D2M8K2.t12916 = [0, 20021956556, 187348306033, 456606615616, 223526536550, 12993903218, 0, 0] := by
  decide +kernel

theorem rows12917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12917 = true := by
  decide +kernel

theorem tot12917 : totK PD2M8K2 D2M8K2.t12917 = [0, 170815887679, 444685071687, 279345763269, 30379478485, 0, 0, 0] := by
  decide +kernel

theorem rows12918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12918 = true := by
  decide +kernel

theorem tot12918 : totK PD2M8K2 D2M8K2.t12918 = [0, 196988925551, 481370308020, 220842735104, 10537225917, 0, 0, 0] := by
  decide +kernel

theorem rows12919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12919 = true := by
  decide +kernel

theorem tot12919 : totK PD2M8K2 D2M8K2.t12919 = [0, 51959793179, 280693465817, 377653408376, 178237160419, 21400436502, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
