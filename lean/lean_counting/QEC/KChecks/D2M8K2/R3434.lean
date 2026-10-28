import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13736 = true := by
  decide +kernel

theorem tot13736 : totK PD2M8K2 D2M8K2.t13736 = [0, 85323046205, 318163896505, 382476771750, 98871937171, 3821179711, 0, 0] := by
  decide +kernel

theorem rows13737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13737 = true := by
  decide +kernel

theorem tot13737 : totK PD2M8K2 D2M8K2.t13737 = [0, 153435604607, 456346069749, 283605024769, 23882306715, 0, 0, 0] := by
  decide +kernel

theorem rows13738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13738 = true := by
  decide +kernel

theorem tot13738 : totK PD2M8K2 D2M8K2.t13738 = [0, 177290894043, 462964941183, 259066912579, 17874598108, 0, 0, 0] := by
  decide +kernel

theorem rows13739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13739 = true := by
  decide +kernel

theorem tot13739 : totK PD2M8K2 D2M8K2.t13739 = [0, 0, 272975146475, 510046857118, 115763858360, 1232609433, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
