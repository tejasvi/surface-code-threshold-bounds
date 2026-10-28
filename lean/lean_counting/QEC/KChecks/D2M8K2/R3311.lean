import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13244 = true := by
  decide +kernel

theorem tot13244 : totK PD2M8K2 D2M8K2.t13244 = [0, 0, 197145219736, 480087342370, 196009277816, 9757737807, 0, 0] := by
  decide +kernel

theorem rows13245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13245 = true := by
  decide +kernel

theorem tot13245 : totK PD2M8K2 D2M8K2.t13245 = [0, 0, 177968810090, 464302091778, 230871054516, 13772981906, 0, 0] := by
  decide +kernel

theorem rows13246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13246 = true := by
  decide +kernel

theorem tot13246 : totK PD2M8K2 D2M8K2.t13246 = [0, 0, 170892548013, 476163575899, 213570056921, 7870241454, 0, 0] := by
  decide +kernel

theorem rows13247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13247 = true := by
  decide +kernel

theorem tot13247 : totK PD2M8K2 D2M8K2.t13247 = [0, 127234728902, 352905329931, 360349815891, 88558954591, 1236758454, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
