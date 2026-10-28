import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9296 = true := by
  decide +kernel

theorem tot9296 : totK PD2M8K2 D2M8K2.t9296 = [36923124222, 202547556691, 432780619079, 218799722658, 9177971211, 0, 0, 0] := by
  decide +kernel

theorem rows9297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9297 = true := by
  decide +kernel

theorem tot9297 : totK PD2M8K2 D2M8K2.t9297 = [173340848741, 446339949093, 251965385117, 22996132093, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9298 = true := by
  decide +kernel

theorem tot9298 : totK PD2M8K2 D2M8K2.t9298 = [186600705548, 473305031023, 223034816716, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9299 = true := by
  decide +kernel

theorem tot9299 : totK PD2M8K2 D2M8K2.t9299 = [0, 285148715413, 489930991408, 102843967846, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
