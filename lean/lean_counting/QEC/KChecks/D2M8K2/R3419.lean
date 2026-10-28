import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13676 = true := by
  decide +kernel

theorem tot13676 : totK PD2M8K2 D2M8K2.t13676 = [0, 182424062440, 463018532986, 220390750119, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows13677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13677 = true := by
  decide +kernel

theorem tot13677 : totK PD2M8K2 D2M8K2.t13677 = [0, 23325336876, 312196794878, 468141320853, 87094263029, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13678 = true := by
  decide +kernel

theorem tot13678 : totK PD2M8K2 D2M8K2.t13678 = [0, 0, 196265679839, 464628810599, 171328766428, 11727338389, 0, 0] := by
  decide +kernel

theorem rows13679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13679 = true := by
  decide +kernel

theorem tot13679 : totK PD2M8K2 D2M8K2.t13679 = [0, 176261417076, 456030793753, 254017276959, 21235390585, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
