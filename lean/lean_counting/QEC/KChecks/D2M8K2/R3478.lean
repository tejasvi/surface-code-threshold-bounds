import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13912 = true := by
  decide +kernel

theorem tot13912 : totK PD2M8K2 D2M8K2.t13912 = [0, 154569040053, 457306381008, 258565884985, 18337374713, 0, 0, 0] := by
  decide +kernel

theorem rows13913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13913 = true := by
  decide +kernel

theorem tot13913 : totK PD2M8K2 D2M8K2.t13913 = [0, 0, 304255097781, 465018704605, 91187959485, 1095107716, 0, 0] := by
  decide +kernel

theorem rows13914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13914 = true := by
  decide +kernel

theorem tot13914 : totK PD2M8K2 D2M8K2.t13914 = [138257157878, 294867299205, 168546595883, 199618165260, 88452003642, 3882006667, 0, 0] := by
  decide +kernel

theorem rows13915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13915 = true := by
  decide +kernel

theorem tot13915 : totK PD2M8K2 D2M8K2.t13915 = [188684247876, 462894298855, 234977035251, 16811517162, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
