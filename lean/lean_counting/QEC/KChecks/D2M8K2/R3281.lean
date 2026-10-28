import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13124 = true := by
  decide +kernel

theorem tot13124 : totK PD2M8K2 D2M8K2.t13124 = [0, 0, 157222309803, 454564045875, 272086845438, 25088168023, 0, 0] := by
  decide +kernel

theorem rows13125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13125 = true := by
  decide +kernel

theorem tot13125 : totK PD2M8K2 D2M8K2.t13125 = [0, 0, 172182539701, 472749715661, 232092677846, 6618102278, 0, 0] := by
  decide +kernel

theorem rows13126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13126 = true := by
  decide +kernel

theorem tot13126 : totK PD2M8K2 D2M8K2.t13126 = [0, 180306072155, 454814603176, 248267972938, 33391195522, 4185297743, 0, 0] := by
  decide +kernel

theorem rows13127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13127 = true := by
  decide +kernel

theorem tot13127 : totK PD2M8K2 D2M8K2.t13127 = [0, 192226400749, 483503670588, 226073513104, 12523541424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
