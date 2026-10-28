import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13580 = true := by
  decide +kernel

theorem tot13580 : totK PD2M8K2 D2M8K2.t13580 = [114359324879, 436368615003, 325556074754, 27619170478, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13581 = true := by
  decide +kernel

theorem tot13581 : totK PD2M8K2 D2M8K2.t13581 = [0, 200819407087, 490102982729, 190334311913, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows13582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13582 = true := by
  decide +kernel

theorem tot13582 : totK PD2M8K2 D2M8K2.t13582 = [83996229490, 311032518522, 374037309504, 103273652309, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows13583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13583 = true := by
  decide +kernel

theorem tot13583 : totK PD2M8K2 D2M8K2.t13583 = [180592202178, 444535141762, 251995752203, 26287535838, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
