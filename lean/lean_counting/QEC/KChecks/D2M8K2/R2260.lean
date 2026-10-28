import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9040 = true := by
  decide +kernel

theorem tot9040 : totK PD2M8K2 D2M8K2.t9040 = [0, 0, 172176040643, 459967277842, 225034646456, 13809284570, 0, 0] := by
  decide +kernel

theorem rows9041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9041 = true := by
  decide +kernel

theorem tot9041 : totK PD2M8K2 D2M8K2.t9041 = [0, 0, 214512267595, 491826761429, 153434037009, 2396478222, 0, 0] := by
  decide +kernel

theorem rows9042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9042 = true := by
  decide +kernel

theorem tot9042 : totK PD2M8K2 D2M8K2.t9042 = [0, 0, 191209420685, 468486710235, 200772056779, 12299451732, 0, 0] := by
  decide +kernel

theorem rows9043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9043 = true := by
  decide +kernel

theorem tot9043 : totK PD2M8K2 D2M8K2.t9043 = [0, 0, 233191053562, 494527246459, 162553002223, 2485734986, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
