import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11860 = true := by
  decide +kernel

theorem tot11860 : totK PD2M8K2 D2M8K2.t11860 = [0, 166122192533, 463522581465, 269840428237, 20088554293, 0, 0, 0] := by
  decide +kernel

theorem rows11861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11861 = true := by
  decide +kernel

theorem tot11861 : totK PD2M8K2 D2M8K2.t11861 = [0, 0, 245231528620, 498656290892, 140927595212, 2304167554, 0, 0] := by
  decide +kernel

theorem rows11862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11862 = true := by
  decide +kernel

theorem tot11862 : totK PD2M8K2 D2M8K2.t11862 = [0, 0, 164965529779, 467324517322, 232951861222, 12601226032, 0, 0] := by
  decide +kernel

theorem rows11863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11863 = true := by
  decide +kernel

theorem tot11863 : totK PD2M8K2 D2M8K2.t11863 = [191552386262, 467060425676, 195355555175, 14024092592, 19770394697, 7077058802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
