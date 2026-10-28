import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11896 = true := by
  decide +kernel

theorem tot11896 : totK PD2M8K2 D2M8K2.t11896 = [106385935448, 433319107971, 335437543680, 38316723583, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11897 = true := by
  decide +kernel

theorem tot11897 : totK PD2M8K2 D2M8K2.t11897 = [0, 180479575176, 447109293611, 257170703123, 25373788367, 0, 0, 0] := by
  decide +kernel

theorem rows11898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11898 = true := by
  decide +kernel

theorem tot11898 : totK PD2M8K2 D2M8K2.t11898 = [0, 178408363127, 505460346050, 210213033626, 5430665091, 0, 0, 0] := by
  decide +kernel

theorem rows11899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11899 = true := by
  decide +kernel

theorem tot11899 : totK PD2M8K2 D2M8K2.t11899 = [177873774604, 393631784918, 256848198252, 89800850013, 6804944647, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
