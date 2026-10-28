import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8288 = true := by
  decide +kernel

theorem tot8288 : totK PD2M8K2 D2M8K2.t8288 = [165440749450, 447374022352, 283904860889, 28703924838, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8289 = true := by
  decide +kernel

theorem tot8289 : totK PD2M8K2 D2M8K2.t8289 = [107218656720, 428093626481, 342110085595, 28955321069, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8290 = true := by
  decide +kernel

theorem tot8290 : totK PD2M8K2 D2M8K2.t8290 = [0, 212477930219, 487414639415, 187593906033, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows8291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8291 = true := by
  decide +kernel

theorem tot8291 : totK PD2M8K2 D2M8K2.t8291 = [84865244063, 318188720067, 374701579992, 103444880636, 3581949829, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
