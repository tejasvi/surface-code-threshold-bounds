import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10528 = true := by
  decide +kernel

theorem tot10528 : totK PD2M8K2 D2M8K2.t10528 = [0, 0, 206551324021, 501557627037, 187348486644, 5265834820, 0, 0] := by
  decide +kernel

theorem rows10529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10529 = true := by
  decide +kernel

theorem tot10529 : totK PD2M8K2 D2M8K2.t10529 = [0, 0, 199785119905, 490286592416, 203328799146, 6302743008, 0, 0] := by
  decide +kernel

theorem rows10530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10530 = true := by
  decide +kernel

theorem tot10530 : totK PD2M8K2 D2M8K2.t10530 = [0, 180853706431, 382164484162, 263840074477, 89846035677, 7840298456, 0, 0] := by
  decide +kernel

theorem rows10531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10531 = true := by
  decide +kernel

theorem tot10531 : totK PD2M8K2 D2M8K2.t10531 = [0, 176483454666, 461407691337, 252483317768, 16598727853, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
